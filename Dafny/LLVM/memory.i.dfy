include "types.dfy"
include "../Libraries/Math/mod_auto.i.dfy"
module memory {

import opened types
import opened Math__mod_auto_i


// Each cell of memory is occupied by either data, a pointer, or uninitialized
// data
datatype MemCell =  mb(size:nat, data:uint8) | 
                    mptr(block:nat, offset:nat, index:nat) |
                    muninit()

// Memory is composed of a bunch of blocks, each block being a list of memory
// cells that all start uninitialized
type Block = seq<MemCell>
type MemMap = map<nat, Block>
datatype MemState = MemState(mem:MemMap, nextBlock:nat)

// A newly-initialized block should start out uninitialized, meaning all its
// members are muninit
predicate IsUninit(b:Block) {
    forall offset | 0 <= offset < |b| :: b[offset].muninit?
}

function UninitBlock(size:nat) : (b:Block)
    ensures IsUninit(b)
    ensures |b| == size
    decreases size
{
    if size == 0 then []
    else UninitBlock(size - 1) + [muninit()]
}

predicate byteRangeIsValid(i:int,s:int)
{
    0 <= i < s
}

// Pointers and block indices can be valid/invalid depending on whether the
// location exists in memory
predicate IsValidBid(s:MemState, bid:nat) {
    bid in s.mem
}
predicate IsValidPtr(s:MemState, bid:nat, offset:nat, size:bitWidth) {
    && bid in s.mem
    && offset < |s.mem[bid]|
    && validBitWidth(size)
}

// On initialization, the memory state is empty and contains no blocks
predicate MemInit(s:MemState) {
    && |s.mem| == 0
    && s.nextBlock == 0
}

// A byte-memory cell is valid within a block if the surrounding memory cells starting
// at the appropriate alignment are of the same size
predicate ByteMemValid(b:Block, offset:nat)
    requires offset < |b|
    requires b[offset].mb?
    requires b[offset].size > 0
    requires offset > 0
{
    var cell := b[offset];
    lemma_mod_auto(offset);
    var align := offset - (offset % cell.size);
    forall i :: (align <= i < (align + cell.size) && i < |b| && i>=0) ==> (i < |b| && b[i].mb? && b[i].size == cell.size)
}

// A block is valid so long as its stored bytes are well-formed; that is, numbers
// of size n start on an index divisible by n and fill the entire n space
predicate BlockValid(b:Block) {
    forall offset :: (0 < offset < |b| && b[offset].mb?) ==> (b[offset].size > 0 && ByteMemValid(b, offset))
}

// Need to check every step to make sure memory is still valid
// predicate MemValid(s:MemState) {
//     && (forall bid | bid in s.mem :: bid < s.nextBlock)
//     && (forall bid | bid in s.mem :: BlockValid(s.mem[bid]))
// }
predicate MemValid(s:MemState) {
    && (forall bid :: bid in s.mem ==> bid < s.nextBlock)
    && (forall bid :: bid in s.mem ==> BlockValid(s.mem[bid]))
}

datatype MemStep = 
    | allocStep(bid:nat, size:nat)
    | freeStep(bid:nat)
    | storeStep(bid:nat, offset:nat, data:Data, n:bitWidth)
    | memCpyStep(bid:nat,bid':nat)
    | stutterStep()

predicate NextMemStep(s:MemState, s':MemState, step:MemStep)
{
    match step  
        case allocStep(bid,size) => Alloc(s,s',bid,size)
        case freeStep(bid) => Free(s,s',bid)
        case storeStep(bid,offset,data,n) => (&& IsValidPtr(s, bid, offset,n)
                                            && data.Int? && IntType(1, false) == data.itype
                                            && MemValid(s)
                                            && (Store(s,s',bid,offset,data)))
        case memCpyStep(bid,bid') => bid' in s'.mem && bid in s.mem && s'.mem[bid'] == s.mem[bid]
        case stutterStep() => s == s'
}

// Describes valid Mem state transition 
predicate MemStateNext(s:MemState,s':MemState,step:MemStep)
{
    MemValid(s)
    && MemValid(s')
    && NextMemStep(s,s',step)
}
// When a new block is allocated, all the previous blocks should remain the same,
// and an unininitialized block of the appropriate size should be added with block
// nextBlock
predicate Alloc(s:MemState, s':MemState, bid:nat, size:nat) {
    && bid == s.nextBlock
    && s'.nextBlock == s.nextBlock + 1
    && s'.mem == s.mem[s.nextBlock := UninitBlock(size)]
}

// Blocks can be freed as well, in which case it is simply removed from the map
predicate Free(s:MemState, s':MemState, bid:nat) {
    && s'.nextBlock == s.nextBlock 
    && IsValidBid(s, bid)
    && !IsValidBid(s', bid)
    && s.mem == s'.mem[bid:= s.mem[bid]]
}

// 
predicate Load(s:MemState, s':MemState, bid:nat, offset:nat, data:Data) {
    if !IsValidPtr(s, bid, offset,1) || data.Ptr?  || data.Void? then false
    else
        var bytes := (if data.Bytes? then data.bytes else IntToBytes(data));
        && (s' == s)
        && (data.Int? ==> offset % |bytes| == 0)
        && (offset + |bytes| <= |s.mem[bid]|)
        && (forall i {:trigger byteRangeIsValid(i,|bytes|)} | 0 <= i < |bytes| :: (offset + i < |s.mem[bid]|))
        && (forall i {:trigger byteRangeIsValid(i,|bytes|)} | 0 <= i < |bytes| :: s.mem[bid][offset + i].mb?)
        && validBitWidth(|bytes|)
}


// 
predicate Store(s:MemState, s':MemState, bid:nat, offset:nat, data:Data)
    requires IsValidPtr(s, bid, offset,1)
    requires data.Int? && IntType(1, false) == data.itype;
    requires MemValid(s);
{
    && s'.nextBlock == s.nextBlock
    && s'.mem == s.mem[bid := s.mem[bid][offset := mb(data.itype.size, DataToUInt8(data))]]
    // && MemValid(s')
    // && NextMemStep(s,s',MemStep.storeStep(bid,offset,data,1))
}

function evalStore(s:MemState, bid:nat, offset:nat, data:Data) : (s':MemState)
    requires IsValidPtr(s, bid, offset,1)
    requires data.Int? && IntType(1, false) == data.itype;
    requires MemValid(s);
    requires s.mem[bid][offset].mb? && s.mem[bid][offset].size == data.itype.size;
    ensures MemValid(s')// ==> Store(s,s',bid,offset,data);
{
    var s' := s.(mem := s.mem[bid := s.mem[bid][offset := mb(data.itype.size, DataToUInt8(data))]]);
    assert MemValid(s');
    s'
}


// lemma StoreImpliesStoreStep(s:MemState, s':MemState, bid:nat, offset:nat, data:Data)
//     requires IsValidPtr(s, bid, offset,1)
//     requires data.Int? && IntType(1, false) == data.itype;
//     requires Store(s,s',bid,offset,data);
//     ensures NextMemStep(s, s', MemStep.storeStep(bid,offset,data,1));
// {
//     assert IsValidPtr(s, bid, offset,1);
//     assert data.Int? && IntType(1, false) == data.itype;
//     assert (Store(s,s',bid,offset,data));
//     assert NextMemStep(s, s', MemStep.storeStep(bid,offset,data,1));
// }
// // Memory Access and Addressing Operations // 
function evalLOAD(s:MemState,s':MemState,t:bitWidth,op1:Data): (out:Data)
    requires MemValid(s)
    requires op1.Ptr?
    // requires IsValidPtr(s,op1.bid,op1.offset)
    ensures out.Bytes? ==> validBitWidth(|out.bytes|)
    ensures out.Int? || out.Void?;
    ensures !out.Ptr?;
    ensures out.Int? ==> out.itype.size == t;
{
    if exists d:Data :: d.Int? && d.itype.size == t && Load(s,s',op1.bid,op1.offset,d) then
        var d:Data :| d.Int? && d.itype.size == t && Load(s,s',op1.bid,op1.offset,d);
        assert d.Int?;
        assert d.Int? ==> d.itype.size == t;
        d
    else Void
}


function evalGETELEMENTPTR(s:MemState,t:bitWidth,op1:Data,op2:Data): (out:Data)
    requires MemValid(s)
    requires op1.Ptr? //TODO: Also could be vector of Ptrs
    requires validBitWidth(t)
    requires IsValidBid(s,op1.bid)
    requires op2.Int? && !op2.itype.signed
    ensures out.Ptr?
    ensures op1.offset + (op2.val * t) < |s.mem[op1.bid]| ==> IsValidPtr(s,out.bid,out.offset,t)
{
    
    assert op1.offset >= 0;
    assert op2.val >= 0;
    assert (op2.val * t) >= 0;
    var newOffset:nat := op1.offset + (op2.val * t);
    Ptr(op1.block,op1.bid,newOffset,t)
}

function evalALLOCA(s:MemState, size:nat): (out:Data)
    requires MemValid(s)
    // requires Alloc(s,s',s.nextBlock,size);
    requires validBitWidth(size);
    ensures out.Ptr?;
{
    // && bid == s.nextBlock
    // && s'.nextBlock == s.nextBlock + 1
    // && s'.mem == s.mem[s.nextBlock := UninitBlock(size)]
    var bid := s.nextBlock;
    // assert Alloc(s,s',bid,size);
    var d := (Ptr(bid,bid,0,size));
    d
}

function AllocaStep(s:MemState, size:nat): (out:MemState)
    requires MemValid(s);
    ensures forall b :: b in s.mem ==> b in out.mem;
    ensures forall bid:nat, offset:nat, size:bitWidth :: IsValidPtr(s,bid,offset,size) ==> IsValidPtr(out,bid,offset,size);
    ensures Alloc(s,out,s.nextBlock,size);
    ensures BlockValid(out.mem[s.nextBlock]);
    ensures MemValid(out);
{
    // s'.nextBlock := s.nextBlock + 1;
     var x := s.mem[s.nextBlock := UninitBlock(size)];
     var y:MemState := MemState(x,s.nextBlock + 1);
     assert forall b :: b in s.mem ==> b in y.mem;
     assert forall bid:nat, offset:nat, size:bitWidth :: IsValidPtr(s,bid,offset,size) ==> IsValidPtr(y,bid,offset,size);
     assert Alloc(s,y,s.nextBlock,size);
     assert BlockValid(y.mem[s.nextBlock]);
     assert MemValid(y);
     y
}

    predicate memCpy(s:MemState, dstPtr:Data, oPtr:Data, s':MemState)
        requires MemValid(s)
        requires dstPtr.Ptr?;
        requires oPtr.Ptr?;  
        requires IsValidPtr(s,dstPtr.bid,dstPtr.offset,dstPtr.size) 
        requires IsValidPtr(s,oPtr.bid,oPtr.offset,oPtr.size) 

        
    {
        var bSrc:Block := s.mem[oPtr.bid];
        && s' == s.(mem := (s.mem[dstPtr.bid := bSrc] ))
        && s'.mem[dstPtr.bid] == s'.mem[oPtr.bid]
        && forall b :: b in s.mem <==> b in s'.mem
        && NextMemStep(s,s',MemStep.memCpyStep(oPtr.bid,dstPtr.bid))
    }

 function evalMemCpy(s:MemState, dstPtr:Data, oPtr:Data) : (s':MemState)
        requires MemValid(s)
        requires dstPtr.Ptr?;
        requires oPtr.Ptr?;  
        requires IsValidPtr(s,dstPtr.bid,dstPtr.offset,dstPtr.size) 
        requires IsValidPtr(s,oPtr.bid,oPtr.offset,oPtr.size) 
    {
        var bSrc:Block := s.mem[oPtr.bid];
        var s' := s.(mem := (s.mem[dstPtr.bid := bSrc]));
        assert memCpy(s,dstPtr,oPtr,s');
        s'
    }
    




}