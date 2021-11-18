include "Types.s.dfy"


module Memory_s {
    import opened Types_s

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
        // lemma_mod_auto(offset);
        var align := offset - (offset % cell.size);
        forall i :: (align <= i < (align + cell.size) && i < |b| && i>=0) ==> (i < |b| && b[i].mb? && b[i].size == cell.size)
    }
// A block is valid so long as its stored bytes are well-formed; that is, numbers
// of size n start on an index divisible by n and fill the entire n space
predicate BlockValid(b:Block) {
    forall offset | 0 < offset < |b| :: (b[offset].mb? ==> (b[offset].size > 0 && ByteMemValid(b, offset)))
}

// Need to check every step to make sure memory is still valid
predicate MemValid(s:MemState) {
    && (forall bid | bid in s.mem :: bid < s.nextBlock)
    && (forall bid | bid in s.mem :: BlockValid(s.mem[bid]))
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
    {
        && s'.nextBlock == s.nextBlock
        && s'.mem == s.mem[bid := s.mem[bid][offset := mb(data.itype.size, DataToUInt8(data))]]
        // && NextMemStep(s,s',MemStep.storeStep(bid,offset,data,1))
    }

}
