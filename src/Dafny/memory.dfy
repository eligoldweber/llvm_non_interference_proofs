include "types.dfy"
include "./Libraries/Math/mod_auto.i.dfy"
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
predicate {:opaque} IsUninit(b:Block) {
    forall offset | 0 <= offset < |b| :: b[offset].muninit?
}

function UninitBlock(size:nat) : (b:Block)
    ensures IsUninit(b)
    ensures |b| == size
    decreases size
{
    reveal_IsUninit();
    if size == 0 then []
    else UninitBlock(size - 1) + [muninit()]
}

// Pointers and block indices can be valid/invalid depending on whether the
// location exists in memory
predicate IsValidBid(s:MemState, bid:nat) {
    bid in s.mem
}
predicate IsValidPtr(s:MemState, bid:nat, offset:nat) {
    && bid in s.mem
    && offset < |s.mem[bid]|
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
    var align := offset - offset % cell.size;
    forall i | align <= i < (align + cell.size) :: (i < |b| && b[i].mb? && b[i].size == cell.size)
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
    &&! IsValidBid(s', bid)
    && s.mem == s'.mem[bid:= s.mem[bid]]
}

// TODO: Support reading and writing more than one byte at a time
predicate Load(s:MemState, s':MemState, bid:nat, offset:nat, data:Data) {
    if !IsValidPtr(s, bid, offset) || data.Ptr? then false
    else
        var bytes := (if data.Bytes? then data.bytes else IntToBytes(data));
        && (s' == s)
        && (data.Int? ==> offset % |bytes| == 0)
        && (offset + |bytes| <= |s.mem[bid]|)
        && (forall i | 0 <= i < |bytes| :: (offset + i < |s.mem[bid]|))
        && (forall i | 0 <= i < |bytes| :: s.mem[bid][offset + i].mb?)
}

// TODO: Support reading and writing more than one byte at a time
predicate Store(s:MemState, s':MemState, bid:nat, offset:nat, data:Data)
    requires IsValidPtr(s, bid, offset)
{
    true
    // && s'.nextBlock == s.nextBlock
    // && s'.mem == s.mem[p.bid := s.mem[p.bid][p.offset := mb(1, val)]]
}


}
