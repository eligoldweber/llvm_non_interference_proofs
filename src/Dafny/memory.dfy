include "types.dfy"

module memory {

import opened types

// TEMPORARY
datatype ptr = ptr(bid:nat, offset:nat)

// Each cell of memory is occupied by either data, a pointer, or uninitialized
// data
datatype MemCell =  mb(size:nat, data:byte) | 
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
predicate IsValidBlock(s:MemState, bid:nat) {
    bid in s.mem
}

predicate IsValidPtr(s:MemState, p:ptr) {
    && p.bid in s.mem
    && p.offset < |s.mem[p.bid]|
}

// On initialization, the memory state is empty and contains no blocks
predicate MemInit(s:MemState) {
    && |s.mem| == 0
    && s.nextBlock == 0
}

// Need to check every step to make sure memory is still valid
predicate MemValid(s:MemState) {
    forall bid | bid in s.mem :: bid < s.nextBlock
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
predicate Free(s:MemState, s':MemState, bid:nat)
    requires IsValidBlock(s, bid)
{
    && s'.nextBlock == s.nextBlock
    && bid !in s'.mem
    && s.mem == s'.mem[bid:= s.mem[bid]]
}

// TODO: Support reading and writing more than one byte at a time
predicate Load(s:MemState, s':MemState, p:ptr, val:byte)
    requires IsValidPtr(s, p)
{
    var cell := s.mem[p.bid][p.offset];
    && s' == s
    && cell.mb?
    && cell.data == val
}

// TODO: Support reading and writing more than one byte at a time
predicate Store(s:MemState, s':MemState, p:ptr, val:byte)
    requires IsValidPtr(s, p)
{
    && s'.nextBlock == s.nextBlock
    && s'.mem == s.mem[p.bid := s.mem[p.bid][p.offset := mb(1, val)]]
}


}