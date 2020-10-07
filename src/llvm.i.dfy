include "ops.dfy"
include "types.dfy"

module LLVM_def {

    import opened ops

    type addr = int
    type LocalVar = string
    type GlobalVar = string

    datatype Value = uint8 | uint16 | uint32 | uint64 | uint128

    //Memory
    datatype mb = Mb(sz:int, b:byte)
    datatype mptr = Mptr(blk:string,ofs:int,idx:int)
    datatype munit = addr
    datatype memoryCell = mb | mptr | munit

    type memmap = map<addr, memoryCell>

    datatype state = State(
        lvs:map<LocalVar, Value>,
        gvs:map<GlobalVar, Value>,
        m:memmap,
        ok:bool)

    function{:axiom} TheValidAddresses(): set<addr>
    predicate{:opaque} ValidMemState(s:memmap)
    {
        // regular mem
        (forall m:addr :: m in TheValidAddresses() <==> m in s)    
    }

    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && ValidMemState(s.m)    
    }

    // predicate Valid_State(s:State)
    // {

    // }
}