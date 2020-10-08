include "ops.dfy"
include "types.dfy"
include "simpleMemory.i.dfy"

module LLVM_def {

    import opened ops
    import opened simple_memory

    type addr = int
    type LocalVar = string
    type GlobalVar = string

    datatype Value = uint8 | uint16 | uint32 | uint64 | uint128


    datatype state = State(
        lvs:map<LocalVar, Value>,
        gvs:map<GlobalVar, Value>,
        m:memmap,
        ok:bool)


    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && ValidMemState(s.m)    
    }

    predicate ValidRegState(lvs:map<LocalVar, Value>,gvs:map<GlobalVar, Value>)
    {
        forall l:LocalVar :: l in lvs && forall g:GlobalVar :: g in gvs
    }

    predicate ValidState(s:state)
    
    {
        ValidRegState(s.lvs,s.gvs) && ValidMemState(s.m)
    }


}