include "ops.dfy"
include "types.dfy"

module LLVM_def {

    import opened ops

    type addr = int
    type LocalVar = string
    type GlobalVar = string

    datatype Value = uint8 | uint16 | uint32 | uint64 | uint128


    datatype state = State(
        lvs:map<LocalVar, Value>,
        gvs:map<GlobalVar, Value>,
        ok:bool)


    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0    
    }

    // predicate Valid_State(s:State)
    // {

    // }
}