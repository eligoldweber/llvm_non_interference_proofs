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


    // Taken from Vale -- modify for llvm
    type shift_amount = s | 0 <= s < 32 // Some shifts allow s=32, but we'll be conservative for simplicity
    datatype Shift =
        | LSLShift(amount_lsl:shift_amount)
        | LSRShift(amount_lsr:shift_amount)
        | RORShift(amount_ror:shift_amount)

    // datatype operand = OConst(n:uint32)
        // | OReg(r:addr)
        // | OShift(reg:addr, s:Shift)
        // | OSymbol(sym:GlobalVar)
        // | OSP
        // | OLR
    datatype operand = Value | LocalVar | GlobalVar

    //---
    //-----------------------------------------------------------------------------
    // Instructions
    //-----------------------------------------------------------------------------

    datatype ins =
    | ADD(t:Value, src1ADD:operand, src2ADD:operand)
    | SUB(t:Value, src1ADD:operand, src2ADD:operand)
    | BR(cond:bool, labelTrue:string,labelFalse:string)
    | CALL() //needs work
    | GETELEMENTPTR(t:Value,p:ptr,) //needs work
    | ICMP()
    | RET()
    | SEXT()
    | SHL()
    | TRUN()
    | ZEXT()
    


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

    predicate ValidInstruction(s:state, ins:ins)
    {
        true
    }

}