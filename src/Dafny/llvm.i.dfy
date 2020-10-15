include "ops.dfy"
include "types.dfy"
include "simpleMemory.i.dfy"

module LLVM_def {

    import opened ops
    import opened simple_memory

    type addr = int
    type LocalVar = string
    type GlobalVar = string

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


    datatype operand = Val(v:Value) | LV(l:LocalVar) | GV(g:GlobalVar)

    //---
    //-----------------------------------------------------------------------------
    // Instructions
    //-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, src1ADD:operand, src2ADD:operand)
    | BR(cond:bool, labelTrue:string,labelFalse:string)
    | CALL() //needs work
    | GETELEMENTPTR(t:Value,p:ptr) //needs work VV
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

    predicate{:opaque} ValidRegState(lvs:map<LocalVar, Value>,gvs:map<GlobalVar, Value>)
    {
        forall l:LocalVar :: l in lvs && forall g:GlobalVar :: g in gvs
    }

    predicate ValidState(s:state)
    
    {
        ValidRegState(s.lvs,s.gvs) && ValidMemState(s.m)
    }

    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case Val(v) => true
            case LV(l) => l in s.lvs
            case GV(g) => g in s.gvs
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(t,src1,src2) => ValidOperand(s,t) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                    && matchOps(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2))
            case SUB(t,src1,src2) => ValidOperand(s,t) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                    && matchOps(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2))
            case BR(cond, labelTrue,labelFalse) => true
            case CALL() => true
            case GETELEMENTPTR(t,p) => true
            case ICMP() => true
            case RET() => true
            case SEXT() => true
            case SHL() => true
            case TRUN() => true
            case ZEXT() => true
                 
    }

    predicate matchOps(v0:Value,v1:Value,v2:Value)
    {
        (v0.Val8? ==> v1.Val8? && v2.Val8?)
        && (v0.Val16? ==> v1.Val16? && v2.Val16?)
        && (v0.Val32? ==> v1.Val32? && v2.Val32?)
        && (v0.Val64? ==> v1.Val64? && v2.Val64?)
        && (v0.Val128? ==> v1.Val128? && v2.Val128?)
    }
    //EVAL//
    predicate ValidRegOperand(s:state, o:operand)
    { 
        ValidOperand(s,o)
    }

    function OperandContents(s:state, o:operand): Value
        requires ValidOperand(s,o)
        requires ValidState(s)
    {
        // let x:Value | 0;

        reveal_ValidRegState();
        match o
            case Val(v) => v
            case LV(l) => s.lvs[l]
            case GV(g) => s.gvs[g]
           
    }


    predicate evalUpdate(s:state, o:operand, val:Value, r:state)
        requires ValidState(s)
        requires ValidRegOperand(s,o)
        ensures evalUpdate(s, o, val, r) ==> ValidState(r)
    {
        reveal_ValidRegState();
        match o
            case Val(v) => r == s 
            case GV(g) => r == s.(gvs := s.gvs[g := val]) 
            case LV(l) => r == s.(lvs := s.lvs[l := val]) 
            
    }

    predicate evalIns(ins:ins, s:state, r:state)
    {   
        if !s.ok || !ValidInstruction(s, ins) then !r.ok
        else match ins
            case ADD(t,src1,src2) => evalUpdate(s, t, 
                                evalADD(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2)),r)
            case SUB(t,src1,src2) => evalUpdate(s, t, 
                                evalSUB(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2)),r)
            case BR(cond, labelTrue,labelFalse) => true
            case CALL() => true
            case GETELEMENTPTR(t,p) => true
            case ICMP() => true
            case RET() => true
            case SEXT() => true
            case SHL() => true
            case TRUN() => true
            case ZEXT() => true
    }




    function evalADD(v0:Value,v1:Value,v2:Value): Value
        requires matchOps(v0,v1,v2)
    {
       if v0.Val8? then Val8(BitwiseAdd8(ValueContents8Bit(v1),ValueContents8Bit(v2))) else 
       if v0.Val16? then Val16(BitwiseAdd16(ValueContents16Bit(v1),ValueContents16Bit(v2))) else
       if v0.Val32? then Val32(BitwiseAdd32(ValueContents32Bit(v1),ValueContents32Bit(v2))) else
       if v0.Val64? then Val64(BitwiseAdd64(ValueContents64Bit(v1),ValueContents64Bit(v2))) else
                        Val128(BitwiseAdd128(ValueContents128Bit(v1),ValueContents128Bit(v2)))
    }

    function evalSUB(v0:Value,v1:Value,v2:Value): Value
        requires matchOps(v0,v1,v2)
    {
       if v0.Val8? then Val8(BitwiseSub8(ValueContents8Bit(v1),ValueContents8Bit(v2))) else 
       if v0.Val16? then Val16(BitwiseSub16(ValueContents16Bit(v1),ValueContents16Bit(v2))) else
       if v0.Val32? then Val32(BitwiseSub32(ValueContents32Bit(v1),ValueContents32Bit(v2))) else
       if v0.Val64? then Val64(BitwiseSub64(ValueContents64Bit(v1),ValueContents64Bit(v2))) else
                        Val128(BitwiseSub128(ValueContents128Bit(v1),ValueContents128Bit(v2)))
    }


}