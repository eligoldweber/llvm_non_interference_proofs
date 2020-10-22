include "ops.dfy"
include "types.dfy"
include "simpleMemory.i.dfy"
include "typeConversions.i.dfy"

module LLVM_def {

    import opened types
    import opened ops
    import opened simple_memory
    import opened type_conversion

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
    datatype condition = eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

    //---
    //-----------------------------------------------------------------------------
    // Instructions
    //-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, src1ADD:operand, src2ADD:operand)
    | BR(flag:bool, labelTrue:string,labelFalse:string)
    | CALL() //needs work
    | GETELEMENTPTR(t:operand,p:ptr) //needs work VV
    | ICMP(cond:condition,t:operand,src1:operand,src2:operand)
    | RET()
    | ZEXT(dst:operand,t0:Value,src:operand,t1:Value)
    | SHL()
    | TRUN()
    | SEXT(dst:operand,t0:Value,src:operand,t1:Value)
    


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
                                    && numericalValue(OperandContents(s,t)) &&  numericalValue(OperandContents(s,src1)) && numericalValue(OperandContents(s,src2))
                                    && matchOps(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2))
            case SUB(t,src1,src2) => ValidOperand(s,t) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                    && numericalValue(OperandContents(s,t)) &&  numericalValue(OperandContents(s,src1)) && numericalValue(OperandContents(s,src2))
                                    && matchOps(OperandContents(s,t),OperandContents(s,src1),OperandContents(s,src2))
            case BR(cond, labelTrue,labelFalse) => true
            case CALL() => true
            case GETELEMENTPTR(t,p) => true
            case ICMP(cond,dst,src1,src2) => ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
            case RET() => true
            case ZEXT(dst,t0,src,t1) => ValidOperand(s,dst) && ValidOperand(s,src) && typesMatch(t0,OperandContents(s,src)) 
                                        && unsignedVal(t0) && unsignedVal(t1) && unsignedValLT(t0,t1) 
            case SHL() => true
            case TRUN() => true
            case SEXT(dst,t0,src,t1) => ValidOperand(s,dst) && ValidOperand(s,src) && typesMatch(t0,OperandContents(s,src)) 
                                        && signedVal(t0) && signedVal(t1) && signedValLT(t0,t1) 
                 
    }

    predicate matchOps(v0:Value,v1:Value,v2:Value)
    {
        (v0.Val8? ==> v1.Val8? && v2.Val8?)
        && (v0.Val16? ==> v1.Val16? && v2.Val16?)
        && (v0.Val32? ==> v1.Val32? && v2.Val32?)
        && (v0.Val64? ==> v1.Val64? && v2.Val64?)
        && (v0.ValBool? ==> !v1.ValBool? && !v2.ValBool?)
    }

     predicate numericalValue(v:Value)
    {
        v.Val8? || v.Val16? || v.Val32? || v.Val64?
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
            case ICMP(cond,dst,src1,src2) => evalUpdate(s, dst, 
                                ValBool(evalICMP(cond,OperandContents(s,dst),OperandContents(s,src1),OperandContents(s,src2))),r)
            case RET() => true
            case ZEXT(dst,t0,src,t1) => evalUpdate(s, dst, 
                                  evalZEXT(t0,OperandContents(s,src),t1),r)
            case SHL() => true
            case TRUN() => true
            case SEXT(dst,t0,src,t1) => true
    }




    function evalADD(v0:Value,v1:Value,v2:Value): Value
        requires numericalValue(v0);
        requires numericalValue(v1);
        requires numericalValue(v2);
        requires matchOps(v0,v1,v2)
    {
       if v0.Val8? then Val8(BitwiseAdd8(ValueContents8Bit(v1),ValueContents8Bit(v2))) else 
       if v0.Val16? then Val16(BitwiseAdd16(ValueContents16Bit(v1),ValueContents16Bit(v2))) else
       if v0.Val32? then Val32(BitwiseAdd32(ValueContents32Bit(v1),ValueContents32Bit(v2))) else
       if v0.Val64? then Val64(BitwiseAdd64(ValueContents64Bit(v1),ValueContents64Bit(v2))) else
                        Val8(0)
    }

    function evalSUB(v0:Value,v1:Value,v2:Value): Value
        requires numericalValue(v0);
        requires numericalValue(v1);
        requires numericalValue(v2);
        requires matchOps(v0,v1,v2)
        
    {
       if v0.Val8? then Val8(BitwiseSub8(ValueContents8Bit(v1),ValueContents8Bit(v2))) else 
       if v0.Val16? then Val16(BitwiseSub16(ValueContents16Bit(v1),ValueContents16Bit(v2))) else
       if v0.Val32? then Val32(BitwiseSub32(ValueContents32Bit(v1),ValueContents32Bit(v2))) else
       if v0.Val64? then Val64(BitwiseSub64(ValueContents64Bit(v1),ValueContents64Bit(v2))) else
                        Val8(0)
    }

// eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

    function evalICMP(c:condition,t:Value,v0:Value,v1:Value): bool
        // requires matchOps(t,v0,v1)
    {
        match c
            case eq => v0 == v1
            case ne => v0 != v1
            case ugt => v0 > v1
            case uge => v0 > v1 || v0 == v1
            case ult => v0 < v1
            case ule => v0 < v1 || v0 == v1
            case sgt => true // signed 
            case sge => true // signed 
            case slt => true // signed 
            case sle => true // signed 
    }


    

}
