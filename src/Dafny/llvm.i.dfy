include "ops.dfy"
include "types.dfy"
include "memory.dfy"
// include "typeConversions.i.dfy"

module LLVM_def {

    import opened types
    import opened ops
    import opened memory
    // import opened type_conversion

    type addr = int
    type LocalVar = string
    type GlobalVar = string

    datatype state = State(
        lvs:map<LocalVar, Data>,
        gvs:map<GlobalVar, Data>,
        m:MemState,
        ok:bool)


    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    datatype condition = eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

    //---
    //-----------------------------------------------------------------------------
    // Instructions
    //-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, t:IntType, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, t:IntType, src1SUB:operand, src2SUB:operand)
    | BR(flag:bool, labelTrue:string,labelFalse:string)
    | CALL() //needs work
    | GETELEMENTPTR() //needs work VV
    | ICMP(cond:condition,dst:operand,src1:operand,src2:operand)
    | RET()
    | ZEXT(dst:operand,tSrc:IntType,src:operand,tDst:IntType)
    | SHL()
    | TRUN()
    | SEXT(dst:operand,tSrc:IntType,src:operand,tDst:IntType)
    


    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && MemInit(s.m)    
    }

    predicate{:opaque} ValidRegState(lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        forall l:LocalVar :: l in lvs && forall g:GlobalVar :: g in gvs
    }

    predicate ValidState(s:state)
    
    {
        ValidRegState(s.lvs,s.gvs) && MemValid(s.m)
    }

    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case D(d) => true
            case LV(l) => l in s.lvs
            case GV(g) => g in s.gvs
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && intTypesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case SUB(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && intTypesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case BR(cond, labelTrue,labelFalse) => true
            case CALL() => true
            case GETELEMENTPTR() => true
            case ICMP(cond,dst,src1,src2) => ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
            case RET() => true
            case ZEXT(dst,tSrc,src,tDst) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && tSrc == OperandContents(s,src).itype 
                                            && !tSrc.signed && !tDst.signed && tSrc.size <= tDst.size
            case SHL() => true
            case TRUN() => true
            case SEXT(dst,tSrc,src,tDst) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                        && tSrc == OperandContents(s,src).itype 
                                        && tSrc.signed && tDst.signed && tSrc.size <= tDst.size
                 
    }

    // predicate matchOps(v0:Value,v1:Value,v2:Value)
    // {
    //     (v0.Val8? ==> v1.Val8? && v2.Val8?)
    //     && (v0.Val16? ==> v1.Val16? && v2.Val16?)
    //     && (v0.Val32? ==> v1.Val32? && v2.Val32?)
    //     && (v0.Val64? ==> v1.Val64? && v2.Val64?)
    //     && (v0.ValBool? ==> !v1.ValBool? && !v2.ValBool?)
    // }

    //  predicate numericalValue(v:Value)
    // {
    //     v.Val8? || v.Val16? || v.Val32? || v.Val64?
    // }

    //EVAL//
    predicate ValidRegOperand(s:state, o:operand)
    { 
        ValidOperand(s,o)
    }

    function OperandContents(s:state, o:operand): Data
        requires ValidOperand(s,o)
        requires ValidState(s)
    {

        reveal_ValidRegState();
        match o
            case D(d) => d
            case LV(l) => s.lvs[l]
            case GV(g) => s.gvs[g]
           
    }


    predicate evalUpdate(s:state, o:operand, data:Data, r:state)
        requires ValidState(s)
        requires ValidRegOperand(s,o)
        ensures evalUpdate(s, o, data, r) ==> ValidState(r)
    {
        reveal_ValidRegState();
        match o
            case D(d) => r == s 
            case GV(g) => r == s.(gvs := s.gvs[g := data]) 
            case LV(l) => r == s.(lvs := s.lvs[l := data]) 
            
    }

    predicate evalIns(ins:ins, s:state, r:state)
    {   
        if !s.ok || !ValidInstruction(s, ins) then !r.ok
        else match ins
            case ADD(dst,t,src1,src2) => evalUpdate(s, dst, 
                                evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case SUB(dst,t,src1,src2) => evalUpdate(s, dst, 
                                evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case CALL() => true
            case GETELEMENTPTR() => true
            // case ICMP(cond,dst,src1,src2) => evalUpdate(s, dst, 
            //                     ValBool(evalICMP(cond,OperandContents(s,dst),OperandContents(s,src1),OperandContents(s,src2))),r)
            case RET() => true
            case BR(cond, labelTrue,labelFalse) => true

            // case ZEXT(dst,t0,src,t1) => evalUpdate(s, dst, 
            //                       evalZEXT(t0,OperandContents(s,src),t1),r)
            case SHL() => true
            case TRUN() => true
            // case SEXT(dst,t0,src,t1) => true
            case SEXT(dst,tSrc,src,tDst) => true
            case ZEXT(dst,tSrc,src,tDst) => true
            case ICMP(cond,dst,src1,src2) => true
    }




    function evalADD(t:IntType_,v0:Data,v1:Data): Data
        requires isInt(v0)
        requires isInt(v1)
        requires intTypesMatch(v0,v1)
    { 

        if v0.itype == IntType(1, false) then UInt8(BitwiseAdd8(DataToUInt8(v0),DataToUInt8(v1))) else 
        if v0.itype == IntType(2, false) then UInt16(BitwiseAdd16(DataToUInt16(v0),DataToUInt16(v1))) else 
        if v0.itype == IntType(4, false) then UInt32(BitwiseAdd32(DataToUInt32(v0),DataToUInt32(v1))) else 
        if v0.itype == IntType(8, false) then UInt64(BitwiseAdd64(DataToUInt64(v0),DataToUInt64(v1))) else
        if v0.itype == IntType(1, true) then SInt8(BitwiseSAdd8(DataToSInt8(v0),DataToSInt8(v1))) else 
        if v0.itype == IntType(2, true) then SInt16(BitwiseSAdd16(DataToSInt16(v0),DataToSInt16(v1))) else 
        if v0.itype == IntType(4, true) then SInt32(BitwiseSAdd32(DataToSInt32(v0),DataToSInt32(v1))) else 
        if v0.itype == IntType(8, true) then SInt64(BitwiseSAdd64(DataToSInt64(v0),DataToSInt64(v1))) else v0
       
    }




    function evalSUB(t:IntType_,v0:Data,v1:Data): Data
        requires isInt(v0)
        requires isInt(v1)
        requires intTypesMatch(v0,v1)
    {
        if v0.itype == IntType(1, false) then UInt8(BitwiseSub8(DataToUInt8(v0),DataToUInt8(v1))) else 
        if v0.itype == IntType(2, false) then UInt16(BitwiseSub16(DataToUInt16(v0),DataToUInt16(v1))) else 
        if v0.itype == IntType(4, false) then UInt32(BitwiseSub32(DataToUInt32(v0),DataToUInt32(v1))) else 
        if v0.itype == IntType(8, false) then UInt64(BitwiseSub64(DataToUInt64(v0),DataToUInt64(v1))) else
        if v0.itype == IntType(1, true) then SInt8(BitwiseSSub8(DataToSInt8(v0),DataToSInt8(v1))) else 
        if v0.itype == IntType(2, true) then SInt16(BitwiseSSub16(DataToSInt16(v0),DataToSInt16(v1))) else 
        if v0.itype == IntType(4, true) then SInt32(BitwiseSSub32(DataToSInt32(v0),DataToSInt32(v1))) else 
        if v0.itype == IntType(8, true) then SInt64(BitwiseSSub64(DataToSInt64(v0),DataToSInt64(v1))) else v0
    }

    // function evalSUB(v0:Value,v1:Value,v2:Value): Value
    //     requires numericalVisIntalue(v0);
    //     requires isInt(v1);
    //     requires isInt(v2);
    //     requires matchOps(v0,v1,v2)
        
    // {
    //    if v0.Val8? then Val8(BitwiseSub8(ValueContents8Bit(v1),ValueContents8Bit(v2))) else 
    //    if v0.Val16? then Val16(BitwiseSub16(ValueContents16Bit(v1),ValueContents16Bit(v2))) else
    //    if v0.Val32? then Val32(BitwiseSub32(ValueContents32Bit(v1),ValueContents32Bit(v2))) else
    //    if v0.Val64? then Val64(BitwiseSub64(ValueContents64Bit(v1),ValueContents64Bit(v2))) else
    //                     Val8(0)
    // }

// eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

    // function evalICMP(c:condition,t:Value,v0:Value,v1:Value): bool
    //     // requires matchOps(t,v0,v1)
    // {
    //     match c
    //         case eq => v0 == v1
    //         case ne => v0 != v1
    //         case ugt => v0 > v1
    //         case uge => v0 > v1 || v0 == v1
    //         case ult => v0 < v1
    //         case ule => v0 < v1 || v0 == v1
    //         case sgt => true // signed 
    //         case sge => true // signed 
    //         case slt => true // signed 
    //         case sle => true // signed 
    // }


    

}
