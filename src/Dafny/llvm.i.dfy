include "ops.dfy"
include "types.dfy"
include "memory.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"

module LLVM_def {

    import opened types
    import opened ops
    import opened memory
    import opened conversion_operations_i
    import opened bitwise_binary_operations_i
    import opened binary_operations_i
    import opened other_operations_i


    type addr = int
    type LocalVar = string
    type GlobalVar = string

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------

    datatype state = State(
        lvs:map<LocalVar, Data>,
        gvs:map<GlobalVar, Data>,
        m:MemState,
        ok:bool)


    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    
    datatype codes = CNil | lvm_CCons(hd:code, tl:codes)
    datatype obool = OCmp(cmp:condition, o1:operand, o2:operand)

    datatype code =
    | Ins(ins:ins)
    | Block(block:codes)
    | IfElse(ifCond:bool, ifTrue:code, ifFalse:code)

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | BR(flag:bool, labelTrue:code,labelFalse:code)
    | CALL(dst:operand,fnc:code)
    | GETELEMENTPTR(dst:operand,t:bitWidth,op1:operand,op2:operand) //needs work VV
    | ICMP(dst:operand,cond:condition,size:nat,src1:operand,src2:operand)
    | RET(val:operand)
    | ZEXT(dst:operand,size:nat,src:operand,dstSize:bitWidth)
    | SHL(dst:operand,src:operand,shiftAmt:operand)
    | LSHR(dst:operand,src:operand,shiftAmt:operand)
    | AND(dst:operand,src1:operand,src2:operand)
    | OR(dst:operand,src1:operand,src2:operand)
    | TRUN(dst:operand,size:nat,src:operand,dstSize:bitWidth)
    | SEXT(dst:operand,size:nat,src:operand,dstSize:bitWidth)
    | LOAD(dst:operand,mems:MemState,t:bitWidth,src:operand) //o:operand, bid:nat, ofs:nat,
    | PHI()
    | INTTOPTR()
    | PTRTOINT()
    | EXTRACTVALUE()
    


    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && MemInit(s.m)    
    }

    predicate{:opaque} ValidRegState(s:state,lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        reveal_ValidData();
        // forall l:LocalVar :: l in lvs && forall g:GlobalVar :: g in gvs
        forall l:LocalVar :: l in lvs ==> ValidData(s,lvs[l])
        && forall g:GlobalVar :: g in gvs ==> ValidData(s,gvs[g])
    }

    predicate{:opaque} ValidData(s:state, d:Data)
    {
        reveal_IntFits();
        match d
            case Void => true
            case Int(val,itype) => IntFits(val,itype)
            case Bytes(bytes) => |bytes| > 0 && forall b :: b in bytes ==> 0 <= b < 0x100
            case Ptr(block,bid,offset) => && IsValidPtr(s.m,bid,offset) 
                                          && block in s.m.mem 
                                          && BlockValid(s.m.mem[block])
    }



    predicate ValidState(s:state)
    
    {
        reveal_ValidRegState();

           ValidRegState(s,s.lvs,s.gvs) 
        && MemValid(s.m) 
        && s.ok
    }

    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case D(d) => true && ValidData(s,d)
            case LV(l) => l in s.lvs && ValidData(s,s.lvs[l])
            case GV(g) => g in s.gvs && ValidData(s,s.gvs[g])
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case SUB(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case BR(cond, labelTrue,labelFalse) => true
            case CALL(dst,fnc) => ValidOperand(s,dst)
            case GETELEMENTPTR(dst,t,op1,op2) => MemValid(s.m) && ValidOperand(s,dst) && ValidOperand(s,op1) && ValidOperand(s,op2)
                                                   && OperandContents(s,op1).Ptr? && OperandContents(s,op2).Int?
                                                   && !OperandContents(s,op2).itype.signed
                                                   && validBitWidth(t)
                                                   && IsValidPtr(s.m,OperandContents(s,op1).bid,OperandContents(s,op1).offset)
                                                   && OperandContents(s,op1).offset + (OperandContents(s,op2).val * t) < |s.m.mem[OperandContents(s,op1).bid]|
            case ICMP(dst,cond,t,src1,src2) =>  && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                            && t == OperandContents(s,src1).itype.size
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case RET(val) => ValidOperand(s,val)
            case ZEXT(dst,t,src,dstSize) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && t == OperandContents(s,src).itype.size
                                            && t < dstSize
                                            && isInt(OperandContents(s,dst)) && !OperandContents(s,dst).itype.signed
                                           
            case SHL(dst,src,shiftAmt) =>   && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,shiftAmt)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src)) && isInt(OperandContents(s,shiftAmt))
                                            && OperandContents(s,src).itype.size*8 > OperandContents(s,shiftAmt).val
                                            && OperandContents(s,shiftAmt).val > 0
                                            && isInt(OperandContents(s,dst)) 
                                            && OperandContents(s,dst).itype.signed == OperandContents(s,src).itype.signed
            
            case LSHR(dst,src,shiftAmt) =>  && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,shiftAmt)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src)) && isInt(OperandContents(s,shiftAmt))
                                            && OperandContents(s,src).itype.size*8 > OperandContents(s,shiftAmt).val
                                            && OperandContents(s,shiftAmt).val > 0
                                            && isInt(OperandContents(s,dst)) && !OperandContents(s,dst).itype.signed
            
            case AND(dst,src1,src2) =>      && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                            && OperandContents(s,dst).itype.size == OperandContents(s,src1).itype.size
                                            && !OperandContents(s,dst).itype.signed
            case OR(dst,src1,src2) =>      && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                            && OperandContents(s,dst).itype.size == OperandContents(s,src1).itype.size
                                            && !OperandContents(s,dst).itype.signed
            case TRUN(dst,t,src,dstSize) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && t == OperandContents(s,src).itype.size
                                            && t > dstSize
                                            && isInt(OperandContents(s,dst))
            case SEXT(dst,t,src,dstSize) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && t == OperandContents(s,src).itype.size
                                            && t < dstSize
                                            && isInt(OperandContents(s,dst)) && OperandContents(s,dst).itype.signed
            case LOAD(dst,mems,size,src) => && ValidOperand(s,dst) && ValidOperand(s,src) 
                                            && MemValid(mems) && OperandContents(s,src).Ptr? 
                                            && IsValidPtr(mems,OperandContents(s,src).bid,OperandContents(s,src).offset)
                                            // && exists d:Data :: Load(mems,OperandContents(s,src).bid,OperandContents(s,src).offset,d)
            case PHI() => true
            case INTTOPTR() => true
            case PTRTOINT() => true
            case EXTRACTVALUE() => true     
    }

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
        requires ValidData(r,data)
        ensures evalUpdate(s, o, data, r) ==> ValidState(r)
        ensures evalUpdate(s, o, data, r) ==> ValidData(r,data)
        ensures evalUpdate(s, o, data, r) ==> ValidRegOperand(r,o)
        ensures evalUpdate(s, o, data, r) ==> ValidOperand(r,o)

    {
        reveal_ValidRegState();
        reveal_ValidData();
        match o
            case D(d) => data == d && r == s 
            case GV(g) => r == s.(gvs := s.gvs[g := data]) 
            case LV(l) => r == s.(lvs := s.lvs[l := data]) 
            
    }

    predicate evalLoad(s:state, o:operand, bid:nat, ofs:nat, r:state)
        requires ValidState(s)
        requires ValidOperand(s,o)
        requires exists d:Data :: Load(s.m,r.m,bid,ofs,d)
        ensures  evalLoad(s, o, bid, ofs, r) ==> ValidState(r)

        
    {
        reveal_ValidData();
        reveal_ValidRegState();
        var d :| Load(s.m,r.m,bid,ofs,d);
        match o
            case D(data) => data == d && r == s 
            case GV(g) => r == s.(gvs := s.gvs[g := d]) 
            case LV(l) => r == s.(lvs := s.lvs[l := d])
    }

    predicate evalIns(ins:ins, s:state, r:state,o:operand)
    {   
        if !s.ok || !ValidInstruction(s, ins) then !r.ok
        else match ins
            case ADD(dst,t,src1,src2) => o == dst 
                                && ValidData(r,evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case SUB(dst,t,src1,src2) => o == dst 
                                && ValidData(r,evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case CALL(dst,fnc) => o == dst 
                                && evalCode(fnc,s,r,o) 
                                && ValidData(r,OperandContents(s,o))
                                && evalUpdate(s,dst,OperandContents(s,o),r)
            case GETELEMENTPTR(dst,t,op1,op2) => o == dst 
                                && ValidData(r,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))
                                && evalUpdate(s, dst, evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)),r)
            case ICMP(dst,cond,t,src1,src2) => o == dst 
                                && ValidData(r,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case RET(val) => o == val && ValidState(r)
            case BR(cond, labelTrue,labelFalse) => evalIfElse(cond,labelTrue,labelFalse,s,r,o)&& ValidState(r)
            case SHL(dst,src,shiftAmt) =>o == dst
                                && ValidData(r,evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)),r)
            case LSHR(dst,src,shiftAmt) => o == dst 
                                && ValidData(r,evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)),r)
            case AND(dst,src1,src2) => o == dst 
                                && ValidData(r,evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),r)
            case OR(dst,src1,src2) => o == dst 
                                && ValidData(r,evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),r)
            case TRUN(dst,t,src,dstSize) => o == dst
                                && ValidData(r,evalTRUNC(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalTRUNC(OperandContents(s,src),dstSize),r)
            case SEXT(dst,t,src,dstSize) => o == dst
                                && ValidData(r,evalSEXT(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalSEXT(OperandContents(s,src),dstSize),r)
            case ZEXT(dst,t,src,dstSize) => o == dst 
                                && ValidData(r,evalZEXT(OperandContents(s,src),dstSize))
                                && evalUpdate(s, dst, evalZEXT(OperandContents(s,src),dstSize),r)
            case LOAD(dst,mems,size,src) => o == dst 
                                && exists d:Data :: Load(s.m,r.m,OperandContents(s,src).bid,OperandContents(s,src).offset,d) 
                                && evalLoad(s,o,OperandContents(s,src).bid,OperandContents(s,src).offset,r) //bid:nat, ofs:nat
            case PHI() => ValidState(r)
            case INTTOPTR() => ValidState(r)
            case PTRTOINT() => ValidState(r)
            case EXTRACTVALUE() => ValidState(r)   
    }

    predicate evalBlock(block:codes, s:state, r:state, o:operand)
    {
        if block.CNil? then
            r == s
        else
            exists r' :: evalCode(block.hd, s, r',o) && evalBlock(block.tl, r', r,o)
    }

    predicate branchRelation(s:state, s':state, cond:bool)
    {
        s' == s
    }
    function evalOBool(s:state, o:obool):bool
        requires ValidState(s)
        requires ValidOperand(s,o.o1)
        requires ValidOperand(s,o.o2)
        requires OperandContents(s, o.o1).Int? && OperandContents(s, o.o2).Int?
        requires typesMatch(OperandContents(s, o.o1),OperandContents(s, o.o2)) 
    {
        dataToBool(evalICMP(o.cmp, OperandContents(s, o.o1).itype.size, OperandContents(s, o.o1), OperandContents(s, o.o2)))
    }

    predicate evalIfElse(cond:bool, ifT:code, ifF:code, s:state, r:state,o:operand)
        decreases if ValidState(s) && cond then ifT else ifF
    {
        if ValidState(s) && s.ok then
            exists s' :: branchRelation(s, s', cond) && (if cond then evalCode(ifT, s', r,o) else evalCode(ifF, s', r,o))
        else
            !r.ok
    }

    predicate evalCode(c:code, s:state, r:state, o:operand)
        decreases c, 0
    {
        match c
            case Ins(ins) => evalIns(ins, s, r, o)
            case Block(block) => evalBlock(block, s, r,o)
            case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r,o)
    }

}
