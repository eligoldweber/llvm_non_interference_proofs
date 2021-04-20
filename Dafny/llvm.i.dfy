include "ops.dfy"
include "types.dfy"
include "memory.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"
include "./Libraries/SeqIsUniqueDef.i.dfy"

module LLVM_def {

    import opened types
    import opened ops
    import opened memory
    import opened Common__SeqIsUniqueDef_i
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
    | IfElse(ifCond:bool, ifTrue:codes, ifFalse:codes)

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | BR(if_cond:operand, labelTrue:codes,labelFalse:codes)
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
    
    predicate{:opaque} ValidData(s:state, d:Data)
    {
        reveal_IntFits();
        match d
            case Void => true
            case Int(val,itype) => IntFits(val,itype)
            case Bytes(bytes) => |bytes| > 0 && forall b :: b in bytes ==> 0 <= b < 0x100
            case Ptr(block,bid,offset) => true
            // case Ptr(block,bid,offset) => && IsValidPtr(s.m,bid,offset) 
            //                               && block in s.m.mem 
            //                               && BlockValid(s.m.mem[block])
    }


    predicate{:opaque} ValidRegState(s:state,lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        reveal_ValidData();
        // forall l:LocalVar :: l in lvs && forall g:GlobalVar :: g in gvs
        forall l:LocalVar :: l in lvs ==> ValidData(s,lvs[l])
        && forall g:GlobalVar :: g in gvs ==> ValidData(s,gvs[g])
    }





    predicate ValidState(s:state)
    
    {
        reveal_ValidRegState();

           ValidRegState(s,s.lvs,s.gvs) 
        && MemValid(s.m) 
        && s.ok
    }

    predicate StateNext(s:state,s':state)
    {
        && ValidState(s)
        && ValidState(s')
        &&  (|| (exists ins :: (ValidInstruction(s,ins) && evalIns(ins, s, s')))
             || (s == s'))
    }

    predicate ValidOperand(s:state,o:operand)
    {
        reveal_ValidData();
        match o
            case D(d) => ValidData(s,d)
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
            case BR(if_cond, labelTrue,labelFalse) => && ValidOperand(s,if_cond)
                                                   && OperandContents(s,if_cond).Int? && !OperandContents(s,if_cond).itype.signed
                                                   && OperandContents(s,if_cond).itype.size == 1 
            case CALL(dst,fnc) => ValidOperand(s,dst)
            case GETELEMENTPTR(dst,t,op1,op2) => MemValid(s.m) && ValidOperand(s,dst) && ValidOperand(s,op1) && ValidOperand(s,op2)
                                                   && OperandContents(s,op1).Ptr? && OperandContents(s,op2).Int?
                                                   && !OperandContents(s,op2).itype.signed
                                                   && validBitWidth(t)
                                                   && IsValidBid(s.m,OperandContents(s,op1).bid)
            case ICMP(dst,cond,t,src1,src2) =>  && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                            && t == OperandContents(s,src1).itype.size
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case RET(val) => && ValidOperand(s,val)//&& ValidOperand(s,dst) 
            case ZEXT(dst,t,src,dstSize) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && OperandContents(s,src).itype.size < dstSize
                                            && isInt(OperandContents(s,dst)) 
            case SHL(dst,src,shiftAmt) =>   && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,shiftAmt)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src)) && isInt(OperandContents(s,shiftAmt))
                                            && OperandContents(s,src).itype.size*8 > OperandContents(s,shiftAmt).val
                                            && OperandContents(s,shiftAmt).val > 0
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
                                            && OperandContents(s,src).itype.size < dstSize
                                            && isInt(OperandContents(s,dst)) 
            case LOAD(dst,mems,size,src) => && ValidOperand(s,dst) && ValidOperand(s,src) 
                                            && MemValid(mems) && OperandContents(s,src).Ptr? 
                                            && IsValidPtr(mems,OperandContents(s,src).bid,OperandContents(s,src).offset)

            case PHI() => true //TODO
            case INTTOPTR() => true //TODO
            case PTRTOINT() => true //TODO
            case EXTRACTVALUE() => true    //TODO 
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
        ensures evalUpdate(s, o, data, r) ==> 
        (forall d :: ValidOperand(s,d) && d != o ==> ValidOperand(r,d) && OperandContents(s,d) == OperandContents(r,d));

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

    predicate evalRet(s:state, o:operand, data:Data, r:state)
        requires ValidState(s)
        requires ValidRegOperand(s,o)
        requires ValidData(r,data)
        // ensures !data.Void? ==> evalUpdate(s,o,data,r)
    {
        reveal_ValidData();
        if data.Void? then 
            && s == r 
            // && OperandContents(s, o) == OperandContents(r, o)
        else evalUpdate(s,o,data,r)
    }

    // lemma equalStatesEqualOperands(s:state, s':state, o:operand)
    //     requires ValidState(s)
    predicate evalIns(ins:ins, s:state, r:state)
    {   
        if !s.ok || !ValidInstruction(s, ins) then !r.ok
        else match ins
            case ADD(dst,t,src1,src2) => //o == dst 
                                && ValidData(r,evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case SUB(dst,t,src1,src2) => //o == dst 
                                && ValidData(r,evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),r)
            case CALL(dst,fnc) => //o == dst 
                                && evalCode(fnc,s,r) 
                                && ValidData(r,OperandContents(s,dst))
                                && evalUpdate(s,dst,OperandContents(s,dst),r)
            case GETELEMENTPTR(dst,t,op1,op2) => //o == dst 
                                && ValidData(r,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))
                                && evalUpdate(s, dst, evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)),r)
            case ICMP(dst,cond,t,src1,src2) => //o == dst 
                                && ValidData(r,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),r)
                                && OperandContents(s,src1).itype == OperandContents(r,src1).itype
            case RET(val) => ValidState(r) && 
                    if OperandContents(s,val).Void? then r == s
                    else //o == val  
                    && evalUpdate(s, val, OperandContents(s,val),r)// && r == s
            // case RET(dst, val) => && ValidData(r,OperandContents(s,val)) 
            //                       && if OperandContents(s,val).Void? then s == r else evalUpdate(s, dst, OperandContents(s,val),r)//evalRet(s,dst,OperandContents(s,val),r)// o == val && ValidState(r) //&& r == s
            case BR(if_cond, labelTrue,labelFalse) => evalIfElse(dataToBool(OperandContents(s,if_cond)),labelTrue,labelFalse,s,r)&& ValidState(r)
            case SHL(dst,src,shiftAmt) =>//o == dst
                                && ValidData(r,evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)),r)
            case LSHR(dst,src,shiftAmt) =>// o == dst 
                                && ValidData(r,evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)),r)
            case AND(dst,src1,src2) => //o == dst 
                                && ValidData(r,evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),r)
            case OR(dst,src1,src2) => //o == dst 
                                && ValidData(r,evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),r)
            case TRUN(dst,t,src,dstSize) => //o == dst
                                && ValidData(r,evalTRUNC(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalTRUNC(OperandContents(s,src),dstSize),r)
            case SEXT(dst,t,src,dstSize) => //o == dst
                                && ValidData(r,evalSEXT(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalSEXT(OperandContents(s,src),dstSize),r)
            case ZEXT(dst,t,src,dstSize) =>// o == dst 
                                && ValidData(r,evalZEXT(OperandContents(s,src),dstSize))
                                && evalUpdate(s, dst, evalZEXT(OperandContents(s,src),dstSize),r)
            case LOAD(dst,mems,size,src) =>// o == dst 
                                && s.m == r.m
                                && evalUpdate(s, dst, evalLOAD(s.m,r.m,size,OperandContents(s,src)),r)
                                // && evalLoad(s,o,OperandContents(s,src).bid,OperandContents(s,src).offset,r) //bid:nat, ofs:nat
            case PHI() => ValidState(r)
            case INTTOPTR() => ValidState(r)
            case PTRTOINT() => ValidState(r)
            case EXTRACTVALUE() => ValidState(r)   
    }

    predicate evalBlock(block:codes, s:state, r:state)
    {
        if block.CNil? then
            r == s
        else
            exists r' :: (evalCode(block.hd, s, r') && evalBlock(block.tl, r', r)
            && (block.hd.Block? ==> s == r'))
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

    predicate evalIfElse(cond:bool, ifT:codes, ifF:codes, s:state, r:state)
        decreases if ValidState(s) && cond then ifT else ifF
    {
        if ValidState(s) && s.ok then
            exists s' :: branchRelation(s, s', cond) && (if cond then evalBlock(ifT, s', r) else evalBlock(ifF, s', r))
        else
            !r.ok
    }

    predicate evalCode(c:code, s:state, r:state)
        decreases c, 0
    {
        match c
            case Ins(ins) => evalIns(ins, s, r)
            case Block(block) => evalBlock(block, s, r)
            case IfElse(cond, ifT, ifF) => evalIfElse(cond, ifT, ifF, s, r)
    }

//// utility functions

    function copyIntOperand(s:Data) : (out:operand)
        requires s.Int?
        ensures out.D? && out.d.Int?
        ensures out.d.val == s.val 
        ensures out.d.itype.size == s.itype.size
        ensures out.d.itype.signed == s.itype.signed;
    {
        var x:operand := D(Int(s.val,IntType(s.itype.size,s.itype.signed)));
        x
    }

    function copyPtrOperand(s:Data) : (out:operand)
        requires s.Ptr?
        ensures out.D? && out.d.Ptr?
        ensures out.d.block == s.block 
        ensures out.d.bid == s.bid
        ensures out.d.offset == s.offset;
    {
        var x:operand := D(Ptr(s.block, s.bid, s.offset));
        x
    }

    predicate operandsUnique(s:state,ops:seq<operand>)
        requires ValidState(s)
        requires forall o :: o in ops ==> ValidOperand(s,o)
    {
        reveal_SeqIsUnique();
        reveal_SeqIsUniqueAtomic();
        SeqIsUnique(ops) && SeqIsUniqueAtomic(ops)
    }

    // lemma twoOperandsUnique(s:state,ops:seq<operand>, o1:operand,o2:operand)
    //     requires ValidState(s)
    //     requires forall o :: o in ops ==> ValidOperand(s,o)
    //     requires operandsUnique(s,ops)
    //     requires o1 in ops
    //     requires o2 in ops
    //     ensures exists i,j :: 
    //             0 <= i < |ops| 
    //             &&  0 <= j < |ops| 
    //             && ops[i] == o1 
    //             && ops[j] == o2
    //             && i != j 
    //             && o1 != o2
    //     {
    //         reveal_SeqIsUnique();
    //         reveal_SeqIsUniqueAtomic();
    //         assert SeqIsUnique(ops) && SeqIsUniqueAtomic(ops);
    //         var i :| 0 <= i < |ops| && ops[i] == o1;
    //         var j :| 0 <= j < |ops| && ops[j] == o2;
            
    //         assert i != j ==> o1 != o2;
    //     }


}
