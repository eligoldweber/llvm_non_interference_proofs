include "./ops.dfy"
include "./types.dfy"
include "./memory.i.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"
include "../Libraries/SeqIsUniqueDef.i.dfy"
include "./llvmIntrinsic.i.dfy"

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
    
    datatype codes = CNil | lvm_Codes(hd:code, tl:codes) | ForeignFunction
    datatype obool = OCmp(cmp:condition, o1:operand, o2:operand)

    datatype code =
    | Ins(ins:ins)
    | Block(block:codes)
    | IfElse(ifCond:bool, ifTrue:codes, ifFalse:codes)
    // | IfElseOp(ifCondOp:operand, ifTrue:codes, ifFalse:codes)
    //| While(whileCond:bool, whileBlock:codes)

//-----------------------------------------------------------------------------
// Instructions
//-----------------------------------------------------------------------------

    datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | BR(if_cond:operand, labelTrue:codes,labelFalse:codes)
    | UNCONDBR(goToLabel:codes)
    | CALL(dst:operand,fnc:codes)
    | GETELEMENTPTR(dst:operand,t:bitWidth,op1:operand,op2:operand)
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
    | STORE(valueToStore:operand,ptr:operand,mems:MemState)
    | ALLOCA(dst:operand,t:bitWidth)
    | INTTOPTR(dst:operand,intSrc:operand,ptrType:operand)
    | PTRTOINT(dst:operand,ptrSrc:operand,intType:operand)
    | BITCAST(dst:operand,src:operand,castType:operand)
    | PHI()
    | EXTRACTVALUE()
    | LLVM_MEMCPY(dst:operand,src:operand,len:bitWidth,volatile:bool)


    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && MemInit(s.m)    
    }
    
    predicate ValidData(s:state, d:Data)
    {    
        match d
            case Void => true
            case Int(val,itype) => IntFits(val,itype)
            case Bytes(bytes) => |bytes| > 0 && forall b :: b in bytes ==> 0 <= b < 0x100
            case Ptr(block,bid,offset,size) => && IsValidPtr(s.m,bid,offset,size) 
    }


    predicate ValidRegState(s:state,lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        forall l:LocalVar :: l in lvs ==> ValidData(s,lvs[l])
        && forall g:GlobalVar :: g in gvs ==> ValidData(s,gvs[g])
    }

    predicate ValidState(s:state)
    
    {
        && ValidRegState(s,s.lvs,s.gvs) 
        && MemValid(s.m) 
        && s.ok
    }

    datatype Step = 
        | evalInsStep(ins:ins)
        | stutterStep()

    predicate stutter(s:state,s':state)
    {
        s == s'
    }

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case evalInsStep(ins) => evalIns(ins,s,s')
            case stutterStep() => stutter(s,s')
    }

    // predicate StateNext(s:state,s':state)
    // {
    //     && ValidState(s)
    //     // && ValidState(s')
    //     && MemStateNext(s.m,s'.m)
    //     &&  (|| (exists ins :: (evalIns(ins, s, s')))
    //          || (s == s'))
    // }

        predicate StateNext(s:state,s':state)
    {
        && exists step :: NextStep(s,s',step)
        && ValidState(s)
        && MemStateNext(s.m,s'.m)
        
    }


    lemma ValidStateSeqImpliesCode(s:state, s':state,code:code){
        assert forall stateSeqS:seq<state> ::
            (&& evalCode(code, s, s') 
            && startAndEndState(s,s',stateSeqS)
            && ValidStateSeq(stateSeqS))  ==> StateSeqEvalsCode(code,stateSeqS);
    }

    predicate ValidStateSeq(states:seq<state>)
    {
        (|states| <= 1 && |states| == 1 ==> ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    predicate StateSeqEvalsCode(c:code,states:seq<state>)
    {
        |states| >= 2 && evalCode(c,states[0],states[|states|-1])
    }

    predicate startAndEndState(s:state,s':state,states:seq<state>)
    {
        |states| >= 2 && states[0] == s && states[|states|-1] == s'
    }

    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case D(d) => ValidData(s,d)
            case LV(l) => l in s.lvs && ValidData(s,s.lvs[l])
            case GV(g) => g in s.gvs && ValidData(s,s.gvs[g])
    }
    
    predicate ValidLocalVars(s:state)
    {
        forall lv :: lv in s.lvs ==> ValidData(s,s.lvs[lv])
    }

    predicate addLocalVar(s:state,s':state,lv:LocalVar,d:Data)
    {
        ValidState(s) && ValidData(s,d) && s' == s.(lvs := s'.lvs[lv:=d])
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case SUB(dst,t,src1,src2) => && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case BR(if_cond, labelTrue,labelFalse) => && ValidOperand(s,if_cond)
                                                   && OperandContents(s,if_cond).Int? && !OperandContents(s,if_cond).itype.signed
                                                   && OperandContents(s,if_cond).itype.size == 1 
             case UNCONDBR(goToLabel) => true
            case CALL(dst,fnc) => && ValidOperand(s,dst) && !fnc.CNil?
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
            case RET(val) => && ValidOperand(s,val)
            case ZEXT(dst,t,src,dstSize) => && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && OperandContents(s,src).itype.size < dstSize
            case SHL(dst,src,shiftAmt) =>   && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,shiftAmt)
                                            && isInt(OperandContents(s,src)) && isInt(OperandContents(s,shiftAmt))
                                            && OperandContents(s,src).itype.size*8 > OperandContents(s,shiftAmt).val
                                            && OperandContents(s,shiftAmt).val > 0            
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
                                            && IsValidPtr(mems,OperandContents(s,src).bid,OperandContents(s,src).offset,size)
            case STORE(valueToStore,ptr,mems) => && ValidOperand(s,valueToStore) && ValidOperand(s,ptr)
                                                 && OperandContents(s,valueToStore).Int? && (IntType(1, false) == OperandContents(s,valueToStore).itype)
                                                 && MemValid(mems) && OperandContents(s,ptr).Ptr? 
                                                 && IsValidPtr(mems,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,1)
            case ALLOCA(dst,t) => && ValidOperand(s,dst) && MemValid(s.m) && OperandContents(s,dst).Ptr? && validBitWidth(t)
            case INTTOPTR(dst,intSrc,ptrType) => && ValidOperand(s,dst) && ValidOperand(s,intSrc) && ValidOperand(s,ptrType)
                                                                         && isInt(OperandContents(s,intSrc)) 
                                                                         && OperandContents(s,ptrType).Ptr? && OperandContents(s,dst).Ptr?
            case PTRTOINT(dst,ptrSrc,intType) => && ValidOperand(s,dst) && ValidOperand(s,ptrSrc) && ValidOperand(s,intType)
                                                                         && isInt(OperandContents(s,intType)) 
                                                                         && OperandContents(s,ptrSrc).Ptr? && OperandContents(s,dst).Int?
            case BITCAST(dst,src,castType) => && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,castType)
                                                                      && ValidOperand(s,dst) 
                                                                      && ( (OperandContents(s,src).Int? && OperandContents(s,castType).Int?) || (OperandContents(s,src).Ptr? && OperandContents(s,castType).Ptr?))
                                                                      && ( (OperandContents(s,dst).Int? && OperandContents(s,castType).Int?) || (OperandContents(s,dst).Ptr? && OperandContents(s,castType).Ptr?))
                                                                      && typesMatch(OperandContents(s,dst),OperandContents(s,castType))
            case EXTRACTVALUE() => true    //TODO 
            case PHI() => true //TODO
            case LLVM_MEMCPY(dst,src,len,volatile) => && ValidOperand(s,dst) && ValidOperand(s,src) && OperandContents(s,dst).Ptr?
                                                     && OperandContents(s,src).Ptr? && OperandContents(s,dst).size >= OperandContents(s,src).size
                                                     && validBitWidth(len) && !volatile // dont support volatile right now
           
    }

    //EVAL LLVM//
    predicate ValidRegOperand(s:state, o:operand)
    { 
        ValidOperand(s,o)
    }

    function OperandContents(s:state, o:operand): Data
        requires ValidOperand(s,o)
        requires ValidState(s)
    {

        
        match o
            case D(d) => d
            case LV(l) => s.lvs[l]
            case GV(g) => s.gvs[g]
           
    }

    predicate evalUpdate(s:state, o:operand, data:Data, s':state)
        requires ValidState(s)
        requires ValidRegOperand(s,o)
        requires ValidData(s',data)
        ensures evalUpdate(s, o, data, s') ==> ValidState(s')
        ensures evalUpdate(s, o, data, s') ==> ValidData(s',data)
        ensures evalUpdate(s, o, data, s') ==> ValidRegOperand(s',o)
        ensures evalUpdate(s, o, data, s') ==> ValidOperand(s',o)
        ensures evalUpdate(s, o, data, s') ==> 
        (forall d :: ValidOperand(s,d) && d != o ==> ValidOperand(s',d) && OperandContents(s,d) == OperandContents(s',d));

    {
        
        
        match o
            case D(d) => data == d && s' == s 
            case GV(g) => s' == s.(gvs := s.gvs[g := data]) 
            case LV(l) => s' == s.(lvs := s.lvs[l := data]) 
            
    }

    predicate evalLoad(s:state, o:operand, bid:nat, ofs:nat, s':state)
        requires ValidState(s)
        requires ValidOperand(s,o)
        requires exists d:Data :: Load(s.m,s'.m,bid,ofs,d)
        ensures  evalLoad(s, o, bid, ofs, s') ==> ValidState(s')

        
    {
        
        
        var d :| Load(s.m,s'.m,bid,ofs,d);
        match o
            case D(data) => data == d && s' == s 
            case GV(g) => s' == s.(gvs := s.gvs[g := d]) 
            case LV(l) => s' == s.(lvs := s.lvs[l := d])
    }

    predicate evalRet(s:state, o:operand, data:Data, s':state)
        requires ValidState(s)
        requires ValidRegOperand(s,o)
        requires ValidData(s',data)
    {
        
        if data.Void? then 
            && s == s' 
            // && OperandContents(s, o) == OperandContents(r, o)
        else evalUpdate(s,o,data,s')
    }

    predicate evalIns(ins:ins, s:state, s':state)
    {   
        if !s.ok || !ValidInstruction(s, ins) then !s'.ok
        else match ins
            case ADD(dst,t,src1,src2) => ValidState(s') //o == dst 
                                && ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case SUB(dst,t,src1,src2) => ValidState(s') //o == dst 
                                && ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case CALL(dst,fnc) => ValidState(s') //o == dst 
                                && evalBlock(fnc,s,s') 
                                && ValidData(s',OperandContents(s,dst))
                                && evalUpdate(s,dst,OperandContents(s,dst),s')
            case GETELEMENTPTR(dst,t,op1,op2) => ValidState(s') //o == dst 
                                && ValidData(s',evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))
                                && evalUpdate(s, dst, evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)),s')
            case ICMP(dst,cond,t,src1,src2) => ValidState(s') //o == dst 
                                && ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),s')
                                && OperandContents(s,src1).itype == OperandContents(s',src1).itype
            case RET(val) => ValidState(s') && s'.m == s.m && (if OperandContents(s,val).Void? then assert ValidState(s'); &&  s' == s
                                            else 
                                             && evalUpdate(s, val, OperandContents(s,val),s'))// && r == s
            case BR(if_cond, labelTrue,labelFalse) => ValidState(s') && evalIfElse(dataToBool(OperandContents(s,if_cond)),labelTrue,labelFalse,s,s')&& ValidState(s')
            case SHL(dst,src,shiftAmt) => ValidState(s') //o == dst
                                && ValidData(s',evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalSHL(OperandContents(s,src),OperandContents(s,shiftAmt)),s')
            case LSHR(dst,src,shiftAmt) => ValidState(s') // o == dst 
                                && ValidData(s',evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)),s')
            case AND(dst,src1,src2) => ValidState(s')  //o == dst 
                                && ValidData(s',evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),s')
            case OR(dst,src1,src2) =>  ValidState(s') //o == dst 
                                && ValidData(s',evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalOR(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),s')
            case TRUN(dst,t,src,dstSize) => ValidState(s') //o == dst
                                && ValidData(s',evalTRUNC(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalTRUNC(OperandContents(s,src),dstSize),s')
            case SEXT(dst,t,src,dstSize) => ValidState(s') //o == dst
                                && ValidData(s',evalSEXT(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalSEXT(OperandContents(s,src),dstSize),s')
            case ZEXT(dst,t,src,dstSize) => ValidState(s') // o == dst 
                                && ValidData(s',evalZEXT(OperandContents(s,src),dstSize))
                                && evalUpdate(s, dst, evalZEXT(OperandContents(s,src),dstSize),s')
            case LOAD(dst,mems,size,src) => ValidState(s') && s.m == s'.m 
                                && if evalLOAD(s.m,s'.m,size,OperandContents(s,src)).Void? then !s'.ok else// o == dst 
                                 evalUpdate(s, dst, evalLOAD(s.m,s'.m,size,OperandContents(s,src)),s') && evalLOAD(s.m,s'.m,size,OperandContents(s,src)).Int?
                                // && evalLoad(s,o,OperandContents(s,src).bid,OperandContents(s,src).offset,r) //bid:nat, ofs:nat
            case STORE(valueToStore,ptr,mems) => ValidState(s') && mems == s.m && Store(s.m,s'.m,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore))
                                                 && (MemValid(s'.m))
            case ALLOCA(dst,t) =>  ValidState(s') && exists b :: (Alloc(s.m,s'.m,b,t)
                                        && evalUpdate(s, dst, Ptr(b, b, 0, t),s'))
            case INTTOPTR(dst,intSrc,ptrType) => ValidState(s')
            case PTRTOINT(dst,ptrSrc,intType) => ValidState(s')
            case BITCAST(dst,src,castType) => ValidState(s')
                                            && ValidData(s',evalBITCAST(OperandContents(s,src),OperandContents(s,castType)))    
                                            && evalUpdate(s, dst, evalBITCAST(OperandContents(s,src),OperandContents(s,castType)),s')
            case EXTRACTVALUE() => ValidState(s')
            case PHI() => ValidState(s')
            case UNCONDBR(goToLabel) => evalBlock(goToLabel,s,s') && ValidState(s')
            case LLVM_MEMCPY(dst,src,len,volatile) => ValidState(s')
    }

    predicate evalBlock(block:codes, s:state, s':state)
    {
        if block.CNil? || block.ForeignFunction? then
            s' == s
        else
            exists r :: (evalCode(block.hd, s, r) && evalBlock(block.tl, r, s'))
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

    predicate evalIfElse(cond:bool, ifT:codes, ifF:codes, s:state, s':state)
        decreases if ValidState(s) && cond then ifT else ifF
    {
        if ValidState(s) && s.ok then
            exists r :: branchRelation(s, r, cond) && (if cond then evalBlock(ifT, r, s') else evalBlock(ifF, r, s'))
        else
            !s'.ok
    }


    predicate evalCode(c:code, s:state, s':state)
        decreases c, 0
    {
        match c
            case Ins(ins) => evalIns(ins, s, s')
            case Block(block) => evalBlock(block, s, s')
            case IfElse(ifCond, ifT, ifF) => evalIfElse(ifCond, ifT, ifF, s, s')
    }

//// utility functions and helper lemmas 

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
        ensures out.d.size == s.size;
    {
        var x:operand := D(Ptr(s.block, s.bid, s.offset,s.size));
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


// ---LLVM INTRINSICs ----
    predicate llvm_lifetime_end(s:state,s':state,size:bitWidth,ptr:Data)
        requires ptr.Ptr?
    {   
        Free(s.m,s'.m,ptr.bid)
    }

    //   method evalLLVM_MEMCPY(s:state,s':state,dst:operand,src:operand,len:bitWidth,volatile:bool) returns (out:Data)
    //     requires ValidOperand(s,dst)
    //     requires ValidOperand(s,src)
    //     requires ValidState(s)
    //     requires OperandContents(s,dst).Ptr?;
    //     requires OperandContents(s,src).Ptr?;
    //     requires OperandContents(s,dst).size >= OperandContents(s,src).size
    //     requires OperandContents(s,src).block in s.m.mem;
    //     requires OperandContents(s,dst).block in s.m.mem;
    //     // ensures OperandContents(s,dst) == out

    // {   
        
    //     assert OperandContents(s,src).block in s.m.mem;
    //     var bSrc:Block := s.m.mem[OperandContents(s,src).block];
    //     var bDst:Block := s.m.mem[OperandContents(s,dst).block];
    //     assert BlockValid(bSrc);
    //     assert |bSrc| > 0;
    //     var i := 0;
    //     var index := 0;
    //     while i < len 
    //     {
    //         var mc:MemCell := bSrc[index];
    //         i := i + 1;
    //     }

    //     out := Ptr(0,0,0,1);
    // }

}
