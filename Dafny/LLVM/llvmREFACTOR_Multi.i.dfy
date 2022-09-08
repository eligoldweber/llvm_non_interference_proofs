include "./ops.dfy"
include "./types.dfy"
include "./memory.i.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"
include "../Libraries/SeqIsUniqueDef.i.dfy"
include "../Libraries/Seqs.s.dfy"
include "../Libraries/Sets.i.dfy"

module LLVM_defRE_Multi {

    import opened types
    import opened ops
    import opened memory
    import opened Common__SeqIsUniqueDef_i
    import opened conversion_operations_i
    import opened bitwise_binary_operations_i
    import opened binary_operations_i
    import opened other_operations_i
    import opened Collections__Seqs_s
    import opened Collections__Sets_i

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
        o:output,
        ok:bool)


///
    datatype version = Version(pre:bool,post:bool)

    datatype output = Out(o:Data) | SubOut(os:seq<output>) | Nil

    type codeSeq = seq<codeRe>

    datatype codeRe =
    | Ins(ins:ins)
    | Block(block:codeSeq)
    | IfElse(ifCond:operand, ifTrue:codeSeq, ifFalse:codeSeq)
    | Divergence(pre:codeSeq,post:codeSeq,patched:bool)
    | NonImpactIns(NIIns:ins)
    | CNil
            
    type behavior = seq<state>

    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    
  
 datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | SDIV(dst:operand, src1:operand, src2:operand)
    | ICMP(dst:operand,cond:condition,size:nat,src1:operand,src2:operand)
    | TRUNC(dst:operand,size:nat,src:operand,dstSize:bitWidth)
    | ZEXT(dst:operand,size:nat,src:operand,dstSize:bitWidth)
    | AND(dst:operand,src1:operand,src2:operand)
    | LSHR(dst:operand,src:operand,shiftAmt:operand)
    | STORE(valueToStore:operand,ptr:operand)
    | LLVM_MEMCPY(dst:operand,src:operand,len:bitWidth,volatile:bool)
    | CALL(dst:operand,fnc:codeSeq)
    | GETELEMENTPTR(dst:operand,t:bitWidth,op1:operand,op2:operand)
    | UNCONDBR(goToLabel:codeRe)
    | BR(if_cond:operand, labelTrue:codeRe,labelFalse:codeRe)
    | ALLOCA(dst:operand,t:bitWidth)
    | LOAD(dst:operand,t:bitWidth,src:operand)
    | BITCAST(dst:operand,src:operand,castType:operand)
    | RET(val:operand)
    | VISIBLE_OUT(o:output)


// STATE TRANSITIONS
    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && MemInit(s.m) 
        && s.o.Nil?   
    }

    predicate ValidData(s:state, d:Data)
    {    
        match d
            case Void => true
            case Int(val,itype) => IntFits(val,itype)
            case Bytes(bytes) => |bytes| > 0 && forall b :: b in bytes ==> 0 <= b < 0x100
            case Ptr(block,bid,offset,size) => && IsValidPtr(s.m,bid,offset,size) 
    }


    predicate ValidVarState(s:state,lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        && (forall l:LocalVar :: l in lvs ==> ValidData(s,lvs[l]))
        && (forall g:GlobalVar :: g in gvs ==> ValidData(s,gvs[g]))
    }


    predicate ValidState(s:state)
    {
        && ValidVarState(s,s.lvs,s.gvs) 
        && MemValid(s.m) 
        && s.ok
    }

    datatype Step = 
    | evalInsStep(ins:ins)
    | stutterStep()
    | errorStateStep()

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case evalInsStep(ins) => validEvalIns(ins,s,s') && s'.ok
            case stutterStep() => stutter(s,s')
            case errorStateStep() => errorStep(s,s')
    }

    predicate StateNext(s:state,s':state)
    {
        && exists step :: NextStep(s,s',step)
        && ValidState(s)
    
    }

    
    predicate stutter(s:state,s':state)
    {
        s == s'
    }
    
    predicate errorStep(s:state,s':state)
    {
        ValidState(s) && !s'.ok
    }


    predicate {:opaque} ValidBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1 && ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }


    function {:opaque} behaviorOutput(b:behavior) : (bOut:seq<output>)
        ensures |bOut| == |b| 
        ensures forall i :: (i >= 0 && i < |b|) 
            ==> (if (b[i].o == SubOut([Nil])) then
                    bOut[i] == Nil
                else 
                    bOut[i] == b[i].o)
        decreases |b|
    {
        if |b| == 0 then
            []
        else
            if b[0].o == SubOut([Nil]) then
                [Nil] + behaviorOutput(all_but_first(b))
            else
                [b[0].o] + behaviorOutput(all_but_first(b))
    }

/// EVAL CODE / CONTROL FLOW


    predicate validIfCond(s:state, o:operand)
    {
        ValidOperand(s,o) && ValidState(s) && isBoolData(OperandContents(s,o))
    }

    function evalCodeRE(c:codeRe, s:state) : (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures c.Block? ==> |b| == |evalBlockRE(c.block, s)|
        // ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlockRE(c.ifTrue,s)| else |b| == |evalBlockRE(c.ifFalse,s)|
        ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)
        
        decreases c, 0
    {
        reveal_ValidBehavior();
            match c
                case Ins(ins) => [evalInsRe(ins,s)]
                case Block(block) => evalBlockRE(block, s) 
                case IfElse(ifCond, ifT, ifF) => 
                    if (validIfCond(s,ifCond)) then
                        if dataToBool(OperandContents(s,ifCond)) then evalBlockRE(ifT, s) else evalBlockRE(ifF,s)
                    else
                        [s]
                case Divergence(pre,post,patched) => if patched then evalBlockRE(post,s) else evalBlockRE(pre,s)
                case NonImpactIns(NIIns) => [s]
                case CNil => [s]
    }

  function evalBlockRE(block:codeSeq, s:state): (b:behavior)
        ensures |b| > 0
        // ensures (first(block).CNil?) ==> |b| == 1
        // ensures forall c :: c in block && c.Ins? ==> |b| == |block|

    {
        if |block| == 0 then
            [s]
        else
            assert |block| > 0;
            if first(block).CNil? then
                [s]
            else
                assert |block| > 0;
                var metaBehavior := evalCodeRE(first(block),s);
                assert |block| > 0;
                var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
                var fullBlock := metaBehavior + theRest;
                assert |metaBehavior| == |evalCodeRE(first(block),s)|;
                assert |theRest| == |evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)))|;
                assert |fullBlock| == |metaBehavior| + |theRest|;

                fullBlock
    }

    function evalInsRe(ins:ins,s:state) : (s':state)
        // requires ValidInstruction(s, ins)
        // ensures ValidState(s) && ValidInstruction(s, ins) ==> StateNext(s,s')
        ensures s'.ok ==> NextStep(s,s',Step.evalInsStep(ins)) && StateNext(s,s');
        ensures (!ValidState(s) || !ValidInstruction(s, ins)) ==> !s'.ok;
        ensures ((!ValidState(s) || !ValidInstruction(s, ins)) && validEvalIns(ins,s,s')) ==> s'.ok
    {
        reveal_ValidBehavior();
        reveal_behaviorOutput();
        if (!ValidState(s) || !ValidInstruction(s, ins)) then 
            var notOK := s.(ok := false);
            notOK
        else match ins
            case ADD(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalADD(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert s'.ok;
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case SUB(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    assert dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case SDIV(dst,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalSDIV(OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSDIV(OperandContents(s,src1),OperandContents(s,src2))) then 
                    assert dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case ICMP(dst,cond,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                assert ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
            case TRUNC(dst,t,src,dstSize) => 
                var s' := stateUpdateVar(s,dst,evalTRUNC(OperandContents(s,src),dstSize));
                    assert ValidData(s',evalTRUNC(OperandContents(s,src),dstSize));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
            case ZEXT(dst,t,src,dstSize) =>
                var s' := stateUpdateVar(s,dst,evalZEXT(OperandContents(s,src),dstSize));
                assert ValidData(s',evalZEXT(OperandContents(s,src),dstSize));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
            case AND(dst,src1,src2)  =>
                var s' := stateUpdateVar(s,dst,evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)));   
                assert ValidData(s',evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)));   
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
            case LSHR(dst,src,shiftAmt) =>
                var s' := stateUpdateVar(s,dst,evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)));
                assert ValidData(s',evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)));
                 assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
            case STORE(valueToStore,ptr) =>
                var s' := s.(m := evalStore(s.m,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore)));
                if MemValid(s'.m) then
                    assert MemStateNext(s.m,s'.m,MemStep.storeStep(OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore),1));
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
            case LLVM_MEMCPY(dst,src,len,volatile) => 
                var s' := s.(o := Nil,m := evalMemCpy(s.m,OperandContents(s,dst),OperandContents(s,src)));
                if MemValid(s'.m) && ValidState(s') then
                    assert MemStateNext(s.m,s'.m,MemStep.memCpyStep(OperandContents(s,src).bid,OperandContents(s,dst).bid));
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
            case ALLOCA(dst,t) => var s' := State(s.lvs,s.gvs,AllocaStep(s.m,t),s.o,s.ok);
                s'
            case BR(if_cond, labelTrue,labelFalse) => s
            case UNCONDBR(goToLabel) => s
            case LOAD(dst,size,src) => s // placeholder
            case CALL(dst,fnc) =>
                var subB := evalBlockRE(fnc,s);
                if ValidBehavior(subB) && ValidOperand(last(subB),dst) then
                    assert |subB| > 0;
                    assert ValidState(last(subB));
                    if dst.GV? || dst.LV? then
                        var stemp := last(subB);
                        var subO := behaviorOutput(subB);
                        if true then // forall o :: o in subO ==> o == Nil
                            var s' := stemp.(o := Nil);
                            assert validEvalIns(ins,s,s');
                            assert s' == last(subB).(o := Nil);
                            s'
                        else
                            var s' := stemp.(o := SubOut(behaviorOutput(subB)));
                            assert s'.o == SubOut(behaviorOutput(subB));
                            assert validEvalIns(ins,s,s');
                            s'
                    else 
                        var subO := behaviorOutput(subB);
                        var s' := s.(o := SubOut(behaviorOutput(subB)));
                        assert s'.o == SubOut(behaviorOutput(subB));
                        assert validEvalIns(ins,s,s');
                        //assert s.o != s'.o;
                        s'
                else
                    var notOk := s.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
            case RET(val) => 
                var s' := s.(o := Out(OperandContents(s,val)));
                assert ValidState(s');
                assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                assert validEvalIns(ins,s,s');
                s'
            case GETELEMENTPTR(dst,t,op1,op2) => 
                if(MemValid(s.m) && ValidData(s,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))) then
                    var s' := stateUpdateVar(s,dst,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)));   
                    assert ValidState(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    //assert s != s';
                    s'
                else
                    var notOk := s.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
            case BITCAST(dst,src,castType) =>
                var s' := stateUpdateVar(s,dst,evalBITCAST(OperandContents(s,src),OperandContents(s,castType)));
                if ValidData(s',evalBITCAST(OperandContents(s,src),OperandContents(s,castType))) then 
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert s'.ok;
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
             case VISIBLE_OUT(o) => var s' := s.(o := o);
                assert ValidState(s');
                assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                assert validEvalIns(ins,s,s');
                s'
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(dst,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case SUB(dst,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case SDIV(dst,src1,src2) => (dst.LV? || dst.GV?)  && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && OperandContents(s,src1).itype.size == 4
                                         && OperandContents(s,src2).itype.size == 4
                                         && OperandContents(s,src2).val != 0
            case ICMP(dst,cond,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && t == OperandContents(s,src1).itype.size
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case TRUNC(dst,t,src,dstSize) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && t == OperandContents(s,src).itype.size
                                            && t > dstSize
                                            && isInt(OperandContents(s,dst))
            case ZEXT(dst,t,src,dstSize) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src) && isInt(OperandContents(s,src))
                                            && OperandContents(s,src).itype.size < dstSize
            case AND(dst,src1,src2) =>      (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                            && OperandContents(s,dst).itype.size == OperandContents(s,src1).itype.size
                                            && !OperandContents(s,dst).itype.signed
            case LSHR(dst,src,shiftAmt) =>  (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,shiftAmt)
                                && isInt(OperandContents(s,dst)) && isInt(OperandContents(s,src)) && isInt(OperandContents(s,shiftAmt))
                                && OperandContents(s,src).itype.size*8 > OperandContents(s,shiftAmt).val
                                && OperandContents(s,shiftAmt).val > 0
                                && isInt(OperandContents(s,dst)) && !OperandContents(s,dst).itype.signed 
            case STORE(valueToStore,ptr) => && ValidOperand(s,valueToStore) && ValidOperand(s,ptr)
                                        && OperandContents(s,valueToStore).Int? && (IntType(1, false) == OperandContents(s,valueToStore).itype)
                                        && MemValid(s.m) && OperandContents(s,ptr).Ptr? 
                                        && IsValidPtr(s.m,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,1)
                                        && s.m.mem[OperandContents(s,ptr).bid][OperandContents(s,ptr).offset].mb? 
                                        && s.m.mem[OperandContents(s,ptr).bid][OperandContents(s,ptr).offset].size == OperandContents(s,valueToStore).itype.size
            case LLVM_MEMCPY(dst,src,len,volatile) => && ValidOperand(s,dst) && ValidOperand(s,src) && OperandContents(s,dst).Ptr?
                                                     && OperandContents(s,src).Ptr? && OperandContents(s,dst).size >= OperandContents(s,src).size
                                                     && validBitWidth(len) && !volatile // dont support volatile right now
            case ALLOCA(dst,t) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && MemValid(s.m) && OperandContents(s,dst).Ptr? && validBitWidth(t)
            case RET(val) => && ValidOperand(s,val)
            case BR(if_cond, labelTrue,labelFalse) => && ValidOperand(s,if_cond)
                                                   && OperandContents(s,if_cond).Int? && !OperandContents(s,if_cond).itype.signed
                                                   && OperandContents(s,if_cond).itype.size == 1 
            case UNCONDBR(goToLabel) => true
            case CALL(dst,fnc) => (dst.LV? || dst.GV? || (dst.D? && dst.d.Void?)) && ValidOperand(s,dst) && |fnc| > 0
            case GETELEMENTPTR(dst,t,op1,op2) => (dst.LV? || dst.GV?) && MemValid(s.m) && ValidOperand(s,dst) && ValidOperand(s,op1) && ValidOperand(s,op2)
                                                   && OperandContents(s,op1).Ptr? && OperandContents(s,op2).Int?
                                                   && !OperandContents(s,op2).itype.signed
                                                   && validBitWidth(t)
                                                   && IsValidBid(s.m,OperandContents(s,op1).bid)
                                                //    && |s.m.mem[OperandContents(s,op1).bid]| == t
            case LOAD(dst,size,src) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src) 
                                && MemValid(s.m) && OperandContents(s,src).Ptr? 
                                && IsValidPtr(s.m,OperandContents(s,src).bid,OperandContents(s,src).offset,size)
            case BITCAST(dst,src,castType) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src) && ValidOperand(s,castType)
                                                        && ValidOperand(s,dst) 
                                                        && ( (OperandContents(s,src).Int? && OperandContents(s,castType).Int?) || (OperandContents(s,src).Ptr? && OperandContents(s,castType).Ptr?))
                                                        && ( (OperandContents(s,dst).Int? && OperandContents(s,castType).Int?) || (OperandContents(s,dst).Ptr? && OperandContents(s,castType).Ptr?))
                                                        && typesMatch(OperandContents(s,dst),OperandContents(s,castType))
            case VISIBLE_OUT(o) => true         
    
    }

    predicate validEvalIns(ins:ins, s:state, s':state)
    {   
        && s.ok 
        && ValidInstruction(s, ins) 
        && match ins
            case ADD(dst,t,src1,src2) => ValidState(s')
                                && ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case SUB(dst,t,src1,src2) => ValidState(s') 
                                && ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case SDIV(dst,src1,src2)=> ValidState(s') 
                                && ValidData(s',evalSDIV(OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSDIV(OperandContents(s,src1),OperandContents(s,src2)),s')
            case ICMP(dst,cond,t,src1,src2) => ValidState(s') 
                                && ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case TRUNC(dst,t,src,dstSize) => ValidState(s') //o == dst
                                && ValidData(s',evalTRUNC(OperandContents(s,src),dstSize))    
                                && evalUpdate(s, dst, evalTRUNC(OperandContents(s,src),dstSize),s')
            case ZEXT(dst,t,src,dstSize) => ValidState(s') // o == dst 
                                && ValidData(s',evalZEXT(OperandContents(s,src),dstSize))
                                && evalUpdate(s, dst, evalZEXT(OperandContents(s,src),dstSize),s')
            case AND(dst,src1,src2) => ValidState(s')  //o == dst 
                                && ValidData(s',evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)))   
                                && evalUpdate(s, dst, evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)),s')
            case LSHR(dst,src,shiftAmt) => ValidState(s') // o == dst 
                                && ValidData(s',evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)))
                                && evalUpdate(s, dst, evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)),s')
            case STORE(valueToStore,ptr) => ValidState(s') && Store(s.m,s'.m,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore))
                                        && (MemValid(s'.m))
            case LLVM_MEMCPY(dst,src,len,volatile) => ValidState(s') && memCpy(s.m, OperandContents(s,dst),OperandContents(s,src), s'.m)                            
            case ALLOCA(dst,t) => //Alloc(s.m,s'.m,s.m.nextBlock,t)
                                        ValidState(s') && ValidData(s',evalALLOCA(s.m,t))
                                        && s' == State(s.lvs,s.gvs,AllocaStep(s.m,t),s.o,s.ok)
                                        && evalAlloca(s, dst, evalALLOCA(s.m,t),t,s')
            case RET(val) => ValidState(s') && s'.m == s.m && s'.o == Out(OperandContents(s,val))   
            case BR(if_cond, labelTrue,labelFalse) => s == s'
            case UNCONDBR(goToLabel) =>  s == s'
            case CALL(dst,fnc)  =>  ValidState(s') && ValidOperand(s',dst) && ValidData(s',OperandContents(s',dst))// maybe adjsut //&& evalUpdate(s, dst, OperandContents(s',dst),s')
            case GETELEMENTPTR(dst,t,op1,op2) => ValidState(s') //o == dst 
                                && ValidData(s',evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))
                                && evalUpdate(s, dst, evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)),s')
            case LOAD(dst,size,src) => s == s' // placeholder
            case BITCAST(dst,src,castType) => ValidState(s')
                                            && ValidData(s',evalBITCAST(OperandContents(s,src),OperandContents(s,castType)))    
                                            && evalUpdate(s, dst, evalBITCAST(OperandContents(s,src),OperandContents(s,castType)),s')
            case VISIBLE_OUT(o) => ValidState(s')// && s == s'.(s'.o == o)
    }



    function stateUpdateVar(s:state, dst:operand, d:Data): (s':state)
         requires dst.LV? || dst.GV?
         requires MemValid(s.m) 
         requires ValidData(s,d)
         ensures MemStateNext(s.m,s'.m,MemStep.stutterStep);
         ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
         ensures forall gv :: gv in s.gvs ==> gv in s'.gvs
         ensures dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
         ensures dst.GV? ==> forall gv :: (gv in s.gvs && gv != dst.g) ==> s'.gvs[gv] == s.gvs[gv]; 
         ensures ValidOperand(s',dst)
         ensures ValidState(s) ==> evalUpdate(s,dst,d,s');
         //ensures s != s'


         {
             if dst.LV? then
                if (dst.l in s.lvs) then
                    var s' := s.(lvs := s.lvs[dst.l := d],o := Nil);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert (s.lvs[dst.l] != d) ==> s != s';
                    s'
                else
                    var s' := s.(lvs := s.lvs[dst.l := d],o := Nil);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert s != s';
                    s'
             else
                assert dst.GV?;
                var s' := s.(gvs := s.gvs[dst.g := d],o := Nil);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    //assert (s.gvs[dst.g] != d) ==> s.gvs != s'.gvs;
                    s'
         }

 predicate evalAlloca(s:state, o:operand, d:Data, size:nat,s':state)
        requires ValidState(s)
        requires ValidOperand(s,o)
        requires s' == State(s.lvs,s.gvs,AllocaStep(s.m,size),s.o,s.ok);
        // requires ValidState(s'); 
            // requires validBitWidth(size);
        // ensures o.D? ==> ValidData(s',d)
        ensures  ValidState(s')
    {

        var newMem := AllocaStep(s.m,size);
        // assert newMem == newMemTemp;
        // var d := evalALLOCA(s.m,size);
        assert MemValid(newMem);
        assert ValidVarState(s,s.lvs,s.gvs); 
        // assert ValidVarState(s',s'.lvs,s'.gvs);
        var newState := State(s.lvs,s.gvs,newMem,s.o,s.ok);
        assert newState.m == AllocaStep(s.m,size);
        assert s' == newState;
        equalStateVarsValid(s,newState,size);
        assert ValidState(newState);
        match o
            case D(data) => data == d && s' == newState
            case GV(g) => s' == newState
            case LV(l) => s' == newState
    }

     lemma equalStateVarsValid(s:state,s':state, size:nat)
        requires ValidState(s);
        requires s'.lvs == s.lvs;
        requires s'.gvs == s.gvs;
        requires s'.m == AllocaStep(s.m,size)
        ensures ValidVarState(s',s'.lvs,s'.gvs);
    {
        assert ValidState(s) ==> ValidVarState(s,s.lvs,s.gvs);
        assert ValidVarState(s,s.lvs,s.gvs) ==> (forall g:GlobalVar :: g in s.gvs  ==> ValidData(s,s.gvs[g]));
        assert forall bid:nat, offset:nat, size:bitWidth :: IsValidPtr(s.m,bid,offset,size) ==> IsValidPtr(s'.m,bid,offset,size);
        //         assert forall g:GlobalVar :: g in s.gvs  ==> ValidData(s,s.gvs[g]);
        //         assert forall l:LocalVar :: l in s.lvs ==> ValidData(s,s.lvs[l]);

        assert forall l:LocalVar :: l in s'.lvs  && s'.lvs[l].Void? ==> ValidData(s',s'.lvs[l]);
        assert forall l:LocalVar :: l in s'.lvs  && s'.lvs[l].Int? ==> ValidData(s',s'.lvs[l]);
        assert forall l:LocalVar :: l in s'.lvs  && s'.lvs[l].Bytes? ==> ValidData(s',s'.lvs[l]);
        assert forall l:LocalVar :: l in s'.lvs  && s'.lvs[l].Ptr? ==> ValidData(s',s'.lvs[l]);
        // assert forall g:GlobalVar :: g in s'.gvs  && s'.gvs[g].Void? ==> ValidData(s',s'.gvs[g]);
        // assert forall g:GlobalVar :: g in s'.gvs  && s'.gvs[g].Int? ==> ValidData(s',s'.gvs[g]);
        // assert forall g:GlobalVar :: g in s'.gvs  && s'.gvs[g].Bytes? ==> ValidData(s',s'.gvs[g]);
        assert forall g:GlobalVar :: g in s'.gvs  && s'.gvs[g].Ptr? ==> ValidData(s',s'.gvs[g]);
    }
    
//// Util Predicates

    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case D(d) => ValidData(s,d)
            case LV(l) => l in s.lvs && ValidData(s,s.lvs[l])
            case GV(g) => g in s.gvs && ValidData(s,s.gvs[g])
    }

    function method OperandContents(s:state, o:operand) : (out:Data)
        requires ValidOperand(s,o)
        requires ValidState(s)
    {

        
        match o
            case D(d) => d
            case LV(l) => s.lvs[l]
            case GV(g) => s.gvs[g]
           
    }

    lemma uniqueOperandContent(s:state,o:operand)
        requires ValidOperand(s,o)
        requires ValidState(s)
    {
        assert forall x,y :: (OperandContents(s,o) == x && OperandContents(s,o) == y) ==> x == y;
    }

    lemma uniqueOperandInState(s:state,o:operand)
        requires ValidOperand(s,o)
        requires o.LV?
        requires ValidState(s)
    {
        assert forall x:operand,y:operand :: (&& x.LV? 
                                                && y.LV?  
                                                && x.l in s.lvs 
                                                && y.l in s.lvs 
                                                && x == o
                                                && y== o) ==> x == y;
    }


    predicate evalUpdate(s:state, o:operand, data:Data, s':state)
        requires ValidState(s)
        requires ValidData(s',data)
        ensures evalUpdate(s, o, data, s') ==> ValidState(s')
    {
        
        
        match o
            case D(d) => data == d && s' == s.(o := Nil) 
            case GV(g) => s' == s.(gvs := s.gvs[g := data],o := Nil) 
            case LV(l) => s' == s.(lvs := s.lvs[l := data],o := Nil) 
            
    }




    // Control flow unwrap witness
        lemma unwrapBlockWitness(b:behavior,block:codeSeq,s:state) 
            returns (step:behavior,remainder:codeSeq,subBehavior:behavior)
            requires b == [s] + evalBlockRE(block,s);

            requires (|block| > 0 && first(block).IfElse?) ==> validIfCond(s,first(block).ifCond);
            // requires forall ins :: (ins in block && ins.Ins?) ==> !ins.ins.CALL? // doesnt work with CALLL rn
            // requires ValidState(s);
            ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse?) ==> |step| > 0
            ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> (b == [s] + step + evalCodeRE(Block(remainder) ,last(step)));
            ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
                        ensures (|block| > 0 && first(block).Ins?) ==> subBehavior == b[1..]

            ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> |remainder| == |block|-1
            ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> remainder == all_but_first(block);
            ensures  (|block| == 1 && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?)==> |remainder| == 0;
            ensures (|block| > 0 && !first(block).CNil? && remainder == [] && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==>  subBehavior == [last(step),last(step)];
            ensures (|block| > 0 && first(block).Ins?) ==> |step| == 1 
            ensures (|block| > 0 && first(block).Ins?) ==> step[0] == evalInsRe(first(block).ins,s)
            ensures (|block| > 0 && first(block).IfElse? && validIfCond(s,first(block).ifCond) && dataToBool(OperandContents(s,first(block).ifCond)))
                     ==> remainder == first(block).ifTrue + all_but_first(block);
            ensures (|block| > 0 && first(block).IfElse?  && validIfCond(s,first(block).ifCond) && !dataToBool(OperandContents(s,first(block).ifCond)))
                 ==> remainder == first(block).ifFalse + all_but_first(block);
            ensures (|block| > 0 && (first(block).Block? || first(block).IfElse?)) ==> step == [s];
            ensures (|block| > 0 && first(block).Block?) ==> remainder == first(block).block + all_but_first(block);
            ensures (|block| > 0 && (first(block).Block? || first(block).IfElse? || first(block).Divergence?)) ==> subBehavior == [s] + evalBlockRE(remainder,s);
            // ensures (|block| > 0 && (first(block).Divergence?)) ==> subBehavior == b;
            ensures (|block| > 0 && first(block).Divergence?) ==> step == [s];
            ensures (|block| > 0 && first(block).Divergence? && first(block).patched)
                     ==> remainder == first(block).post + all_but_first(block);
            ensures (|block| > 0 && first(block).Divergence? && !first(block).patched)
                     ==> remainder == first(block).pre + all_but_first(block);

            // ensures (|block| > 0 && first(block).IfElse? && first(block).ifCond ) ==> subBehavior == [s] +  evalBlockRE(first(block).ifTrue,s);
            // ensures (|block| > 0 && first(block).IfElse? && !first(block).ifCond ) ==> subBehavior == [s] +  evalBlockRE(first(block).ifFalse,s);


            // ensures 
            // requires |block| > 0;
            
        {
            // reveal_evalCodeRE();
            reveal_ValidBehavior();
            if (|block| == 0 || first(block).CNil?) {
                assert b == [s,s];
                step := [s];
                remainder := [];

                subBehavior := b[|step|..];
                assert b == [s] + step + all_but_first(subBehavior);
                assert !ValidBehavior(step) ==> !ValidBehavior(b);
                assert NextStep(s,step[0], Step.stutterStep());
                assert ValidState(s) ==> ValidBehavior([s] + step);

            }else{
                assert !(|block| == 0 || first(block).CNil?);
                if(first(block).Block?){
                    assert b == [s] + evalBlockRE(block,s);
                    // assert evalBlockRE(block,s) ==  evalBlockRE(first(block).block + all_but_first(block),s);
                    step := [s];
                    remainder := first(block).block + all_but_first(block);
                    assert |remainder| == |first(block).block| + |all_but_first(block)| ;
                    subBehavior := [s] + evalBlockRE(remainder,s);
               } else if(first(block).Divergence?){
                    step := [s];
                    if(first(block).patched){
                        remainder := first(block).post + all_but_first(block);
                    }else{
                        remainder := first(block).pre + all_but_first(block);
                    }
                    subBehavior := [s] + evalBlockRE(remainder,s);
                    // assert evalBlockRE(remainder,s) == evalBlockRE(block,s);
                //    subBehavior := b;
                }else if(first(block).IfElse? ){ 
                        step := [s];
                        if(dataToBool(OperandContents(s,first(block).ifCond))){
                            remainder := first(block).ifTrue + all_but_first(block);
                            //subBehavior := [s] + evalBlockRE(first(block).ifTrue,s);
                        }else{
                            remainder := first(block).ifFalse + all_but_first(block);
                            //subBehavior := [s] + evalBlockRE(first(block).ifFalse,s);
                        }
                        subBehavior := [s] + evalBlockRE(remainder,s);
                        // assert evalBlockRE(all_but_first(block),s) == evalBlockRE(all_but_first(remainder),s);
                        // assert subBehavior == b;
                        // assert evalBlockRE(remainder,s) == evalBlockRE(block,s);
                        // subBehavior := b;
                        
                }else{
                    assert first(block).Ins? || first(block).NonImpactIns?;
                    var metaBehavior := evalCodeRE(first(block),s);
                    // assert (first(block).Ins? && ValidInstruction(s,first(block).ins)) ==> ValidBehavior([s] + metaBehavior);
                    assert (first(block).Ins? && first(block).ins.CALL?) ==> metaBehavior == [evalInsRe(first(block).ins,s)];
                    var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
                    assert evalBlockRE(block,s) == metaBehavior + theRest;
                    assert b == [s] + evalBlockRE(block,s);
                    assert b == [s] + metaBehavior + theRest;
                    step := metaBehavior;
                    // assert ValidBehavior(step);
                    remainder := all_but_first(block);
                    
                    assert b[1..|step|+1] == step;
                    subBehavior := b[|step|..];
                    // assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
                    assert evalBlockRE([],last(step)) == [last(step)];
                    // assert b == [s] + b[1..|step|] + b[|step|..];
                    assert b == [s] + step + all_but_first(subBehavior);
                }
            }
        }
    


}
