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

module LLVM_def_NEW {

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
        pc:int,
        ok:bool)


///
    datatype version = Version(pre:bool,post:bool)

    datatype configuration = Config(ops:map<string, operand>)

    datatype output = Out(o:Data) | SubOut(os:seq<output>) | Nil

    // type codeSeq = seq<codeRe>

    datatype Code =
    | Ins(ins:ins)
    | Block(block:seq<Code>)
    | IfElse(ifCond:operand, ifTrue:Code, ifFalse:Code)
    | CNil
    // | Divergence(pre:seq<Code>,post:seq<Code>,patched:bool)
    // | NonImpactIns(NIIns:ins)
            
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
    | CALL(dst:operand,fnc:seq<Code>)
    | GETELEMENTPTR(dst:operand,t:bitWidth,op1:operand,op2:operand)
    | UNCONDBR(goToLabel:Code)
    | BR(if_cond:operand, labelTrue:Code,labelFalse:Code)
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
    | validToErrorStep()
    | errorStateStep()

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case evalInsStep(ins) => validEvalIns(ins,s,s') && s'.ok
            case stutterStep() => stutter(s,s')
            case validToErrorStep() => validToError(s,s')
            case errorStateStep() => errorStep(s,s')
    }

    predicate StateNext(s:state,s':state)
    {
        && exists step :: NextStep(s,s',step)
        // && ValidState(s)
    
    }

    
    predicate stutter(s:state,s':state)
    {
        s == s'
    }
    
    predicate validToError(s:state,s':state)
    {
        s.ok && !s'.ok
    }

    predicate errorStep(s:state,s':state)
    {
        !s.ok && !s'.ok
    }

    lemma validNonTrivalStepIsIns(s:state, s':state, step:Step)
        requires NextStep(s,s',step)
        requires ValidState(s)
        requires ValidState(s')
        requires s != s'
        ensures step.evalInsStep?;
    {
        assert step.evalInsStep?;
    }

    predicate {:opaque} ValidBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1 && ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    predicate {:opaque} ValidSimpleBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1) 
        || (&& |states| >= 2
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    lemma subValidBIsValid(b:behavior,s:state)
        requires ValidSimpleBehavior([s] + b);
        requires |b| > 0;
        ensures ValidSimpleBehavior(b);
        ensures StateNext(s,b[0]);
    {
        reveal_ValidSimpleBehavior();
        var combo := [s] + b;
        assert StateNext(combo[0],combo[1]);
        assert StateNext(s,b[0]);
        assert ValidSimpleBehavior([s]);
        if (|b| == 1)
        {
            assert ValidSimpleBehavior(b);
        }else{
            assert |b| >= 2;
            assert b == combo[1..];
            assert ValidSimpleBehavior(b);
        }
    }

    lemma validConcatIsValid(a:behavior,b:behavior)
        requires ValidSimpleBehavior(a);
        requires ValidSimpleBehavior(b);
        requires |a| > 0
        requires |b| > 0
        requires ValidSimpleBehavior([last(a)] + b);
        ensures ValidSimpleBehavior(a+b);
    {
        reveal_ValidSimpleBehavior();
        var combo := [last(a)] + b;
        assert ValidSimpleBehavior(combo);
        assert last(a) == combo[0];
        assert first(b) == combo[1];
        assert ValidSimpleBehavior(a+b);
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
//
function evalCodeFn(c:Code,s:state) : (b:behavior)
    ensures |b| > 0
    ensures (c.Ins?) ==> |b| == 1
    ensures b == [s] ==> NextStep(s,s, Step.stutterStep()) && StateNext(s,s);
    ensures  StateNext(s,b[0])
    ensures ValidSimpleBehavior([s] + b);
    decreases c, 0
{
    reveal_ValidSimpleBehavior();
    match c 
        case Ins(ins) => 
            var s' := evalInsRe(c.ins,s);
            [s']
        case Block(block) => 
            var blockB := evalCodeSeqFn(c.block,s); 
            blockB
        case IfElse(ifCond, ifT, ifF) => 
            if (validIfCond(s,ifCond)) then
                if dataToBool(OperandContents(s,ifCond)) then
                    var blockB_true := evalCodeFn(c.ifTrue,s); 
                    blockB_true 
                else 
                    var blockB_false := evalCodeFn(c.ifFalse,s); 
                    blockB_false
            else
                [s]
        case CNil => 
            [s]
}
function evalCodeSeqFn(block:seq<Code>, s:state) : (b:behavior)
    ensures |b| > 0;
    ensures b == [s] ==> NextStep(s,s, Step.stutterStep()) && StateNext(s,s);
    ensures StateNext(s,b[0]);
    ensures ValidSimpleBehavior([s] + b);
    ensures |block| == 0 ==> b == [s]
    decreases block
  {
    reveal_ValidSimpleBehavior();
    if |block| == 0 then
        [s]
    else
        var first := first(block);
        var remainder := all_but_first(block);
        var firstStep := evalCodeFn(first,s);
        var restB := evalCodeSeqFn(remainder,last(firstStep));
        subValidBIsValid(firstStep,s);
        subValidBIsValid(restB,last(firstStep));
        var seqB := firstStep + restB;
        // validConcatIsValid(firstStep,restB);
        seqB
    
  }

///////
    lemma evalCodeRE(c:Code, s:state) returns (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures  StateNext(s,b[0])
        ensures ValidSimpleBehavior([s] + b);
        // ensures c.Block? ==> |b| == |evalBlockRE(c.block, s)| //+1
        // // ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlockRE(c.ifTrue,s)| else |b| == |evalBlockRE(c.ifFalse,s)|
        // ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)
        
        decreases c, 0
    {
        reveal_ValidSimpleBehavior();
        if (c.Ins?){
            var s' := evalInsRe(c.ins,s);
            assert ValidSimpleBehavior([s] + [s']);
            b := [s'];
        }
        else if(c.Block?){
            var blockB := evalCodeSeq(c.block,s); 
            assert ValidSimpleBehavior([s] + blockB);
            b := blockB;
        }else if(c.IfElse?){
            if (validIfCond(s,c.ifCond)) {
                if dataToBool(OperandContents(s,c.ifCond)){
                    var blockB_true := evalCodeFn(c.ifTrue,s); 
                    assert ValidSimpleBehavior([s] + blockB_true);
                    b := blockB_true;
                }  else {
                    var blockB_false := evalCodeFn(c.ifFalse,s); 
                    assert ValidSimpleBehavior([s] + blockB_false);
                    b := blockB_false;
                }
            }else{
                assert NextStep(s,s, Step.stutterStep());
                assert StateNext(s,s);
                b := [s];
            }
        }else{
            assert c.CNil?;
            assert NextStep(s,s, Step.stutterStep());
        assert StateNext(s,s);
            b := [s];
        }
    }


  lemma evalCodeSeq(block:seq<Code>, s:state) returns (b:behavior)
    ensures |b| > 0;
    ensures StateNext(s,b[0]);
    ensures ValidSimpleBehavior([s] + b);
    decreases block,0
  {
    reveal_ValidSimpleBehavior();
    if (|block| == 0) {
        var stutter := [s];
        assert NextStep(s,stutter[0], Step.stutterStep());
        assert StateNext(s,stutter[0]);
        assert ValidSimpleBehavior([s] + stutter);
        assert |stutter| == 1;
        b := stutter;
        // remainder := [CNil];
    }else{
        var first := first(block);
        var remainder := all_but_first(block);

        var firstStep := evalCodeRE(first,s);
        assert StateNext(s,firstStep[0]);
        var restB := evalCodeSeq(remainder,last(firstStep));

        assert ValidSimpleBehavior([s] + firstStep);
        subValidBIsValid(firstStep,s);
        assert ValidSimpleBehavior(firstStep);
        assert ValidSimpleBehavior([last(firstStep)] + restB);
        subValidBIsValid(restB,last(firstStep));
        assert ValidSimpleBehavior(restB);
        var seqB := firstStep + restB;
        validConcatIsValid(firstStep,restB);
        assert ValidSimpleBehavior(seqB);

        b := seqB;
    }
  }

    function incPC(s:state):(s':state)
        ensures s' == s.(pc := s.pc+1);
        ensures s != s';
    {
        var s' := s.(pc := s.pc+1);
        s'
    }

    function evalInsRe(ins:ins,s:state) : (s':state)
        // requires ValidInstruction(s, ins)
        // ensures ValidState(s) && ValidInstruction(s, ins) ==> StateNext(s,s')
        ensures  StateNext(s,s');
        ensures s'.ok ==> NextStep(s,s',Step.evalInsStep(ins))
        // ensures s'.ok ==> s != s'
        ensures (!s.ok || !ValidInstruction(s, ins)) ==> !s'.ok;
        ensures ((!s.ok || !ValidInstruction(s, ins)) && validEvalIns(ins,s,s')) ==> s'.ok
    {
        reveal_ValidBehavior();
        reveal_behaviorOutput();
        if (!s.ok || !ValidInstruction(s, ins)) then 
            var notOK := s.(ok := false);
            if !s.ok then
                assert NextStep(s,notOK,errorStateStep());
                assert StateNext(s,notOK);
                // assert errorStep(s,notOK); 
                notOK
            else 
                assert s.ok;
                assert !notOK.ok;
                assert  NextStep(s,notOK,validToErrorStep());
                assert StateNext(s,notOK);
                notOK
        else match ins
            case ADD(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalADD(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    var s' := incPC(s');
                    assert s'.pc == s.pc+1;
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert s'.ok;
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert  NextStep(s,notOk,validToErrorStep());
                    notOk
            case SUB(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    var s' := incPC(s');
                    assert dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert  NextStep(s,notOk,validToErrorStep());
                    notOk
            case SDIV(dst,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalSDIV(OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSDIV(OperandContents(s,src1),OperandContents(s,src2))) then 
                    var s' := incPC(s');
                    assert dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert  NextStep(s,notOk,validToErrorStep());
                    notOk
            case ICMP(dst,cond,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                assert ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                    var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
            case TRUNC(dst,t,src,dstSize) => 
                var s' := stateUpdateVar(s,dst,evalTRUNC(OperandContents(s,src),dstSize));
                    var s' := incPC(s');
                    assert ValidData(s',evalTRUNC(OperandContents(s,src),dstSize));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
            case ZEXT(dst,t,src,dstSize) =>
                var s' := stateUpdateVar(s,dst,evalZEXT(OperandContents(s,src),dstSize));
                assert ValidData(s',evalZEXT(OperandContents(s,src),dstSize));
                   var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
            case AND(dst,src1,src2)  =>
                var s' := stateUpdateVar(s,dst,evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)));   
                assert ValidData(s',evalAND(OperandContents(s,dst).itype.size,OperandContents(s,src1),OperandContents(s,src2)));   
                    var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
            case LSHR(dst,src,shiftAmt) =>
                var s' := stateUpdateVar(s,dst,evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)));
                var s' := incPC(s');
                assert ValidData(s',evalLSHR(OperandContents(s,src),OperandContents(s,shiftAmt)));
                 assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
            case STORE(valueToStore,ptr) =>
                var s' := s.(m := evalStore(s.m,OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore)));
                if MemValid(s'.m) then
                    var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.storeStep(OperandContents(s,ptr).bid,OperandContents(s,ptr).offset,OperandContents(s,valueToStore),1));
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert  NextStep(s,notOk,validToErrorStep());
                    notOk
            case LLVM_MEMCPY(dst,src,len,volatile) => 
                var s' := s.(o := Nil,m := evalMemCpy(s.m,OperandContents(s,dst),OperandContents(s,src)));
                if MemValid(s'.m) && ValidState(s') then
                    var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.memCpyStep(OperandContents(s,src).bid,OperandContents(s,dst).bid));
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert  NextStep(s,notOk,validToErrorStep());
                    notOk
            case ALLOCA(dst,t) => 
                var s' := State(s.lvs,s.gvs,AllocaStep(s.m,t),s.o,s.pc,s.ok);
                var s' := incPC(s');
                assert MemStateNext(s.m,s'.m,MemStep.allocStep(s.m.nextBlock,t));
                assert validEvalIns(ins,s,s');
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
            case BR(if_cond, labelTrue,labelFalse) =>
                var s' := incPC(s); 
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
            case UNCONDBR(goToLabel) => 
                var s' := incPC(s); 
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
            case LOAD(dst,size,src) => 
                var s' := incPC(s); 
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
            case CALL(dst,fnc) =>
                var s' := incPC(s); 
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
                // var subB := evalBlockRE(fnc,s);
                // if ValidBehavior(subB) && ValidOperand(last(subB),dst) then
                //     assert |subB| > 0;
                //     assert ValidState(last(subB));
                //     if dst.GV? || dst.LV? then
                //         var stemp := last(subB);
                //         var subO := behaviorOutput(subB);
                //         if true then // forall o :: o in subO ==> o == Nil
                //             var s' := stemp.(o := Nil);
                //             assert validEvalIns(ins,s,s');
                //             assert s' == last(subB).(o := Nil);
                //             assert NextStep(s,s',Step.evalInsStep(ins));
                //             assert StateNext(s,s');
                //             s'
                //         else
                //             var s' := stemp.(o := SubOut(behaviorOutput(subB)));
                //             assert s'.o == SubOut(behaviorOutput(subB));
                //             assert validEvalIns(ins,s,s');
                //             assert NextStep(s,s',Step.evalInsStep(ins));
                //             assert StateNext(s,s');
                //             s'
                //     else 
                //         var subO := behaviorOutput(subB);
                //         var s' := s.(o := SubOut(behaviorOutput(subB)));
                //         assert s'.o == SubOut(behaviorOutput(subB));
                //         assert validEvalIns(ins,s,s');
                //         assert NextStep(s,s',Step.evalInsStep(ins));
                //         assert StateNext(s,s');
                //         //assert s.o != s'.o;
                //         s'
                // else
                //     var notOk := s.(ok := false);
                //     assert  NextStep(s,notOk,validToErrorStep());
                //     notOk
            case RET(val) => 
                var s' := s.(o := Out(OperandContents(s,val)));
                var s' := incPC(s');
                assert ValidState(s');
                assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                assert validEvalIns(ins,s,s');
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
                s'
            case GETELEMENTPTR(dst,t,op1,op2) => 
                if(MemValid(s.m) && ValidData(s,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))) then
                    var s' := stateUpdateVar(s,dst,evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)));   
                    var s' := incPC(s');
                    assert ValidState(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    //assert s != s';
                    s'
                else
                    var notOk := s.(ok := false);
                    assert NextStep(s,notOk, Step.validToErrorStep());
                    notOk
            case BITCAST(dst,src,castType) =>
                var s' := stateUpdateVar(s,dst,evalBITCAST(OperandContents(s,src),OperandContents(s,castType)));
                if ValidData(s',evalBITCAST(OperandContents(s,src),OperandContents(s,castType))) then 
                    var s' := incPC(s');
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert s'.ok;
                    assert NextStep(s,s',Step.evalInsStep(ins));
                    assert StateNext(s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                     assert NextStep(s,notOk, Step.validToErrorStep());
                    notOk
             case VISIBLE_OUT(o) => 
                var s' := s.(o := o);
                assert ValidState(s');
                var s' := incPC(s');
                assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                assert validEvalIns(ins,s,s');
                assert NextStep(s,s',Step.evalInsStep(ins));
                assert StateNext(s,s');
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
        && s'.pc == s.pc + 1
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
            case ALLOCA(dst,t) => ValidState(s') && ValidData(s',evalALLOCA(s.m,t))
                                  && s' == State(s.lvs,s.gvs,AllocaStep(s.m,t),s.o,s.pc+1,s.ok)
                                  && evalAlloca(s, dst, evalALLOCA(s.m,t),t,s')
            case RET(val) => ValidState(s') && s'.m == s.m && s'.o == Out(OperandContents(s,val))   
            case BR(if_cond, labelTrue,labelFalse) =>  s' == incPC(s) //s == s'
            case UNCONDBR(goToLabel) =>  s' == incPC(s)// s == s'
            case CALL(dst,fnc)  =>  ValidState(s') && ValidOperand(s',dst) && ValidData(s',OperandContents(s',dst))// maybe adjsut //&& evalUpdate(s, dst, OperandContents(s',dst),s')
            case GETELEMENTPTR(dst,t,op1,op2) => ValidState(s') //o == dst 
                                && ValidData(s',evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)))
                                && evalUpdate(s, dst, evalGETELEMENTPTR(s.m,t,OperandContents(s,op1),OperandContents(s,op2)),s')
            // case LOAD(dst,size,src) => ValidState(s') 
            //                            && s'.m == s.m 
            //                            && ValidData(s',evalLOAD(s.m,s'.m,size,OperandContents(s,src)))
            //                            && evalUpdate(s, dst, evalLOAD(s.m,s'.m,size,OperandContents(s,src)),s')
            case LOAD(dst,size,src) => s' == incPC(s)  //s == s' // placeholder
            case BITCAST(dst,src,castType) => ValidState(s')
                                            && ValidData(s',evalBITCAST(OperandContents(s,src),OperandContents(s,castType)))    
                                            && evalUpdate(s, dst, evalBITCAST(OperandContents(s,src),OperandContents(s,castType)),s')
            case VISIBLE_OUT(o) =>  s'.pc == s.pc+1 && ValidState(s')// && s == s'.(s'.o == o)
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
        requires s' == State(s.lvs,s.gvs,AllocaStep(s.m,size),s.o,s.pc+1,s.ok);
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
        var newState := State(s.lvs,s.gvs,newMem,s.o,s.pc+1,s.ok);
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
            case D(d) => data == d && s' == s.(o := Nil, pc := s.pc +1) 
            case GV(g) => s' == s.(gvs := s.gvs[g := data],o := Nil,pc := s.pc +1) 
            case LV(l) => s' == s.(lvs := s.lvs[l := data],o := Nil,pc := s.pc +1) 
            
    }


    lemma unwrapCodeWitness(b:behavior,c:seq<Code>,s:state) 
            returns (step:behavior,remainder:seq<Code>,subBehavior:behavior)
        requires b == evalCodeSeqFn(c,s);
        // requires b == evalCodeRE(c,s)
        ensures |c| > 0 ==> step == evalCodeFn(first(c),s);
        ensures |c| > 0 ==> remainder == c[1..];
        ensures |c| > 0 ==> subBehavior == evalCodeSeqFn(c[1..],last(evalCodeFn(first(c),s)));

        // ensures (|c| > 0 ) ==> subBehavior == b[1..];
        // ensures (|c| == 0 ) ==> subBehavior == evalBlockRE(remainder,step);
    {
        if(|c| == 0){
            step := [s];
            remainder := [];
            subBehavior := [];
            assert NextStep(s,step[0], Step.stutterStep());
            assert subBehavior == b[1..];
        }else{
            assert |c| > 0;
            var first := first(c);
            if (first.CNil?) {
                step := [s];
                remainder := c[1..];
                subBehavior := evalCodeSeqFn(remainder,s);
                assert NextStep(s,step[0], Step.stutterStep());
                assert subBehavior == b[1..];
            }else if(first.Ins?) {
                    step := evalCodeFn(first, s);
                    assert |step| == 1;
                    assert step[0].ok ==> NextStep(s,step[0],Step.evalInsStep(first.ins));
                    assert StateNext(s,step[0]);
                    remainder := c[1..];
                    subBehavior := evalCodeSeqFn(remainder,step[0]);
                    assert subBehavior == b[1..];
            } else if(first.Block?){
                if(|first.block| == 0) { 
                    step := [s];
                    assert |step| == 1;
                    remainder := c[1..];
                    subBehavior := evalCodeSeqFn(remainder,s);
                    assert NextStep(s,step[0], Step.stutterStep());
                    var firstStep := evalCodeFn(first,s);
                    var restB := evalCodeSeqFn(remainder,last(firstStep));
                    assert b == firstStep + restB;
                    assert firstStep == evalCodeSeqFn(first.block,s); 
                    // assert firstStep == [s];
                    assert subBehavior == b[1..];
                }else{
                //     assert |first.block| > 0;
                    step := evalCodeFn(first,s);
                    remainder := c[1..];
                    subBehavior := evalCodeSeqFn(remainder,last(step));
                //     assert StateNext(s,step);
                //     remainder := all_but_first(first.block) + c[1..];
                //     subBehavior := evalCodeSeqFn(remainder,step);
                    
                //     var firstStep := evalCodeFn(first,s);
                //     var restB := evalCodeSeqFn(all_but_first(c),last(firstStep));
                // assert restB == evalCodeSeqFn(c[1..],last(firstStep));
                // assert b == firstStep + restB;

                //     assert step == firstStep[0];

                //     // assert last(firstStep) == last(evalCodeSeqFn(all_but_first(first.block),step));

                //     assert firstStep == evalCodeSeqFn(first.block,s);
                //     // assert firstStep[1..] == evalCodeSeqFn(all_but_first(first.block),step);
                //     var firstStep_firstStep := evalCodeFn(first.block[0],s);
                //     var restB_firstStep :=  evalCodeSeqFn(all_but_first(first.block),last(firstStep_firstStep));
                //     assert firstStep == firstStep_firstStep + restB_firstStep;
                //     assert firstStep_firstStep[0] == step;
                // assert |firstStep_firstStep| == 1;
                // assert firstStep == [step] + evalCodeSeqFn(all_but_first(first.block),step);
                // assert subBehavior == b[1..];
                }
            }
            step := evalCodeFn(first,s);
                    remainder := c[1..];
                    subBehavior := evalCodeSeqFn(remainder,last(step));
        }
        
    }


    /////////////// OLD

    // // Control flow unwrap witness
    //     lemma unwrapBlockWitness(b:behavior,block:seq<Code>,s:state) 
    //         returns (step:behavior,remainder:seq<Code>,subBehavior:behavior)
    //         requires b == [s] + evalBlockRE(block,s);

    //         requires (|block| > 0 && first(block).IfElse?) ==> validIfCond(s,first(block).ifCond);
    //         // requires forall ins :: (ins in block && ins.Ins?) ==> !ins.ins.CALL? // doesnt work with CALLL rn
    //         // requires ValidState(s);
    //         // ensures subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
    //         ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse?) ==> |step| > 0
    //         ensures (|subBehavior| > 0 && |block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> ( b == [s] + step + all_but_first(subBehavior));
    //         ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
    //                     ensures (|block| > 0 && first(block).Ins?) ==> subBehavior == b[1..]

    //         ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> |remainder| == |block|-1
    //         ensures (|block| > 0 && !first(block).CNil? && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==> remainder == all_but_first(block);
    //         ensures  (|block| == 1 && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?)==> |remainder| == 0;
    //         ensures (|block| > 0 && !first(block).CNil? && remainder == [] && !first(block).Block? && !first(block).IfElse? && !first(block).Divergence?) ==>  subBehavior == [last(step),last(step)];
    //         ensures (|block| > 0 && first(block).Ins?) ==> |step| == 1 
    //         ensures (|block| > 0 && first(block).Ins?) ==> step[0] == evalInsRe(first(block).ins,s)
    //         ensures (|block| > 0 && first(block).IfElse? && validIfCond(s,first(block).ifCond) && dataToBool(OperandContents(s,first(block).ifCond)))
    //                  ==> remainder == first(block).ifTrue + all_but_first(block);
    //         ensures (|block| > 0 && first(block).IfElse?  && validIfCond(s,first(block).ifCond) && !dataToBool(OperandContents(s,first(block).ifCond)))
    //              ==> remainder == first(block).ifFalse + all_but_first(block);
    //         ensures (|block| > 0 && (first(block).Block? || first(block).IfElse?)) ==> step == [s];
    //         ensures (|block| > 0 && first(block).Block?) ==> remainder == first(block).block + all_but_first(block);
    //         ensures (|block| > 0 && (first(block).Block? || first(block).IfElse? || first(block).Divergence?)) ==> subBehavior == [s] + evalBlockRE(remainder,s);
    //     // ensures (|block| > 0 && (first(block).Block?)) ==> subBehavior == b[|step|..]; //[s] + evalBlockRE(remainder,s);

    //         // ensures (|block| > 0 && (first(block).Divergence?)) ==> subBehavior == b;
    //         ensures (|block| > 0 && first(block).Divergence?) ==> step == [s];
    //         ensures (|block| > 0 && first(block).Divergence? && first(block).patched)
    //                  ==> remainder == first(block).post + all_but_first(block);
    //         ensures (|block| > 0 && first(block).Divergence? && !first(block).patched)
    //                  ==> remainder == first(block).pre + all_but_first(block);
    //         ensures |block| > 0 && first(block).CNil? ==> remainder == all_but_first(block);
    //         ensures |block| > 0 && first(block).CNil? ==> step == [s];
    //                     ensures |block| > 0 && first(block).CNil? ==> subBehavior == [last(step)] + evalBlockRE(remainder,last(step));



    //         // ensures (|block| > 0 && first(block).IfElse? && first(block).ifCond ) ==> subBehavior == [s] +  evalBlockRE(first(block).ifTrue,s);
    //         // ensures (|block| > 0 && first(block).IfElse? && !first(block).ifCond ) ==> subBehavior == [s] +  evalBlockRE(first(block).ifFalse,s);


    //         // ensures 
    //         // requires |block| > 0;
            
    //     {
    //         // reveal_evalCodeRE();
    //         reveal_ValidBehavior();
    //         if (|block| == 0 ) {
    //             assert b == [s,s];
    //             step := [s];
    //             remainder := [];

    //             subBehavior := b[|step|..];
    //             assert b == [s] + step + all_but_first(subBehavior);
    //             assert !ValidBehavior(step) ==> !ValidBehavior(b);
    //             assert NextStep(s,step[0], Step.stutterStep());
    //             assert ValidState(s) ==> ValidBehavior([s] + step);

    //         }else if(first(block).CNil?){ // added 
    //             assert b == [s] + evalBlockRE(block,s);
    //             step := [s];
    //             remainder := all_but_first(block);

    //             subBehavior := [s] + evalBlockRE(remainder,s);
    //             assert b == [s] + evalBlockRE(block,s);
    //             assert !ValidBehavior(step) ==> !ValidBehavior(b);
    //             assert NextStep(s,step[0], Step.stutterStep());
    //             assert ValidState(s) ==> ValidBehavior([s] + step);
    //             assert subBehavior == [s] + evalBlockRE(remainder,s);
    //             // assert subBehavior == b[|step|..];
    //             assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));

            
    //         }else{
    //             assert !(|block| == 0 || first(block).CNil?);
    //             if(first(block).Block?){
    //                 assert b == [s] + evalBlockRE(block,s);

    //                 // assert evalBlockRE(block,s) ==  evalBlockRE(first(block).block + all_but_first(block),s);
                    
    //                 step := [s];
    //                 // step := evalCodeRE(first(first(block).block),s);
    //                 remainder := first(block).block + all_but_first(block);
    //                 // remainder := all_but_first(first(block)) + all_but_first(block);
    //                 assert |remainder| == |first(block).block| + |all_but_first(block)| ;
    //                 subBehavior := [s] + evalBlockRE(remainder,s);
    //                 // subBehavior := [s] + b[|step|..];
    //                 // assert b == [s] + evalBlockRE(block,s);
    //                 // assert (|block| > 0 && !first(block).CNil?);
    //                 // assert evalBlockRE(block,s) == [s] + evalBlockRE(remainder,s);
    //                 //  assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
    //                 //  assert b == [s] + step + all_but_first(subBehavior);
    //                 assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
    //                 //  assert b == [s] + step + evalCodeRE(Block(remainder) ,last(step)); // <----
    //            } else if(first(block).Divergence?){
    //                 step := [s];
    //                 if(first(block).patched){
    //                     remainder := first(block).post + all_but_first(block);
    //                 }else{
    //                     remainder := first(block).pre + all_but_first(block);
    //                 }
    //                 subBehavior := [s] + evalBlockRE(remainder,s);
    //                 // assert evalBlockRE(remainder,s) == evalBlockRE(block,s);
    //             //    subBehavior := b;
    //             }else if(first(block).IfElse? ){ 
    //                     step := [s];
    //                     if(dataToBool(OperandContents(s,first(block).ifCond))){
    //                         remainder := first(block).ifTrue + all_but_first(block);
    //                         //subBehavior := [s] + evalBlockRE(first(block).ifTrue,s);
    //                     }else{
    //                         remainder := first(block).ifFalse + all_but_first(block);
    //                         //subBehavior := [s] + evalBlockRE(first(block).ifFalse,s);
    //                     }
    //                     subBehavior := [s] + evalBlockRE(remainder,s);
    //                     // assert evalBlockRE(all_but_first(block),s) == evalBlockRE(all_but_first(remainder),s);
    //                     // assert subBehavior == b;
    //                     // assert evalBlockRE(remainder,s) == evalBlockRE(block,s);
    //                     // subBehavior := b;
                        
    //             }else{
    //                 assert first(block).Ins? || first(block).NonImpactIns?;
    //                 var metaBehavior := evalCodeRE(first(block),s);
    //                 // assert (first(block).Ins? && ValidInstruction(s,first(block).ins)) ==> ValidBehavior([s] + metaBehavior);
    //                 assert (first(block).Ins? && first(block).ins.CALL?) ==> metaBehavior == [evalInsRe(first(block).ins,s)];
    //                 var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
    //                 assert evalBlockRE(block,s) == metaBehavior + theRest;
    //                 assert b == [s] + evalBlockRE(block,s);
    //                 assert b == [s] + metaBehavior + theRest;
    //                 step := metaBehavior;
    //                 // assert ValidBehavior(step);
    //                 remainder := all_but_first(block);
                    
    //                 assert b[1..|step|+1] == step;
    //                 assert |step| == 1;
    //                 subBehavior := b[|step|..];
    //                 // assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
    //                 assert evalBlockRE([],last(step)) == [last(step)];
    //                 // assert b == [s] + b[1..|step|] + b[|step|..];
    //                 assert b == [s] + step + all_but_first(subBehavior);
    //             }
    //         }
    //     }
    
//   function evalBlockRE(block:seq<Code>, s:state): (b:behavior)
//         ensures |b| > 0
//         // ensures (first(block).CNil?) ==> |b| == 1
//         // ensures forall c :: c in block && c.Ins? ==> |b| == |block|
//         // ensures (|block| > 0 && !first(block).CNil?) ==>
//         //     b == evalCodeRE(first(block),s) + evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)));

//     {
//         if |block| == 0 then
//             [s]
//         else
//             assert |block| > 0;
//             // if first(block).CNil? then
//             //     [s]
//             // else
//                 assert |block| > 0;
//                 var metaBehavior := evalCodeRE(first(block),s);
//                 assert |block| > 0;
//                 var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
//                 var fullBlock := metaBehavior + theRest;
//                 assert |metaBehavior| == |evalCodeRE(first(block),s)|;
//                 assert |theRest| == |evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)))|;
//                 assert |fullBlock| == |metaBehavior| + |theRest|;

//                 fullBlock
//     }

    // lemma subCodeSeqIsSmaller(c:seq<Code>)
    //     requires |c| > 0
    // {
    //     var subCodeSeq := all_but_first(c);
    //     if(first(c).Ins?)
    //     {
    //         assert |c| > |subCodeSeq|;
    //     }
    //     else if (first(c).Block?)
    //     {
    //         assert |c| > |subCodeSeq|;
    //         var unwrap := first(c).block + subCodeSeq;
    //         assert |c| == |subCodeSeq| + 1;
    //         assert |unwrap| == |first(c).block| + |subCodeSeq|;
    //         assert codeSeqLengthV2([first(c)]) > codeSeqLengthV2(first(c).block);
    //     }
    //     // assert codeSeqLength(c,0) >= codeSeqLength(subCodeSeq,0);
    // }
    // function codeReLength(c:Code) : (len:int)
    //     // decreases blockLength(c);
    //     // ensures |c| > 0 ==> blockLength(all_but_first(c)) <= blockLength(c);
    //     ensures len >= 0
    // {
    //         match c
    //             case Ins(ins) =>  1
    //             case Block(block) => 1 + codeSeqLengthV2(block)
    //             case IfElse(ifCond, ifT, ifF) => 1 + codeSeqLengthV2(ifT) + codeSeqLengthV2(ifF)
    //             // case Divergence(pre,post,patched) => 0
    //             // case NonImpactIns(NIIns) => 0
    //             case CNil => 0
    // }

    // function codeSeqLengthV2(c:seq<Code>) : (len:int)
    //     ensures len >= 0
    //     ensures |c| > 0 ==> codeSeqLengthV2(c) >= codeSeqLengthV2(all_but_first(c))
    //     ensures |c| > 0 && first(c).Block? ==> (codeSeqLengthV2(c) ==  codeReLength(first(c)) + codeSeqLengthV2(all_but_first(c)));
    //     ensures |c| > 0 && first(c).Block? ==> (codeSeqLengthV2(c) == 1 + codeSeqLengthV2(first(c).block) + codeSeqLengthV2(all_but_first(c)));
    //     // ensures forall i :: i in c && i.Ins? ==> |c| == codeSeqLengthV2(c)
    //     // ensures codeSeqLengthV2(c)
    //     // ensures forall a:codeSeq,b:codeSeq :: (a + b == c) ==> codeSeqLengthV2(c) == codeSeqLengthV2(a) + codeSeqLengthV2(b);
    // {
    //      if |c| == 0 then
    //         0
    //     else
    //         var first := first(c);
    //         assert codeReLength(first) >= 0;
    //         assert first.Ins? ==> codeReLength(first) == 1;
    //         // assert if forall i :: i in all_but_first(c) && i.Ins? then |all_but_first(c)| == codeSeqLengthV2(all_but_first(c)) else true;
    //         codeReLength(first) + codeSeqLengthV2(all_but_first(c))
    // }
    // lemma codeSeqLengthV3(c:seq<Code>) returns (len:int)
    // {
    //     if |c| == 0 {
    //         len := 0;
    //     }else{
    //         assert |c| > 0;
    //         len := 0;
    //         var cr := c;
    //         while(|cr| > 0)
    //             decreases |cr|
    //         {
    //             var first := first(cr);
    //             cr := all_but_first(cr);
    //             if (first.Ins?)
    //             {
    //                 len := len +1;
    //             }else if(first.Block?)
    //             {
    //                 // len := codeSeqLengthV3(first.block);
    //             }
    //             len := len +1;
    //         }
           
    //     }
    // }

    // lemma codeSeqLengthV2Addition(a:seq<Code>,b:seq<Code>,c:seq<Code>)
    //     requires c == a + b
    //     requires forall i :: i in a ==> i.Ins?;
    //     requires forall i :: i in b ==> i.Ins?;

    //     requires |c| > 0
    // {
    //     if (|a| == 0)
    //     {
    //         assert c == b;
    //         assert codeSeqLengthV2(a) == 0;
    //         assert codeSeqLengthV2(c) == codeSeqLengthV2(a) + codeSeqLengthV2(b);
    //     }
    //     else if(|b| == 0)
    //     {
    //         assert c == a;
    //         assert codeSeqLengthV2(b) == 0;
    //         assert codeSeqLengthV2(c) == codeSeqLengthV2(a) + codeSeqLengthV2(b);
    //     }else{
    //         assert |c| == |a| + |b|;
    //         assert codeSeqLengthV2(c) == codeSeqLengthV2(a+b);
    //         var d := [Ins(RET(D(Void)))];
    //         var e := [Ins(RET(D(Void)))];
    //         var f := [Ins(RET(D(Void))),Ins(RET(D(Void)))];
    //         assert f == d + e;
    //         assert codeSeqLengthV2(f) == codeSeqLengthV2(d) + codeSeqLengthV2(e);
    //         // assert codeSeqLengthV2(d) == 1;
    //         // assert codeSeqLengthV2(a + d) == codeSeqLengthV2(a) + 1;
    //         // assert codeSeqLengthV2(a) + codeSeqLengthV2(d) == codeSeqLengthV2(a + d);
    //         // assert codeSeqLengthV2(c) > codeSeqLengthV2(a);
    //         // assert codeSeqLengthV2(c) == codeSeqLengthV2(a) + codeSeqLengthV2(b);
    //     }
    // }


    // function codeSeqLength(c:seq<Code>,curr:int) : int
    // {
    //     if |c| == 0 then
    //         curr
    //     else
    //     var first := first(c);
    //     match first
    //         case Ins(ins) =>  codeSeqLength(all_but_first(c),curr + 1)
    //         case Block(block) => codeSeqLength(all_but_first(c),curr + codeSeqLength(first.block,0))
    //         case IfElse(ifCond, ifT, ifF) => codeSeqLength(all_but_first(c),curr + codeSeqLength(first.ifTrue,0) + codeSeqLength(first.ifFalse,0))
    //         // case Divergence(pre,post,patched) => 0
    //         // case NonImpactIns(NIIns) => 0
    //         case CNil => 0
    // }

    //  lemma subBehaviorHasSameLastState(s:state,b:behavior,c:seq<Code>) returns (b':behavior)
    //     requires b ==  evalCodeSeqFn(c,s);
    //     requires |c| > 0;
    //     // ensures b[1..] == b';
    //     decreases c,0
    // {
    //     var firstStep := evalCodeFn(first(c),s);
    //     var restB := evalCodeSeqFn(all_but_first(c),last(firstStep));
    //     assert b == firstStep + restB;
    //     var step := b[0];
    //     assert StateNext(s,step);
    //     var subC := c[1..];
    //     // var fullSub := [Block(all_but_first(c[0].block))] + all_but_first(c);
    //     // assert |fullSub| > 0;
    //     // assert subC == fullSub[1..];
    //     b' := evalCodeSeqFn(subC,step);
    //     assert b[0] == step;
    //     if (|firstStep| == 1)
    //     {
    //         assert b[1] == b'[0];
    //         assert b == [step] + b';
    //         assert last(b) == last(b');
    //         assert b[1..] == b';
    //     }else{
    //         assert |firstStep| > 0;
    //         assert c[0].Block? || c[0].IfElse?;
    //         var test := evalCodeSeqFn(subC,last(firstStep));
    //         assert test == restB;
    //         if(c[0].Block?){
    //             assert |c[0].block| > 0;
    //             var fullSub := [Block(all_but_first(c[0].block))] + all_but_first(c);
    //             assert subC == fullSub[1..];
    //             assert |fullSub| <= |c|;
    //             var evalFullSub := evalCodeSeqFn(fullSub,step);
    //             var firstStep' := evalCodeFn(first(fullSub),step);
    //             var restB' := evalCodeSeqFn(all_but_first(fullSub),last(firstStep'));
    //             assert evalFullSub == firstStep' + restB';
    //             assert firstStep == evalCodeSeqFn(first(c).block,s);
    //             // assert firstStep == [step] + evalCodeSeqFn([Block(all_but_first(c[0].block))],step);
    //             // assert b[1] == b'[0];
    //         }
    //     }
    //     // forall i | i >= 0 && i < |b|
    //     // {
    //     //     b[i] == evalCodeFn(first,s);
    //     // }
    //     // assert b[1] == b'[0];
    //     // assert b == [s] + b';
    // }

    // lemma behaviorMinusFirstStateIsSubBehavior(s:state,b:behavior,c:seq<Code>)
    //     requires b ==  evalCodeSeqFn(c,s);
    //     requires |c| > 0;
    //     requires c[0].Block?;
    //     requires |c[0].block| > 0;
    // {
    //     var step := b[0];
    //     assert StateNext(s,step);
    //     var subCode := [Block(all_but_first(c[0].block))] + all_but_first(c);
    //     var b' := evalCodeSeqFn(subCode,step);
    //     // b
    //     var firstStep := evalCodeFn(first(c),s);
    //     var restB := evalCodeSeqFn(all_but_first(c),last(firstStep));
    //     assert b == firstStep + restB;
    //     assert step == firstStep[0];
    //     assert b[1..] == all_but_first(firstStep) + restB;
    //     //b'
    //     // assert |subCode| > 0;
    //     if(|subCode| == 0)
    //     {
    //         // assert
    //     }else{
    //         var firstStep' := evalCodeFn(first(subCode),step);
    //         assert |firstStep'| > 0;
    //         assert evalCodeFn(first(c),s) == evalCodeSeqFn(first(c).block,s);
    //         assert evalCodeSeqFn(first(c).block,s)[0] == step;
    //         // assert firstStep == [step] + evalCodeFn(first(subCode),step);

    //         var restB' := evalCodeSeqFn(all_but_first(subCode),last(firstStep'));
    //         assert b' == firstStep' + restB';
    //         // assert
    //         assert all_but_first(subCode) == all_but_first(c);
    //         // assert last(firstStep) == last(firstStep');
    //         // assert b == [step] + firstStep' + restB';
    //         // assert restB' == restB;
    //     }

    //     // assert b' == all_but_first(firstStep) + restB;
    //     // assert b == [step] + evalCodeSeqFn(all_but_first(c),step);
    //     // assert b[1..] == b';
    // }
//  function evalCodeSeqFnV2(block:seq<Code>, s:state) : (b:behavior)
//     ensures |b| > 0;
//     ensures StateNext(s,b[0]);
//     ensures ValidSimpleBehavior([s] + b);
//     ensures |block| == 0 ==> b == [s]
//     decreases block,0
//   {
//     reveal_ValidSimpleBehavior();
//     if |block| == 0 then
//         assert NextStep(s,s, Step.stutterStep());
//         assert StateNext(s,s);
//         assert ValidSimpleBehavior([s] + [s]);
//         // assert |stutter| == 1;
//         [s]
        
//         // b := stutter;
//         // remainder := [CNil];
//     else
//         var first := first(block);
//         // if first.Block? && |first.block| > 0 then
//         //     var first' := first.block[0];
//         //     var remainder := [Block(all_but_first(first.block))] + all_but_first(block);
            
//         //     assert NextStep(s,s, Step.stutterStep());
//         //     assert StateNext(s,s);
//         //     assert ValidSimpleBehavior([s] + [s]);
//         //     // assert |stutter| == 1;
//         //     [s]
//         // else
//             var remainder := all_but_first(block);

//             var firstStep := evalCodeFn(first,s);
        
//             assert StateNext(s,firstStep[0]);
//             var restB := evalCodeSeqFn(remainder,last(firstStep));

//             assert ValidSimpleBehavior([s] + firstStep);
//             subValidBIsValid(firstStep,s);
//             assert ValidSimpleBehavior(firstStep);
//             assert ValidSimpleBehavior([last(firstStep)] + restB);
//             subValidBIsValid(restB,last(firstStep));
//             assert ValidSimpleBehavior(restB);
//             var seqB := firstStep + restB;
//             validConcatIsValid(firstStep,restB);
//             assert ValidSimpleBehavior(seqB);
//             seqB
    
//   }

}
