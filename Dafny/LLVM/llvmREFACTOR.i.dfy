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


module LLVM_defRE {

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

    datatype output = Out(o:Data) | Nil

    type codeSeq = seq<codeRe>

    datatype codeRe =
    | Ins(ins:ins)
    | Block(block:codeSeq)
    | IfElse(ifCond:bool, ifTrue:codeSeq, ifFalse:codeSeq)
    | CNil
            
    type behavior = seq<state>
    predicate {:opaque} ValidBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1 && ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    predicate ValidBehaviorNonTrivial(b:behavior)
    {
        ValidBehavior(b) && |b| > 0
        
    }

  predicate {:opaque} BehaviorEvalsCode(c:codeRe,b:behavior)
    {
        |b| >= 2 && b == [b[0]] + evalCodeRE(c,b[0])
    }

    lemma behaviorThatEvalsSameCodeWithSameInitIsEqual(s:state,c:codeRe,b:behavior)
        requires ValidState(s);
        requires ValidBehaviorNonTrivial(b);
        requires BehaviorEvalsCode(c,b);
        ensures forall b' :: (|b'| > 0 && BehaviorEvalsCode(c,b')  && b'[0] == b[0]) ==> b' == b;
     {  
         reveal_BehaviorEvalsCode();
         assert forall b' :: (|b'| > 0 && BehaviorEvalsCode(c,b')  && b'[0] == b[0]) ==> b' == b;
     }



    function {:opaque} behaviorOutput(b:behavior) : (bOut:seq<output>)
        ensures |bOut| == |b| 
        ensures forall i :: (i >= 0 && i < |b|) ==> bOut[i] == b[i].o
        decreases |b|
    {
        if |b| == 0 then
            []
        else 
            [b[0].o] + behaviorOutput(all_but_first(b))
    }

    predicate {:opaque} expandedAllBehaviorsSurjective(bSet:set<behavior>,allBOut:set<seq<output>>)
    {
        (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y))
    }

    lemma allBehaviorsSetSurjective(bSet:set<behavior>,allBOut:set<seq<output>>)
        requires SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures expandedAllBehaviorsSurjective(bSet,allBOut);
        ensures (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y))
    {
        //  reveal_SurjectiveOver();
         reveal_expandedAllBehaviorsSurjective();
         assert expandedAllBehaviorsSurjective(bSet,allBOut);
         assert  (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    }

    lemma allBehaviorEqualityIsInjective(bSet:set<behavior>,allBOut:set<seq<output>>)
       requires allBOut == allBehaviorOutputSet(bSet);
       ensures SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
       ensures  SurjectiveOver(bSet,allBOut, x => behaviorOutput(x)) ==> (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
        // ensures (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    
    {
       reveal_behaviorOutput();
        reveal_expandedAllBehaviorsSurjective();
       assert SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
       assert SurjectiveOver(bSet,allBOut, x => behaviorOutput(x)) ==> (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    //    allBehaviorsSetSurjective(bSet,allBOut);
    // //    assert (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    // //    assert false;
    }

    lemma subsetOfBehaviorImpliesSubsetOfOutput(superset:set<behavior>,subset:set<behavior>,f:behavior->bool)
        requires subset == MakeSubset(superset,f);
        ensures forall x :: x in allBehaviorOutputSet(subset) ==> x in allBehaviorOutputSet(superset);
    {
        assert forall elem :: elem in subset ==> elem in superset;
        var superOut := allBehaviorOutputSet(superset);
        var subOut := allBehaviorOutputSet(subset);

        assert forall x :: x in subOut ==> x in superOut;
    }

    lemma subsetOfBehaviorImpliesSubsetOfOutputFull(superset:set<behavior>,subset:set<behavior>,superOut:set<seq<output>>,subOut:set<seq<output>>,f:behavior->bool)
        requires subset == MakeSubset(superset,f);
        requires superOut == allBehaviorOutputSet(superset);
        requires subOut == allBehaviorOutputSet(subset);

        ensures forall x :: x in subOut ==> x in superOut;
    {
        assert forall elem :: elem in subset ==> elem in superset;
        assert forall x :: x in subOut ==> x in superOut;
    }

    function  allBehaviorOutputSet(bSet:set<behavior>) : (allBOut:set<seq<output>>)
        // ensures |bOut| == |a|
        ensures SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
        ensures (allBOut == allBehaviorOutputSet(bSet)) ==> SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures |bSet| > 0 ==> |allBOut| > 0
                // ensures forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y);
        // ensures forall p :: behaviorOutput(p) in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y);
        // ensures allBOut == MakeSubset(bSet, x => exists y :: y in bSet && x == behaviorOutput(y));
        // ensures forall x :: !(exists b :: b in bSet && behaviorOutput(b) == behaviorOutput(x)) ==> !(behaviorOutput(x) in allBOut);
        // ensures forall a,b :: a == b ==> allBehaviorOutputSet(a) == allBehaviorOutputSet(b);

        // ensures forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b))
        // ensures forall x :: !(exists b :: b in bSet && behaviorOutput(x) == behaviorOutput(b)) ==> !(behaviorOutput(x) in allBOut);

        ensures |bSet| == 0 ==> |allBOut| == 0;
        decreases |bSet|
    {
        // reveal_SurjectiveOver();
        reveal_behaviorOutput();
        if |bSet| == 0 then
            var out := {};
            assert forall b :: behaviorOutput(b) in out ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
                         allBehaviorsSetSurjective(bSet,out);

            out
        else   
             var behavior :| behavior in bSet;
             var bSubset := bSet - {behavior};
             var singleOutput := {behaviorOutput(behavior)};
             var rest := allBehaviorOutputSet(bSubset);
            //  assert forall b :: behaviorOutput(b) in rest ==> (exists elem :: elem in bSubset && behaviorOutput(elem) == behaviorOutput(b));
             var out := singleOutput + rest;
             subsetUnion(singleOutput,rest,behaviorOutput(behavior));
             assert behaviorOutput(behavior) in out;
             assert forall b :: b in rest ==> b in out;
             assert forall b :: b in bSubset ==> b in bSet;
             assert out == {behaviorOutput(behavior)} + allBehaviorOutputSet(bSubset);
            //  assert forall b :: behaviorOutput(b) in out ==> (behaviorOutput(behavior) == behaviorOutput(b) 
                                                            // || exists elem :: elem in bSubset && behaviorOutput(elem) == behaviorOutput(b));
       
            //  assert exists b :: b in bSet && behaviorOutput() == behaviorOutput(behavior)
             assert behavior in bSet && behaviorOutput(behavior) == behaviorOutput(behavior);
             allBehaviorsSetSurjective(bSet,out);
             out

    }

    lemma identicalBehaviorSetsHaveSameOutput(a:set<behavior>,b:set<behavior>)
        requires a == b
        ensures allBehaviorOutputSet(a) == allBehaviorOutputSet(b)
    {
    }

    lemma setsWithIdenticalOutputsHaveSameOutput(a:set<behavior>,b:set<behavior>)
        // requires forall elem :: elem in a ==> 
    {

    }
    // lemma identicalOutputSetsAreEqual(bSet:set<behavior>,allBOut:set<seq<output>>,equalOut:set<seq<output>>)
    //     requires allBOut == allBehaviorOutputSet(bSet);
    //     requires forall x :: x in bSet ==> behaviorOutput(x) in allBOut;
    //     requires forall x :: x in bSet ==> behaviorOutput(x) in equalOut;
    // {
    //     if (|bSet| == 0)
    //     {
    //         assert |allBOut| == 0;
    //     //     assert allBOut == equalOut;
    //     }
    //     // var test:set<seq<output>> := MapSetToSetOver(bSet, x => exists y :: y in bSet && equalOutput(x,behaviorOutput(y)));
    //     // assert allBOut == equalOut;
    // }

    // lemma reducedAllOutputSetLessThanOrEqual(bSet:set<behavior>,bSetReduced:set<behavior>,b:behavior)
    //     requires |bSet| == |bSetReduced| + 1;
    //     requires forall reducedB :: reducedB in bSetReduced ==> reducedB in bSet
    //     requires b in bSet
    //     requires !(b in bSetReduced)
    // {
    //     var allOut := allBehaviorOutputSet(bSet);
    //     var reducedOut := allBehaviorOutputSet(bSetReduced);
    //     assert behaviorOutput(b) in allOut;
    //     assert (exists y :: y in bSetReduced && behaviorOutput(b) == behaviorOutput(y) && b != y) ==> behaviorOutput(b) in reducedOut;
    //     // assert (forall other :: (other in bSetReduced && other != b) ==> behaviorOutput(other) != behaviorOutput(b)) ==> !(behaviorOutput(b) in reducedOut);


    //     var test := MakeSubset(allOut, x => exists y :: y in bSetReduced && x == behaviorOutput(y));
    //     // assert reducedOut <= allOut;
    //     assert forall rOut :: rOut in test ==> rOut in allOut;
    //     assert test <= allOut;
    //     assert forall x :: x in bSetReduced ==> behaviorOutput(x) in reducedOut;
    //     assert forall x :: x in bSetReduced ==> behaviorOutput(x) in test;

    //     assert (forall x :: x in bSetReduced && (exists y :: y in bSet && behaviorOutput(x) == behaviorOutput(y))) ==>  allOut == reducedOut;
    //     assert (forall x :: x in bSetReduced ==> behaviorOutput(x) != behaviorOutput(b)) ==> |reducedOut| <= |allOut|;    
    //     // assert                 
    //     // assert (reducedOut == allOut) ==> (exists otherB :: otherB in bSetReduced && behaviorOutput(b) == behaviorOutput(otherB));

    //     // assert (allOut == reducedOut) ==> 
    //     // assert (forall p :: p in bSet ==> (exists rp :: rp in bSetReduced && behaviorOutput(p) == behaviorOutput(rp))) ==> allOut == reducedOut;
    //     // assert forall x :: x in MakeSubset(xs, f) <==> x in xs && f(x)
    //     // assert test ==  reducedOut;
    //     // assert (exists y :: y in bSetReduced && behaviorOutput(b) == behaviorOutput(y) && b != y) ==> allOut == reducedOut;
    // }

    // lemma allBOutputSetLemma(bSet:set<behavior>,allBOut:set<seq<output>>)
    //     requires allBOut == allBehaviorOutputSet(bSet)
    //     // ensures forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    // {
        
    //     if (|bSet| == 0){
    //         assert forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    //     }else{
    //         if (|bSet| == 1)
    //         {
    //             assert forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
    //             var x :| x in bSet;
    //             assert bSet - {x} == {};
    //             assert behaviorOutput(x) in allBOut;
    //             assert forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    //         }else{
    //             assert |bSet| > 1;
    //             var x :| x in bSet;
    //             var reducedBSet := bSet - {x};
    //             assert  |reducedBSet| >= 1;
    //             assert |reducedBSet| < |bSet|;
    //             assert forall elems :: elems in reducedBSet ==> elems in bSet;
    //             assert behaviorOutput(x) in allBOut;
    //             // var test := MakeSubset(allBOut, val =>  behaviorOutput(x) != val);
    //             var reducedTotalB := allBehaviorOutputSet(reducedBSet);
    //             // assert (reducedTotalB == allBOut) ==> (exists otherB :: otherB in reducedBSet && behaviorOutput(x) == behaviorOutput(otherB));
    //             assert (exists y :: y in bSet && behaviorOutput(x) == behaviorOutput(y) && x != y) ==> behaviorOutput(x) in reducedTotalB;
    //             // assert !(exists y :: y in bSet && behaviorOutput(x) == behaviorOutput(y) && x != y) ==> |reducedTotalB| < |allBOut|;
    //             // assert forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    //             // assert |reducedTotalB| <= |allBOut|;
    //             assert behaviorOutput(x) in allBOut;
    //             var xBehavior :| xBehavior == behaviorOutput(x) && behaviorOutput(x) in allBOut;
    //             allBOutputSetLemma(reducedBSet,reducedTotalB);
    //         }
    //     }
        
    // }
    // lemma allBOutputSetLemmaV2(bSet:set<behavior>,allBOut:set<seq<output>>)
    //     requires allBOut == allBehaviorOutputSet(bSet)
    //     // requires forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
    //     // ensures forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    // {
        
    //     if (|bSet| == 0){
    //         assert forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    //     }else{
    //         if (|bSet| == 1)
    //         {
    //             assert forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
    //             var x :| x in bSet;
    //             assert bSet - {x} == {};
    //             assert behaviorOutput(x) in allBOut;
    //             assert forall b :: behaviorOutput(b) in allBOut ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
    //         }else{
    //             assert |bSet| > 1;
    //             var pick :| pick in bSet;
    //             var suspects:set<behavior> := (set x | x in bSet && behaviorOutput(x) == behaviorOutput(pick));
    //             assert pick in suspects;
    //             assert |suspects| >= 1;
    //             var reducedBSet := bSet - suspects;
    //             var reducedTotalB := allBehaviorOutputSet(reducedBSet);
    //             var removedOut := allBOut - {behaviorOutput(pick)};
    //             // assert forall x :: x in suspects ==> !(exists b :: b in reducedTotalB && behaviorOutput(x) == b);
    //             assert forall b :: b in reducedBSet ==> behaviorOutput(b) in removedOut;
    //             // assert reducedTotalB == removedOut;
    //             //  allBOutputSetLemma(reducedBSet,removedOut);
    //             // assert reducedTotalB == (allBOut - {behaviorOutput(pick)});
    //         }
    //     }
        
    // }

    // lemma reducedEquality(bSet:set<behavior>,allBOut:set<seq<output>>)
    //     requires allBOut == allBehaviorOutputSet(bSet)


    function allBehaviorOutput(a:seq<behavior>) : (bOut:seq<seq<output>>)
        ensures |bOut| == |a|
        ensures forall a' :: a' in a ==> behaviorOutput(a') in bOut;
        ensures forall i :: (i >= 0 && i < |a|) ==> bOut[i] == behaviorOutput(a[i])
        ensures |a| == 0 ==> |bOut| == 0;
       
        decreases |a|
    {
        if |a| == 0 then
            var out := [];
            assert forall a' :: behaviorOutput(a') in out ==> a' in a;
            out
        else   
         
            var out := [behaviorOutput(a[0])] + allBehaviorOutput(all_but_first(a));
            
            out
            //{behaviorOutput(x)} + allBehaviors(a')
    }

    predicate equalOutput(a:seq<output>,b:seq<output>)
        // ensures equalOutput(a,b) ==> a == b
    {
        && |a| == |b|
        && forall i :: (i >=0 && i < |a|) ==> a[i] == b[i]
    }


    lemma equalOutputLemma(a:seq<output>,b:seq<output>)
        requires equalOutput(a,b)
        ensures a == b
    {
        assert a == b;
    }

    lemma outputIsEqual(a:seq<output>,b:seq<output>)
        requires a == b
        ensures equalOutput(a,b)
    {
        assert equalOutput(a,b);
    }

    lemma transitiveEquality(a:seq<output>,b:seq<output>,c:seq<output>)
        requires equalOutput(a,c);
        requires equalOutput(b,c);
        ensures equalOutput(a,b);
        ensures a == b
    {
        assert equalOutput(a,b);
        equalOutputLemma(a,b);
    }

    lemma equalOutputIsTransitive(a:seq<output>,b:seq<output>,all:seq<seq<output>>)
        requires a == b;
        requires a in all;
        ensures b in all;
    {
        assert b in all;
    }

lemma equalOutputIsTransitiveSet(a:seq<output>,b:seq<output>,all:set<seq<output>>)
        requires a == b;
        requires a in all;
        ensures b in all;
    {
        assert b in all;
    }



    // lemma behaviorOutputAll(a:set<behavior>,bOut:seq<seq<output>>)
    //     requires bOut == allBehaviorOutput(a)
    //     // ensures forall b :: b in bOut ==> exists a' :: a' in a && behaviorOutput(a') == b
    // {
    //     assert |bOut| == |a|;
    //     assert forall a' :: a' in a ==> behaviorOutput(a') in bOut;
    //     assert forall b :: b in bOut ==> exists a' :: a' in a && behaviorOutput(a') == b;
    // }

///

    function  evalCodeRE(c:codeRe, s:state) : (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures c.Block? ==> |b| == |evalBlockRE(c.block, s)|
        ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlockRE(c.ifTrue,s)| else |b| == |evalBlockRE(c.ifFalse,s)|
        ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)
        
        decreases c, 0
    {
        reveal_ValidBehavior();
        match c
            case Ins(ins) => [evalInsRe(ins,s)]
            case Block(block) => evalBlockRE(block, s) 
            case IfElse(ifCond, ifT, ifF) => if ifCond then evalBlockRE(ifT, s) else evalBlockRE(ifF,s)
            case CNil => [s]
    }

//   function evalBlockRE(block:codeSeq, s:state): (b:behavior)
//         ensures |b| > 0
//         ensures (|block| == 0 || first(block).CNil?) ==> |b| == 1

//     {
//         if |block| == 0 || first(block).CNil? then
//             [s]
//         else
//             var metaBehavior := evalCodeRE(first(block),s);
//             var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
//             var fullBlock := metaBehavior + theRest;
//             assert |metaBehavior| == |evalCodeRE(first(block),s)|;
//             assert |theRest| == |evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)))|;
//             assert |fullBlock| == |metaBehavior| + |theRest|;

//             fullBlock
//     }
  function evalBlockRE(block:codeSeq, s:state): (b:behavior)
        ensures |b| > 0
        // ensures (first(block).CNil?) ==> |b| == 1

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
                    s'
                else
                    var s' := s.(lvs := s.lvs[dst.l := d],o := Nil);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    s'
             else
                var s' := s.(gvs := s.gvs[dst.g := d],o := Nil);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    s'
         }

    function evalInsRe(ins:ins,s:state) : (s':state)
        // requires ValidInstruction(s, ins)
        // ensures ValidState(s) && ValidInstruction(s, ins) ==> StateNext(s,s')
        ensures s'.ok ==> NextStep(s,s',Step.evalInsStep(ins)) && StateNext(s,s');

    {
        if (!ValidState(s) || !ValidInstruction(s, ins)) then 
            var notOK := s.(ok := false);
            notOK
        else match ins
            case ADD(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalADD(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    // assert NextStep(s,s', Step.evalInsStep(ins));
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
                    // assert NextStep(s,s', Step.evalInsStep(ins));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case ICMP(dst,cond,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
            case RET(val) => 
                var s' := s.(o := Out(OperandContents(s,val)));
                assert ValidState(s');
                assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                assert validEvalIns(ins,s,s');
                s'
                //s
    }
    
////

    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    
  
 datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | ICMP(dst:operand,cond:condition,size:nat,src1:operand,src2:operand)
    // | BR(if_cond:operand, labelTrue:codeRe,labelFalse:codeRe)
    | RET(val:operand)


    datatype behaviors = preBehavior(preB:behavior) | postBehavior(postB:behavior)

    function getBehavior(b:behaviors) : behavior
    {
        match b
            case preBehavior(preB) => preB
            case postBehavior(postB) => postB
    }

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
            case ICMP(dst,cond,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && t == OperandContents(s,src1).itype.size
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
            case RET(val) => && ValidOperand(s,val)
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
            case ICMP(dst,cond,t,src1,src2) => ValidState(s') 
                                && ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case RET(val) => ValidState(s') && s'.m == s.m && s'.o == Out(OperandContents(s,val))     
    
    }

    // Control flow 
        lemma unwrapBlockWitness(b:behavior,block:codeSeq,s:state) 
            returns (step:behavior,remainder:codeSeq,subBehavior:behavior)
            requires b == [s] + evalBlockRE(block,s);
            // requires ValidState(s);
            ensures |step| > 0
            ensures (|block| > 0 && !first(block).CNil?) ==> (b == [s] + step + evalCodeRE(Block(remainder),last(step)));
            ensures (|block| > 0 && !first(block).CNil?) ==> subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
            ensures (|block| > 0 && !first(block).CNil?) ==> |remainder| == |block|-1
            ensures (|block| > 0 && !first(block).CNil?) ==> remainder == all_but_first(block);
            ensures |block| == 1 ==> |remainder| == 0;
            ensures (|block| > 0 && !first(block).CNil? && remainder == []) ==>  subBehavior == [last(step),last(step)];
            ensures (|block| > 0 && first(block).Ins?) ==> |step| == 1 
            ensures (|block| > 0 && first(block).Ins?) ==> step[0] == evalInsRe(first(block).ins,s)
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
                var metaBehavior := evalCodeRE(first(block),s);
                assert (first(block).Ins? && ValidInstruction(s,first(block).ins)) ==> ValidBehavior([s] + metaBehavior);
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
                assert b == [s] + b[1..|step|] + b[|step|..];
                assert b == [s] + step + all_but_first(subBehavior);
            }
        }




    // ghost method testUpdateLV(s:state, o:operand, d:Data) returns (s':state)
    //     requires o.LV? 
    //     ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
    //     ensures forall lv :: (lv in s.lvs && lv != o.l) ==> s'.lvs[lv] == s.lvs[lv]; 
    //     // modifies o,d
    // {
    //     s' := s;
    //     if o.l in s.lvs {
    //         s' := s.(lvs := s.lvs[o.l := d]);
    //         assert forall lv :: (lv in s'.lvs && lv != o.l) ==> s'.lvs[lv] == s.lvs[lv];
    //         assert |s.lvs| ==  |s'.lvs|;
    //     }else{
    //         s' := s.(lvs := s.lvs[o.l := d]);
    //         assert |s.lvs| ==  |s'.lvs| - 1;
    //     }
    //     return s';
        
    // }

    // lemma a(s:state, o:operand)
    //      requires o.LV? 
    //      requires o.l in s.lvs
         
    // {
    //     var a := testUpdateLV(s,o,Int(16,IntType(4,false)));
    // }

    // function stateUpdateVar(s:state, dst:operand, d:Data): (s':state)
    //     //  requires dst.LV? || dst.GV?
    //      requires MemValid(s.m) 
    //      requires ValidData(s,d)
    //      ensures MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //      ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
    //      ensures forall gv :: gv in s.gvs ==> gv in s'.gvs
    //      ensures dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
    //      ensures dst.GV? ==> forall gv :: (gv in s.gvs && gv != dst.g) ==> s'.gvs[gv] == s.gvs[gv]; 
    //      ensures ValidOperand(s',dst)

    //      {
    //          if dst.GV? then
    //             var s' := s.(gvs := s.gvs[dst.g := d]);
    //                 assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                 s'
    //          else 
    //             if dst.LV? then
    //                 if (dst.l in s.lvs) then
    //                     var s' := s.(lvs := s.lvs[dst.l := d]);
    //                     assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                     s'
    //                 else
    //                     var s' := s.(lvs := s.lvs[dst.l := d]);
    //                     assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                     s'
    //             else
    //                 assert dst.D?;
    //                 var s' := s;
    //                 assert ValidData(s',dst.d);
    //                 s'
    //      }

        // function evalBlockRE(block:codesRe, s:state): (b:behavior)
    //     ensures |b| > 0
    // {
    //     if block.CNil? || block.ForeignFunction? || (block.lvm_CodesRe? && |block.codeSeq| == 0) then
    //         [s]
    //     else
    //         var metaBehavior := evalCodeRE(first(block.codeSeq),s);
    //         assert |all_but_first(block.codeSeq)| < |block.codeSeq|;
    //         var theRest := evalCodeRE(Block(lvm_CodesRe(all_but_first(block.codeSeq))),last(metaBehavior));
    //         metaBehavior + theRest
    //         // evalBlockRE(lvm_CodesRe(all_but_first(block.codeSeq)),evalCodeRE(block.codeSeq[0],last(subBehavior)))
    //         // evalCodeRE(block.codeSeq[0],last(subBehavior)) + evalBlockRE(all_but_first(block.codeSeq))
    //         // exists r :: (evalCode(block.hd, s, r) && evalBlock(block.tl, r, s'))
    // }

    // predicate evalIfElseRE(cond:bool, ifT:codes, ifF:codes, s:state, s':state)
    //     decreases if ValidState(s) && cond then ifT else ifF
    // {
    //     if ValidState(s) && s.ok then
    //         exists r :: branchRelation(s, r, cond) && (if cond then evalBlock(ifT, r, s') else evalBlock(ifF, r, s'))
    //     else
    //         !s'.ok
    // }
    


}
