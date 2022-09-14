include "./llvmREFACTOR_Multi.i.dfy"
include "../Libraries/Seqs.s.dfy"
include "../Libraries/Sets.i.dfy"


module behavior_lemmas 
{
    import opened LLVM_defRE_Multi
    import opened Collections__Sets_i
    import opened Collections__Seqs_s


    // type behavior = seq<state>
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

    lemma behaviorThatEvalsSameCodeWithSameInitHasEqualOut(s:state,c:codeRe,b:behavior)
        requires ValidState(s);
        requires ValidBehaviorNonTrivial(b);
        requires BehaviorEvalsCode(c,b);
        ensures forall b' :: (|b'| > 0 && BehaviorEvalsCode(c,b')  && b'[0] == b[0]) ==> behaviorOutput(b') == behaviorOutput(b);
     {  
         reveal_BehaviorEvalsCode();
         assert forall b' :: (|b'| > 0 && BehaviorEvalsCode(c,b')  && b'[0] == b[0]) ==> behaviorOutput(b') == behaviorOutput(b);
     }




     function  allBehaviorOutputSet(bSet:set<behavior>) : (allBOut:set<seq<output>>)
        // ensures |bOut| == |a|
        ensures SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
        // ensures (allBOut == allBehaviorOutputSet(bSet)) ==> SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures |bSet| > 0 ==> |allBOut| > 0
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
             var out := singleOutput + rest;
             subsetUnion(singleOutput,rest,behaviorOutput(behavior));
             allBehaviorsSetSurjective(bSet,out);
             out

    }

    predicate {:opaque} expandedAllBehaviorsSurjective(bSet:set<behavior>,allBOut:set<seq<output>>)
    {

        // |ys| > 0
        // var y :| y in ys
        // assert SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        // x :| x in xs && behaviorOutput(x) == y)

        (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y))
    }

    lemma allBehaviorsSetSurjective(bSet:set<behavior>,allBOut:set<seq<output>>)
        requires SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures expandedAllBehaviorsSurjective(bSet,allBOut);
        ensures (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y))
    {
         reveal_expandedAllBehaviorsSurjective();
         assert expandedAllBehaviorsSurjective(bSet,allBOut);
         assert  (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    }

    lemma allBehaviorEqualityIsSurjective(bSet:set<behavior>,allBOut:set<seq<output>>)
       requires allBOut == allBehaviorOutputSet(bSet);
       ensures SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
       ensures  SurjectiveOver(bSet,allBOut, x => behaviorOutput(x)) ==> (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));    
    {
        reveal_behaviorOutput();
        reveal_expandedAllBehaviorsSurjective();
        assert SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        assert SurjectiveOver(bSet,allBOut, x => behaviorOutput(x)) ==> (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    //    allBehaviorsSetSurjective(bSet,allBOut);
    //    assert (forall y :: y in allBOut ==> (exists x :: x in bSet && behaviorOutput(x) == y));
    }

    lemma subsetOfBehaviorImpliesSubsetOfOutput(superset:set<behavior>,subset:set<behavior>,f:behavior->bool)
        requires subset == MakeSubset(superset,f);
        ensures forall subsetElem :: subsetElem in allBehaviorOutputSet(subset) ==> subsetElem in allBehaviorOutputSet(superset);
    {
        assert forall subElem :: subElem in subset ==> subElem in superset;
        var superOut := allBehaviorOutputSet(superset);
        var subOut := allBehaviorOutputSet(subset);

        assert forall subsetElem :: subsetElem in subOut ==> subsetElem in superOut;
    }

    lemma subsetOfBehaviorImpliesSubsetOfOutputFull(superset:set<behavior>,subset:set<behavior>,superOut:set<seq<output>>,subOut:set<seq<output>>,f:behavior->bool)
        requires subset == MakeSubset(superset,f);
        requires superOut == allBehaviorOutputSet(superset);
        requires subOut == allBehaviorOutputSet(subset);

        ensures forall subsetElem :: subsetElem in subOut ==> subsetElem in superOut;
    {
        assert forall subElem :: subElem in subset ==> subElem in superset;
        assert forall subsetElem :: subsetElem in subOut ==> subsetElem in superOut;
    }

   
    lemma identicalBehaviorSetsHaveSameOutput(a:set<behavior>,b:set<behavior>)
        requires a == b
        ensures allBehaviorOutputSet(a) == allBehaviorOutputSet(b)
    {
    }


    predicate equalOutput(a:seq<output>,b:seq<output>)
        ensures equalOutput(a,b) ==> (a == b)
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


}

