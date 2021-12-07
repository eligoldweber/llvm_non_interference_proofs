include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"

module simpleBugCompleteLemmasV2{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i

lemma possibleVulnOutputs(s:state, b:behavior) 
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
     
    }

    lemma possibleVulnOutputsWithMiniSpec(s:state, b:behavior)
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> !MiniSpec(b);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> MiniSpec(b);
        ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b)) ==> 
                        (!MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
         ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b)) ==> 
                        (MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]));
    {
        // possibleVulnOutputs(s,b);
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures !MiniSpec(b);
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures !MiniSpec(b) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
            assert !MiniSpec(b);
            assert (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures MiniSpec(b);
            ensures !(behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
            assert MiniSpec(b);
            assert (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
            assert !(behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        }
        // assert !MiniSpec(b) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    }


lemma findModMsSet(s:state,vulnBehaviors:set<behavior>) returns (vulnBehaviorsModMs:set<behavior>)
    requires ValidState(s);
    requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors);
    ensures vulnBehaviorsModMs == MakeSubset(vulnBehaviors, x => !MiniSpec(x));
    ensures forall p :: p in vulnBehaviorsModMs ==> !MiniSpec(p);
    ensures nonTrivialBehaviorPreconditionsVulnModMs(s,vulnBehaviorsModMs);
    // ensures (forall b :: b in vulnBehaviorsModMs ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));
{
    reveal_nonTrivialBehaviorPreconditionsVuln();
    reveal_nonTrivialBehaviorPreconditionsVulnModMs();
    var subset := MakeSubset(vulnBehaviors, x => !MiniSpec(x));
    forall v | v in subset
        ensures (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(v) && BehaviorEvalsCode(codeVuln(input),v) && v[0] == s);
    {
        assert v in vulnBehaviors;
        assert (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(v) && BehaviorEvalsCode(codeVuln(input),v) && v[0] == s);
    }
    vulnBehaviorsModMs := subset;

}

lemma vulnModMsOutput(s:state,vulnModMs:set<behavior>,vulnModMsOut:set<seq<output>>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        //requires (forall b :: b in vulnModMs ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));
        requires forall p :: p in vulnModMs ==> !MiniSpec(p);
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        ensures forall b :: b in vulnModMsOut ==> equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    {
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();
        forall p | p in vulnModMs
            ensures (behaviorOutput(p) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            possibleVulnOutputsWithMiniSpec(s,p);
            assert !MiniSpec(p);
            assert (behaviorOutput(p) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        }
        assert forall b :: b in vulnModMsOut ==> equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    }


    lemma patchIsCompleteEmptyVulnSet(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs| == 0
        requires |vulnModMsOut| == 0
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        // requires forall b :: b in vulnModMs ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);

        ensures forall p :: p in vulnModMsOut  ==> p in patchOut
        {
            reveal_nonTrivialBehaviorPreconditionsVulnModMs();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            assert |vulnModMs| == 0;
            assert |vulnModMsOut| == 0;
            assert forall p :: p in vulnModMsOut  ==> p in patchOut;
            
        }

    lemma patchIsCompleteNonTrivial(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs|  > 0
        requires |patchBehaviors|  > 0
        requires ValidState(s);
        requires forall p :: p in vulnModMs ==> !MiniSpec(p);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        // requires forall b :: b in vulnModMs ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);
        ensures forall p :: p in vulnModMsOut  ==> p in patchOut;
    {
        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();

                // reveal_evalCodeRE();
                reveal_ValidBehavior();

        vulnModMsOutput(s,vulnModMs,vulnModMsOut);
        assert forall b :: b in vulnModMsOut ==> equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

        forall p | p in patchBehaviors
            ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures behaviorOutput(p) in patchOut;
        {
            var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
            var b' := unwrapPatchBehaviors(s,input);
            assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            assert behaviorOutput(p) in patchOut;
        }

        var patchB :| patchB in patchBehaviors;
        var input :| BehaviorEvalsCode(codePatch(input),patchB) && |patchB| > 0 && validInput(patchB[0],input);
        var b' := unwrapPatchBehaviors(s,input);
        assert equalOutput(behaviorOutput(patchB),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        assert behaviorOutput(patchB) in patchOut;

        forall p | p in vulnModMsOut
            ensures p in patchOut;
        {
            assert equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            transitiveEquality(p,behaviorOutput(patchB),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            assert p == behaviorOutput(patchB);
            equalOutputIsTransitiveSet(behaviorOutput(patchB),p,patchOut);
            assert p in patchOut;
        }
        assert forall p :: p in vulnModMsOut  ==> p in patchOut;
    }



lemma patchBehaviorsInVulnModMSBehaviors(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs|  > 0
        requires |patchBehaviors|  > 0
        requires ValidState(s);
        requires forall p :: p in vulnModMs ==> !MiniSpec(p);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);
        // ensures forall p :: p in patchOut  ==> p in vulnModMsOut;
        ensures forall p :: p in patchBehaviors ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures forall p :: p in patchBehaviors ==> behaviorOutput(p) in patchOut;
        ensures forall p :: p in patchBehaviors ==> behaviorOutput(p) in vulnModMsOut;
    {

        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();

        vulnModMsOutput(s,vulnModMs,vulnModMsOut);
        assert forall b :: b in vulnModMsOut ==> equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        assert |vulnModMsOut| > 0;
        assert |patchBehaviors| > 0;
        assert |patchOut| > 0;
        var vulnMsBehaviorOut :| vulnMsBehaviorOut in vulnModMsOut;

        forall p | p in patchBehaviors
            ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures behaviorOutput(p) in patchOut;
            ensures behaviorOutput(p) in vulnModMsOut;
        {
            var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
            var b' := unwrapPatchBehaviors(s,input);
            assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            assert behaviorOutput(p) in patchOut;
            transitiveEquality(vulnMsBehaviorOut, behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            equalOutputIsTransitiveSet(vulnMsBehaviorOut,behaviorOutput(p),vulnModMsOut);
            assert behaviorOutput(p) in vulnModMsOut;
        }
        // assert forall p :: p in patchBehaviors ==> behaviorOutput(p) in vulnModMsOut;
        // allBehaviorEqualityIsInjective(patchBehaviors,patchOut); 
        // allBehaviorsSetSurjective(patchBehaviors,patchOut);
        // assert (forall y :: y in patchOut ==> (exists x :: x in patchBehaviors && behaviorOutput(x) == y));
        // assert SurjectiveOver(patchBehaviors,patchOut, x => behaviorOutput(x));
        // assert SurjectiveOver(patchBehaviors,patchOut, x => behaviorOutput(x)) ==> (forall y :: y in patchOut ==> (exists x :: x in patchBehaviors && behaviorOutput(x) == y));

        // assert forall y :: y in test ==> (exists x :: x in patchBehaviors && behaviorOutput(x) == y);
        // assert expandedAllBehaviorsSurjective(patchBehaviors,patchOut);// ==> (forall y :: y in patchOut ==> (exists x :: x in patchBehaviors && behaviorOutput(x) == y));
        // assert  forall y :: y in patchOut ==> (exists x :: x in patchBehaviors && behaviorOutput(x) == y);
        // forall pOut | behaviorOutput(pOut) in patchOut
        // {
        //     assert SurjectiveOver(patchBehaviors,patchOut, x => behaviorOutput(x));
        //     // assert (exists p :: p in patchBehaviors && behaviorOutput(p) ==  behaviorOutput(pOut));
        //     // assert equalOutput(behaviorOutput(pOut),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        // }
            //    assert  forall p :: p in patchOut  ==> p in vulnModMsOut;

    }

// lemma fullPatch(a:set<behavior>,b:set<behavior>)
//     requires benignPatch(a,b);
//     requires successfulPatch(b);
//     requires completePatch(a,b);
//     ensures safePatch(a,b);

    // lemma patchIsCompleteNonTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
    //     requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    //     requires |vulnBehaviors| > 0
    //     requires ValidState(s);
                    
    //     requires |patchBehaviors| > 0;

    //     requires vulnOut == allBehaviorOutputSet(vulnBehaviors);
    //     requires patchOut ==  allBehaviorOutputSet(patchBehaviors);

    //     ensures forall p :: p in vulnBehaviors && !MiniSpec(p) ==> (behaviorOutput(p) in vulnOut && behaviorOutput(p) in patchOut);
    //     // ensures forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut
    //     // ensures forall p :: p in (reducedVulnModMS(s,vulnBehaviors,patchBehaviors,vulnOut)) ==> p in patchOut;
    //     {
    //         reveal_BehaviorEvalsCode();
            
    //         reveal_nonTrivialBehaviorPreconditionsVuln();
    //         reveal_nonTrivialBehaviorPreconditionsPatch();
            
            
    //         forall p | (p in vulnBehaviors && !MiniSpec(p))
    //             ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             ensures behaviorOutput(p) in vulnOut;
    //             ensures behaviorOutput(p) in patchOut;
    //         {
    //             var input :| BehaviorEvalsCode(codeVuln(input),p) && |p| > 0 && validInput(p[0],input);
    //             var b' := unwrapVulnBehaviors(s,input);
    //             possibleVulnOutputsWithMiniSpec(s,p);
    //             assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             assert behaviorOutput(p) in vulnOut;

    //             var singlePatchBehavior :| singlePatchBehavior in patchBehaviors;
    //             var patchInput :| BehaviorEvalsCode(codePatch(patchInput),singlePatchBehavior) && |singlePatchBehavior| > 0 && validInput(singlePatchBehavior[0],patchInput);
    //             var patch' := unwrapPatchBehaviors(s,patchInput);
    //             outputIsEqual(behaviorOutput(patch'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             assert equalOutput(behaviorOutput(patch'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             assert behaviorOutput(patch') in patchOut;
    //             transitiveEquality(behaviorOutput(patch'),behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             equalOutputIsTransitiveSet(behaviorOutput(patch'),behaviorOutput(p),patchOut);

    //         }
    //          forall p | p in patchBehaviors
    //             ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             ensures behaviorOutput(p) in patchOut;
    //          {
    //             var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
    //             var b' := unwrapPatchBehaviors(s,input);
    //             assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    //             assert behaviorOutput(p) in patchOut;

    //          }

    //     }

            // assert (forall b :: behaviorOutput(b) in vulnOut <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));





}