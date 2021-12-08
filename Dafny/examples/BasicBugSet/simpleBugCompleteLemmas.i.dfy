include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"

module simpleBugCompleteLemmas{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i
    import opened behavior_lemmas

    lemma possibleVulnOutputs(s:state, preB:behavior) 
        requires ValidState(s);
        requires |preB| > 0;
        requires preB[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB)) 
                                  ==> (behaviorOutput(preB) == validOutput());
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB)) 
                                  ==> (behaviorOutput(preB) == invalidOutput());
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB)
            ensures (behaviorOutput(preB) == validOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB);
            var preBWitness := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),preBWitness);
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB)
            ensures (behaviorOutput(preB) == invalidOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB);
            var preBWitness := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),preBWitness);
        }
     
    }

    lemma possibleVulnOutputsWithMiniSpec(s:state, preB:behavior)
        requires ValidState(s);
        requires |preB| > 0;
        requires preB[0] == s;
        requires s.o.Nil?;
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB)) 
                                  ==> !MiniSpec(preB);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB)) 
                                  ==> MiniSpec(preB);
        ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),preB)) ==> 
                        (!MiniSpec(preB) <==> (behaviorOutput(preB) == validOutput()));
         ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),preB)) ==> 
                        (MiniSpec(preB) <==> (behaviorOutput(preB) == invalidOutput()));
    {
        // possibleVulnOutputs(s,b);
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB)
            ensures !MiniSpec(preB);
            ensures (behaviorOutput(preB) == validOutput());
            ensures !MiniSpec(preB) ==> (behaviorOutput(preB) == validOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),preB);
            var preBWitness := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),preBWitness);
            assert !MiniSpec(preB);
            assert (behaviorOutput(preB) == validOutput());
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB)
            ensures MiniSpec(preB);
            ensures !(behaviorOutput(preB) == validOutput());
            ensures MiniSpec(preB) <==> (behaviorOutput(preB) == invalidOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),preB);
            var preBWitness := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),preBWitness);
            assert MiniSpec(preB);
            assert (behaviorOutput(preB) == invalidOutput());
            assert !(behaviorOutput(preB) == validOutput());
        }
        // assert !MiniSpec(b) ==> (behaviorOutput(b) == validOutput());
    }


    lemma findModMsSet(s:state,vulnBehaviors:set<behavior>) returns (vulnBehaviorsModMs:set<behavior>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors);
        ensures vulnBehaviorsModMs == MakeSubset(vulnBehaviors, x => !MiniSpec(x));
        ensures forall p :: p in vulnBehaviorsModMs ==> !MiniSpec(p);
        ensures nonTrivialBehaviorPreconditionsVulnModMs(s,vulnBehaviorsModMs);
    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();
        var vulnBehaviorsMod := MakeSubset(vulnBehaviors, x => !MiniSpec(x));
        forall preB | preB in vulnBehaviorsMod
            ensures nonTrivialBehaviorPreconditionsVulnModMs(s,vulnBehaviorsMod);
        {
            assert preB in vulnBehaviors;
            assert (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(preB) && BehaviorEvalsCode(codeVuln(input),preB) && preB[0] == s);
        }
        vulnBehaviorsModMs := vulnBehaviorsMod;

    }

    lemma vulnModMsOutput(s:state,vulnModMs:set<behavior>,vulnModMsOut:set<seq<output>>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        requires forall preBModMs :: preBModMs in vulnModMs ==> !MiniSpec(preBModMs);
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        ensures forall preBModMs :: preBModMs in vulnModMsOut ==> equalOutput(preBModMs,validOutput());
    {
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();
        forall preBModMs | preBModMs in vulnModMs
            ensures (behaviorOutput(preBModMs) == validOutput());
        {
            possibleVulnOutputsWithMiniSpec(s,preBModMs);
            assert !MiniSpec(preBModMs);
            assert (behaviorOutput(preBModMs) == validOutput());
        }
        assert forall preBModMs :: preBModMs in vulnModMsOut ==> equalOutput(preBModMs,validOutput());
    }


    lemma patchIsCompleteEmptyVulnSet(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs| == 0
        requires |vulnModMsOut| == 0
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);

        ensures forall preBModMs :: preBModMs in vulnModMsOut  ==> preBModMs in patchOut
        {
            reveal_nonTrivialBehaviorPreconditionsVulnModMs();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            assert |vulnModMs| == 0;
            assert |vulnModMsOut| == 0;
            assert forall preBModMs :: preBModMs in vulnModMsOut  ==> preBModMs in patchOut;
            
        }

    lemma patchIsCompleteNonTrivial(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs|  > 0
        requires |patchBehaviors|  > 0
        requires ValidState(s);
        requires forall p :: p in vulnModMs ==> !MiniSpec(p);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);
        ensures forall preBModMs :: preBModMs in vulnModMsOut  ==> preBModMs in patchOut;
    {
        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();
        reveal_ValidBehavior();

        vulnModMsOutput(s,vulnModMs,vulnModMsOut);
        assert forall preBModMs :: preBModMs in vulnModMsOut ==> equalOutput(preBModMs,validOutput());

        forall postB | postB in patchBehaviors
            ensures equalOutput(behaviorOutput(postB),validOutput());
            ensures behaviorOutput(postB) in patchOut;
        {
            var input :| BehaviorEvalsCode(codePatch(input),postB) && |postB| > 0 && validInput(postB[0],input);
            var postBWitness := unwrapPatchBehaviors(s,input);
            assert equalOutput(behaviorOutput(postB),validOutput());
            assert behaviorOutput(postB) in patchOut;
        }

        var patchB :| patchB in patchBehaviors;
        var input :| BehaviorEvalsCode(codePatch(input),patchB) && |patchB| > 0 && validInput(patchB[0],input);
        var postBWitness := unwrapPatchBehaviors(s,input);
        assert equalOutput(behaviorOutput(patchB),validOutput());
        assert behaviorOutput(patchB) in patchOut;

        forall preBModMs | preBModMs in vulnModMsOut
            ensures preBModMs in patchOut;
        {
            assert equalOutput(preBModMs,validOutput());
            transitiveEquality(preBModMs,behaviorOutput(patchB),validOutput());
            assert preBModMs == behaviorOutput(patchB);
            equalOutputIsTransitiveSet(behaviorOutput(patchB),preBModMs,patchOut);
            assert preBModMs in patchOut;
        }
        assert forall preBModMs :: preBModMs in vulnModMsOut  ==> preBModMs in patchOut;
    }

    lemma patchBehaviorsInVulnModMSBehaviors(s:state,vulnModMs:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires vulnModMsOut == allBehaviorOutputSet(vulnModMs);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        requires |vulnModMs|  > 0
        requires |patchBehaviors|  > 0
        requires ValidState(s);
        requires forall preBModMs :: preBModMs in vulnModMs ==> !MiniSpec(preBModMs);
        requires nonTrivialBehaviorPreconditionsVulnModMs(s,vulnModMs);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);

        ensures forall postB :: postB in patchBehaviors ==> equalOutput(behaviorOutput(postB),validOutput());
        ensures forall postB :: postB in patchBehaviors ==> behaviorOutput(postB) in patchOut;
        ensures forall postB :: postB in patchBehaviors ==> behaviorOutput(postB) in vulnModMsOut;
    {

        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        reveal_nonTrivialBehaviorPreconditionsVulnModMs();

        vulnModMsOutput(s,vulnModMs,vulnModMsOut);
        assert forall b :: b in vulnModMsOut ==> equalOutput(b,validOutput());
        assert |vulnModMsOut| > 0;
        assert |patchBehaviors| > 0;
        assert |patchOut| > 0;
        var vulnMsBehaviorOut :| vulnMsBehaviorOut in vulnModMsOut;

        forall postB | postB in patchBehaviors
            ensures equalOutput(behaviorOutput(postB),validOutput());
            ensures behaviorOutput(postB) in patchOut;
            ensures behaviorOutput(postB) in vulnModMsOut;
        {
            var input :| BehaviorEvalsCode(codePatch(input),postB) && |postB| > 0 && validInput(postB[0],input);
            var b' := unwrapPatchBehaviors(s,input);
            assert equalOutput(behaviorOutput(postB),validOutput());
            assert behaviorOutput(postB) in patchOut;
            transitiveEquality(vulnMsBehaviorOut, behaviorOutput(postB),validOutput());
            equalOutputIsTransitiveSet(vulnMsBehaviorOut,behaviorOutput(postB),vulnModMsOut);
            assert behaviorOutput(postB) in vulnModMsOut;
        }

    }


}