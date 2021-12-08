include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Sets.i.dfy"

module simpleBugBenignLemmas{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Sets_i

    lemma possibleVulnOutputs(s:state, b:behavior) 
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && ValidBehaviorNonTrivial(b) &&BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == validOutput());
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == invalidOutput());
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);

        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == validOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == invalidOutput());
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
     
    }
lemma existsVulnBehavor(s:state,b:behavior,vulnBehaviors:set<behavior>,input:operand)
        requires ValidState(s);
        requires validVulnBehavior(b)
        requires |b| > 0;
        requires |vulnBehaviors| > 0; 
        requires b[0] == s;
        requires BehaviorEvalsCode(codeVuln(input),b) && |b| > 0 && validInput(b[0],input);
        requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors);
        ensures exists vuln, vulnIn :: vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);

    {
        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        validInputVulnImpliesBehavior(s);
        var b' := unwrapVulnBehaviors(s,input);
        assert exists vuln, vulnIn :: vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);
    }

    lemma vulnBehaviorIncludesPatchedBehavior(s:state,b:behavior,vulnBehaviors:set<behavior>)
        requires ValidState(s);
        requires validPatchBehavior(b)
        requires |vulnBehaviors| > 0; 
        requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors);
        ensures exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), validOutput()));

    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_BehaviorEvalsCode();
        validInputVulnImpliesBehavior(s);
        assert nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors);
        var vulnB :| vulnB in vulnBehaviors;
        var input :| validInput(s,input) &&  ValidBehaviorNonTrivial(vulnB) && BehaviorEvalsCode(codeVuln(input),vulnB) && vulnB[0] == s;
        var b' := unwrapVulnBehaviors(s,input);
       
        existsVulnBehavor(s,vulnB,vulnBehaviors,input);
        var vuln, vulnIn :| vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);
        possibleVulnOutputs(s,vuln);
        assert equalOutput(behaviorOutput(vuln),validOutput());
        
        var vulnOut := allBehaviorOutputSet(vulnBehaviors);
        assert validOutput() in vulnOut;

    }


    lemma patchIsBenignTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires |patchBehaviors| == 0
        requires |patchOut| == 0
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors);
        ensures forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut
        {
            reveal_nonTrivialBehaviorPreconditionsVuln();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            assert |patchBehaviors| == 0;
            assert |patchOut| == 0;
            assert forall postB :: postB in patchBehaviors ==> postB in vulnBehaviors;
            assert forall postB :: postB in patchBehaviors ==> (exists preB :: preB in vulnBehaviors && equalOutput(behaviorOutput(preB), behaviorOutput(postB)));
            assert forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut;
            
        }


    lemma patchIsBenignNonTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |patchBehaviors| > 0;
        requires vulnOut == allBehaviorOutputSet(vulnBehaviors);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);

        ensures forall postB :: postB in patchBehaviors ==> exists preB :: (preB in vulnBehaviors && equalOutput(behaviorOutput(preB), behaviorOutput(postB)));
        ensures forall postB :: postB in patchBehaviors ==> equalOutput(behaviorOutput(postB),validOutput());
        ensures forall postB :: postB in patchBehaviors ==> behaviorOutput(postB) in vulnOut;
        ensures forall postB :: postB in patchBehaviors ==> behaviorOutput(postB) in patchOut;
    {
        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        assert |patchBehaviors| > 0;
        assert forall postB :: postB in patchBehaviors ==> validPatchBehavior(postB);

        forall postB | postB in patchBehaviors
            ensures exists preB :: (preB in vulnBehaviors && equalOutput(behaviorOutput(preB), behaviorOutput(postB)));
            ensures equalOutput(behaviorOutput(postB),validOutput());
            ensures behaviorOutput(postB) in vulnOut;
            ensures behaviorOutput(postB) in patchOut;
            {

                var input :| BehaviorEvalsCode(codePatch(input),postB) && |postB| > 0 && validInput(postB[0],input);
                var b' := unwrapPatchBehaviors(s,input);
                assert equalOutput(behaviorOutput(postB),validOutput());

                vulnBehaviorIncludesPatchedBehavior(s,postB,vulnBehaviors);
                assert exists preB :: (preB in vulnBehaviors && equalOutput(behaviorOutput(preB), validOutput()));
                var preB :| (preB in vulnBehaviors && equalOutput(behaviorOutput(preB), validOutput()));
                assert behaviorOutput(preB) in vulnOut;
                
                transitiveEquality(behaviorOutput(postB),behaviorOutput(preB),validOutput());
                assert behaviorOutput(postB) == behaviorOutput(preB);
                equalOutputIsTransitiveSet(behaviorOutput(preB),behaviorOutput(postB),vulnOut);
                assert behaviorOutput(postB) in vulnOut;
            }
        assert forall postB :: postB in patchBehaviors ==> behaviorOutput(postB) in vulnOut;
            
    }

   lemma validInputPatchImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: ValidBehaviorNonTrivial(b) &&  BehaviorEvalsCode(codePatch(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codePatch(input),b) && b[0] == s
        {
            var b := unwrapPatchBehaviors(s,input);
            assert exists b' :: ValidBehaviorNonTrivial(b') && BehaviorEvalsCode(codePatch(input),b') && b'[0] == s;
        }
    }

    lemma validInputVulnImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s
        {
            var b := unwrapVulnBehaviors(s,input);
            assert exists b' :: ValidBehaviorNonTrivial(b') && BehaviorEvalsCode(codeVuln(input),b') && b'[0] == s;
        }
    }

    
}