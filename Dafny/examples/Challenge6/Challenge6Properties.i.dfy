include "Challenge6Code.s.dfy"
include "Challenge6CodeLemmasPatch.i.dfy"
include "Challenge6CodeLemmasVuln.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Sets.i.dfy"
include "Challenge6Common.i.dfy"

module challenge6Properties{
    import opened challenge6Code
    import opened challenge6CodeLemmasPatch
    import opened challenge6CodeLemmasVuln
    import opened behavior_lemmas
    import opened LLVM_defRE
    import opened types
    import opened Collections__Sets_i
    import opened challenge6common

        // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(pre:set<behavior>,post:set<behavior>)
    {
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall postB :: postB in postOutput ==> postB in preOutput
    }


    
    lemma patchIsBenign(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        ensures benignPatch(vulnBehaviors,patchBehaviors)
    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        
        var vulnOut := allBehaviorOutputSet(vulnBehaviors);
        var patchOut :=  allBehaviorOutputSet(patchBehaviors);
        if (|patchBehaviors| == 0){
            // patchIsBenignTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut;
        }else{
            assert |patchBehaviors| > 0;
            patchIsBenignNonTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            // assert forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut;
        }
    }

    lemma patchIsBenignNonTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |patchBehaviors| > 0;
        requires vulnOut == allBehaviorOutputSet(vulnBehaviors);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        ensures  forall patchO :: patchO in patchOut ==> patchO in vulnOut;
    {
        reveal_BehaviorEvalsCode();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        assert |patchBehaviors| > 0;
        assert forall postB :: postB in patchBehaviors ==> validPatchBehavior(postB);

        forall postB | postB in patchBehaviors
            ensures behaviorOutput(postB) == validBehaviorsOuts();
        {
            var b := unwrapPatchBehaviors(s,challenge_prob_6_code_write_encrypted_simple_patch());
            assert behaviorOutput(postB) == validBehaviorsOuts();
        }
        forall preB | preB in vulnBehaviors
            ensures behaviorOutput(preB) == validBehaviorsOuts();
            ensures behaviorOutput(preB) in vulnOut;
        {
            var b := unwrapVulnBehaviors(s,challenge_prob_6_code_write_encrypted_simple_vuln());
            assert behaviorOutput(preB) == validBehaviorsOuts();
        }

        assert SurjectiveOver(patchBehaviors,patchOut, x => behaviorOutput(x));
        forall patchO | patchO in patchOut
            ensures patchO in vulnOut;
        {
            assert exists patchB :: patchB in patchBehaviors && behaviorOutput(patchB) == patchO;
            var patchB :| patchB in patchBehaviors && behaviorOutput(patchB) == patchO;
            assert equalOutput(behaviorOutput(patchB),validBehaviorsOuts());
            assert patchO in vulnOut;

        } 

    }



  predicate validPatchBehavior(b:behavior)
    {
        BehaviorEvalsCode(challenge_prob_6_code_write_encrypted_simple_patch(),b) && |b| > 0 && ValidState(b[0]) && validInput(b[0])
    }

   predicate nonTrivialBehaviorPreconditions(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
    {
        && ValidState(s)
        && nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors)
        && nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors)
        && |vulnBehaviors| >= |patchBehaviors|
    }

        
    predicate {:opaque} nonTrivialBehaviorPreconditionsPatch(s:state,patchBehaviors:set<behavior>)
        requires ValidState(s)
    {   
        (forall b :: b in patchBehaviors <==> ( && validStartingState(s)
                                                && validInput(s)
                                                && ValidBehaviorNonTrivial(b)
                                                && BehaviorEvalsCode(challenge_prob_6_code_write_encrypted_simple_patch(),b)
                                                && b[0] == s))
    }
    
    predicate {:opaque} nonTrivialBehaviorPreconditionsVuln(s:state,vulnBehaviors:set<behavior>)
        requires ValidState(s)
    {
        (forall b :: b in vulnBehaviors <==> (&& validStartingState(s)
                                              && validInput(s)
                                              && ValidBehaviorNonTrivial(b)
                                              && BehaviorEvalsCode(challenge_prob_6_code_write_encrypted_simple_vuln(),b)
                                              && b[0] == s))
    }

}