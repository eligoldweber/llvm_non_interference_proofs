include "Challenge8Code.s.dfy"
include "../../LLVM/llvmREFACTOR_Multi.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"

module challenge8Benign{
    import opened challenge8Code
    import opened LLVM_defRE_Multi
    import opened types
    import opened behavior_lemmas
    import opened Collections__Seqs_s


    lemma vulnBehaviors(s:state,c:codeRe) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_8_transport_handler_create_conn_vuln();
        
        ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),preB);
        ensures ValidBehaviorNonTrivial(preB);
    {
        reveal_BehaviorEvalsCode();
        assert |c.block| == 3;
        preB := [s] + evalCodeRE(c,s);

        var step,remainder,subBehavior := unwrapBlockWitness(preB,c.block,s);
        assert preB[0] == s;   

        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert NextStep(preB[0],preB[1],Step.stutterStep());
        assert StateNext(preB[0],preB[1]);
        assert NextStep(preB[1],preB[2],Step.stutterStep());
        assert StateNext(preB[1],preB[2]);
        // assert |preB| == 5;
        assert ValidBehaviorNonTrivial(preB);
        // assert behaviorOutput(preB) == [Nil,Nil,Nil];
    }


    lemma patchBehaviors(s:state,c:codeRe) returns (postB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_8_transport_handler_create_conn_patch();
        
        ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),postB);
    {
        reveal_BehaviorEvalsCode();
        assert |c.block| == 3;
        postB := [s] + evalCodeRE(c,s);

        var step,remainder,subBehavior := unwrapBlockWitness(postB,c.block,s);
        assert postB[0] == s; 
        assert first(remainder).CNil?;

         step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        // assert remainder == [patchBlock(),postfixCode()];
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert NextStep(postB[0],postB[1],Step.stutterStep());
        assert StateNext(postB[0],postB[1]);
        // assert postB[2] == evalInsRe(CALL(D(Void),delete_connection()),postB[1]);
        // assert NextStep(postB[1],postB[2],Step.stutterStep());
        // assert StateNext(postB[1],postB[2]); 
        // assert |preB| == 5;
        // assert ValidBehaviorNonTrivial(postB); 
    }

        // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(pre:set<behavior>,post:set<behavior>)
    {
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall postB :: postB in postOutput ==> postB in preOutput
    }

    lemma equalPrefixBlocksEvalEquallyAndAreBenign(blockA:codeRe,blockB:codeRe)
        requires blockA == blockB
        ensures forall s :: ValidState(s) ==> evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
        ensures forall s :: ValidState(s) ==> benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
    {
        forall s | ValidState(s)
            ensures evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
            ensures benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
        {
            var b_a := evalCodeRE(blockA,s);
            var b_b := evalCodeRE(blockB,s);
            assert b_a == b_b;
            assert benignPatch({b_a},{b_b});
        }
    }

    // Proof
    function vulnified(s:state) : (s_vuln:state)
    {
        // assume exists vuln :: BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln) && |vuln| > 0;
        // var vuln :| BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln);
        // assume exists s_vuln :: s_vuln in vuln;
        // var s_vuln :| s_vuln in vuln;
        // s_vuln
        s
    }

    function patchified(s:state) : state
    {
        s
    }

    function mapPatchedToVuln(patchedBehavior:behavior) : (mappedBehavior:behavior)
        // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),patchedBehavior)
        ensures |patchedBehavior| == |mappedBehavior|
        ensures forall i :: (i >= 0 && i < |patchedBehavior|) ==> mappedBehavior[i] == vulnified(patchedBehavior[i])
        //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    {
        //placeholder
        if(|patchedBehavior| == 0) then
            var mappedBehavior := [];
            mappedBehavior
        else 
            var rest := mapPatchedToVuln(all_but_first(patchedBehavior));
            var mappedBehavior := [vulnified(patchedBehavior[0])] + rest;
            mappedBehavior
        
    }

     function mapVulnToPatched(vulnBehaviors:behavior) : (mappedBehavior:behavior)
        // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),patchedBehavior)
        ensures |vulnBehaviors| == |mappedBehavior|
        ensures forall i :: (i >= 0 && i < |vulnBehaviors|) ==> mappedBehavior[i] == patchified(vulnBehaviors[i])
        //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patched(),mappedBehavior)
    {
        //placeholder
        if(|vulnBehaviors| == 0) then
            var mappedBehavior := [];
            mappedBehavior
        else 
            var rest := mapVulnToPatched(all_but_first(vulnBehaviors));
            var mappedBehavior := [patchified(vulnBehaviors[0])] + rest;
            mappedBehavior
        
    }

    predicate canMapToVuln(patchedBehavior:behavior)
    {
        var mappedBehavior := mapPatchedToVuln(patchedBehavior);
        BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    }

    predicate canMapToPatch(vulnBehavior:behavior)
    {
        var mappedBehavior := mapVulnToPatched(vulnBehavior);
        BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),mappedBehavior)
    }

    lemma patchIsBenign(vuln:codeRe,patch:codeRe)
        requires vuln == challenge_8_transport_handler_create_conn_vuln();
        requires patch == challenge_8_transport_handler_create_conn_patch();
        //ensures forall b :: BehaviorEvalsCode(patch,b) ==> canMapToVuln(b)
    {

    }

    predicate miniSpec(b:behavior)
    {
        true
    }

    lemma patchIsSuccesful(patch:codeRe)
        requires patch == challenge_8_transport_handler_create_conn_patch();
        // ensures forall b :: BehaviorEvalsCode(patch,b) ==> !miniSpec(b)
    {

    }
    
    //     predicate completePatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    // {
    //     // forall p :: (p in a && !MiniSpec(p)) ==> p in b

    //     var preOutput := allBehaviorOutputSet(pre);
    //     var postOutput := allBehaviorOutputSet(post);
    //     forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) ==> behaviorOutput(preB) in postOutput
    // }

    lemma patchIsComplete(vuln:codeRe,patch:codeRe)
        requires vuln == challenge_8_transport_handler_create_conn_vuln();
        requires patch == challenge_8_transport_handler_create_conn_patch();
        // ensures forall b :: BehaviorEvalsCode(vuln,b) && !miniSpec(b) ==> canMapToPatch(b);
    {

    }

    // lemma patchIsBenign(s:state,vuln:codeRe,patch:codeRe)
    //     requires ValidState(s)
    //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     // requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    //     // ensures benignPatch(vulnBehaviors,patchBehaviors)
    // {
    //     prefixAndPostfixAreEqual();
    //     assert benignPatch({evalCodeRE(vuln.block[0],s)},{evalCodeRE(patch.block[0],s)});
    //     assert |vuln.block| == |patch.block|;
    //     var prefix_vuln_s := last(evalCodeRE(vuln.block[0],s));
    //     var prefix_patch_s := last(evalCodeRE(patch.block[0],s));
    //     assert prefix_vuln_s == prefix_patch_s;
    //     var evalVuln := evalCodeRE(vuln,s);
    //     // assert forall r :: r in evalVuln ==> r == s;
    //     // assert forall i :: (&& i >= 0 
    //     //                    && i < |vuln.block|
    //     //                    && benignPatch({evalCodeRE(vuln.block[i],s)},{evalCodeRE(patch.block[i],s)}))
    //     //                    ==> benignPatch({evalCodeRE(vuln,s)},{evalCodeRE(patch,s)});
        
    // }

}

