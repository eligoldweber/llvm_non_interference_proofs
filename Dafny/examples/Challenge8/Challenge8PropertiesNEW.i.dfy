include "Challenge8CodeNEW.s.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Seqs.i.dfy"


module challenge8Benign{
    import opened challenge8CodeNEW
    import opened LLVM_def_NEW
    import opened types
    import opened behavior_lemmas
    import opened Collections__Seqs_s
    import opened Collections__Seqs_i

    lemma vulnBehavorsTest(s:state,c:seq<Code>) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_8_transport_handler_create_conn_vuln_test();
        // decreases *;
    {
        reveal_ValidBehavior();
        //    [ Block([CNil]), Block([CNil]), Block([CNil])]
        var b:behavior := evalCodeSeqFn(c,s);
        assert ValidBehaviorV2([s] + b);
        assert |b| >= 0;
        assert c == [ Block([CNil]), Block([CNil]), Block([CNil])];

        var step,remainder,subB := unwrapCodeWitness(b,c,s);
        assert step == evalCodeFn(Block([CNil]),s);
        assert remainder == [Block([CNil]), Block([CNil])];
        // lets dive into the block
            var subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s);
            assert subStep == [s];
            assert subRemainder == [];
            assert subSubB == [s];
            // unwrapped entire subBlock
        assert step == subStep+subSubB;
        assert b[..|step|] == step;

        var s' := last(step);
        step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
        assert step == evalCodeFn(Block([CNil]),s');
        assert remainder == [ Block([CNil])];
            // lets dive into the block
            subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s');
            assert subStep == [s'];
            assert subRemainder == [];
            assert subSubB == [s'];

         assert step == subStep+subSubB;
        assert couldBeSubSeq(b,step);

        s' := last(step);
        step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
        assert step == evalCodeFn(Block([CNil]),s');
        assert remainder == [];

        assert subB == [s'];
        assert ValidBehavior(b);
        assert NextStep(b[0],b[1],Step.stutterStep());
        assert StateNext(b[0],b[1]);
        assert NextStep(b[1],b[2],Step.stutterStep());
        assert StateNext(b[1],b[2]);
        assert |b| == 7;
        preB := b;
    }

lemma patchBehavorsTest(s:state,c:seq<Code>) returns (postB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_8_transport_handler_create_conn_patch();
        // decreases *;
    {
        reveal_ValidBehavior();
        //    [ Block([CNil]), Block([CNil]), Block([CNil])]
        var b:behavior := evalCodeSeqFn(c,s);
        assert ValidBehaviorV2([s] + b);
        assert |b| >= 0;
        
        var step,remainder,subB := unwrapCodeWitness(b,c,s);
        assert step == evalCodeFn(Block([CNil]),s);
        // assert remainder == [patch_block,postfixCode()];
        // lets dive into the block
            var subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s);
            assert subStep == [s];
            assert subRemainder == [];
            assert subSubB == [s];
            // unwrapped entire subBlock
        assert step == subStep+subSubB;
        assert b[..|step|] == step;

        var s' := last(step);
        var mainBlock := remainder;
        // assert re
        step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
        assert remainder == [ Block([CNil])];
         // lets dive into the block
            assert step == evalCodeFn(first(mainBlock),s');
            assert first(mainBlock).Block?;
            assert step == evalCodeSeqFn(first(mainBlock).block,s');

            // assert step == evalCodeSeqFn(first(mainBlock),s');
            subStep,subRemainder,subSubB := unwrapCodeWitness(step,first(mainBlock).block,s');
            assert |subStep| == 1;
            assert s'.ok;
            assert first(mainBlock).block[0].Ins?;
            assert first(mainBlock).block[0].ins.SDIV?;
            assert ValidOperand(s',first(mainBlock).block[0].ins.dst);
            var testIns := first(mainBlock).block[0].ins;
                
            assert ValidInstruction(s', first(mainBlock).block[0].ins);
            assert NextStep(s',subStep[0],Step.evalInsStep(first(mainBlock).block[0].ins));
            // assert subRemainder == [];
            assert b[1] == s';
            assert b[2] == subStep[0];  
            s' := subStep[0];
            var nextIns := subRemainder;
            subStep,subRemainder,subSubB := unwrapCodeWitness(subSubB,subRemainder,s');
            assert |subStep| == 1;
            assert NextStep(s',subStep[0],Step.evalInsStep(first(nextIns).ins));
            assert b[3] == subStep[0];
            assert ValidInstruction(s', first(nextIns).ins);

            s' := subStep[0];
            nextIns := subRemainder;
            assert first(subRemainder).IfElse?;
            assert validIfCond(s',first(subRemainder).ifCond);
                //unwrap branch
            assert |subRemainder| > 0;
            subStep,subRemainder,subSubB := unwrapCodeWitness(subSubB,subRemainder,s');
             
                if dataToBool(OperandContents(s',first(nextIns).ifCond)){
                    assert subStep == evalCodeFn(first(nextIns).ifTrue,s');
                    // new block that needs unwrapping 
                    patchBehavorsTestsubBlock(subStep,first(nextIns).ifTrue,s');
                    // var if_true_block := first(nextIns).ifTrue;
                    // var step_if_then19,remainder_if_then19,subB_if_then19 := unwrapCodeWitness(subStep,if_true_block.block,s');
                    // assert |step_if_then19| == 1;
                    // assert first(if_true_block.block).Ins?;
                    // assert first(if_true_block.block).ins.CALL?;
                    // assert NextStep(s',step_if_then19[0],Step.evalInsStep(first(if_true_block.block).ins));

                    // var if_true_next := first(remainder_if_then19);
                    // s' := first(step_if_then19); 
                    // step_if_then19,remainder_if_then19,subB_if_then19 := unwrapCodeWitness(subB_if_then19,remainder_if_then19,s');
                    // assert |step_if_then19| == 1;
                    // assert NextStep(s',step_if_then19[0],Step.evalInsStep((if_true_next).ins));
                    // assert |remainder_if_then19| == 1;


                }else{
                    assert subStep == evalCodeFn(first(nextIns).ifFalse,s');
                    assert subRemainder == [];
                    assert subSubB == [s']; 
                    assert b[4] == subStep[0]; 
                    assert b[5] == subStep[0];
                    assert |b| == 10;
                }
        
        s' := last(step);
        step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
        assert step == evalCodeFn(Block([CNil]),s');
        assert remainder == [];

        assert subB == [s'];


            // assert subSubB == [s];


    }

    lemma {:opaque} patchBehavorsTestsubBlock(b:behavior,c:Code,s:state)
        requires c == if_then19();
        requires ValidState(s);
        requires validConfig(s,allVariablesConfig());
        requires b == evalCodeSeqFn(c.block,s);
        ensures  first(c.block).Ins?;
        ensures first(c.block).ins.CALL?;
        
        
    {
        var behavior := evalCodeSeqFn(c.block,s);
        var initalCode := c.block;
        var step,remainder,subB := unwrapCodeWitness(b,c.block,s);
        assert |step| == 1;
        assert first(initalCode).Ins?;
        assert first(initalCode).ins.CALL?;
        assert StateNext(s,step[0]);
        // assert step == [evalInsRe(first(initalCode).ins,s)];
        // assert s.ok;
        assert NextStep(s,step[0],Step.evalInsStep(first(initalCode).ins));
        initalCode := remainder;
        var s' := step[0];
        assert ValidState(s');
        step,remainder,subB := unwrapCodeWitness(subB,remainder,last(step));
        assert |step| == 1;
        assert first(initalCode).Ins?;
        assert first(initalCode).ins.STORE?; 
        // assert ensures first(c.block).ins.STORE?;
        // assert s'.ok;
        // assert ValidOperand(s',first(initalCode).ins.valueToStore);
        // assert ValidOperand(s',first(initalCode).ins.ptr);
        // assert ValidInstruction(s',first(initalCode).ins);
        // assert NextStep(s',step[0],Step.evalInsStep(first(initalCode).ins));

        // assert false;
    }


    // lemma patchBehaviors(s:state,c:codeRe) returns (postB:behavior)
    //     requires ValidState(s);
    //     requires validStartingState(s);
    //     requires c == challenge_8_transport_handler_create_conn_patch();
        
    //     ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),postB);
    // {
    //     reveal_BehaviorEvalsCode();
    //     assert |c.block| == 3;
    //     postB := [s] + evalBlockRE(c.block,s);

    //     assert first(c.block).Block?;
    //     assert c.Block?;
    //     var metaBehavior := evalCodeRE(first(c.block),s);
    //     // assert postB == [s] + metaBehavior + evalBlockRE(all_but_first(c.block),last(metaBehavior));
    //    ///
    //     assert first(c.block) == Block([CNil]);
    //     assert first(c.block).Block?;
    //     assert metaBehavior == [s] + evalBlockRE(first(c.block).block, s); 
    //     var tempMeta := evalCodeRE(CNil,s);
    //     assert tempMeta == [s];
    //     assert metaBehavior == [s] + [s] + evalBlockRE([],s);
    //     assert metaBehavior == [s,s,s];
    //     // assert postB == [s] + [s] + [s] + evalBlockRE([patchBlock(),postfixCode()],s);
    //     // assert metaBehavior == evalCodeRE(CNil,s) + evalBlockRE([],s);
    // ////
    //     var step,remainder,subBehavior := unwrapBlockWitness(postB,c.block,s);
    //     // assert subBehavior == metaBehavior;
    //     assert postB[0] == s; 
    //     assert first(remainder).CNil?;
    //     assert NextStep(postB[0],postB[1],Step.stutterStep());
    //     assert StateNext(postB[0],postB[1]);
    //     assert postB[1] == last(step);
    //     assert step == [s];
    //     assert remainder == [CNil] + all_but_first(c.block);
    //     assert all_but_first(c.block) == [patchBlock(),postfixCode()];
    //     // assert subBehavior == [s] + evalBlockRE(remainder,s);
    //     assert evalBlockRE(remainder,s) == [s] + evalBlockRE([patchBlock(),postfixCode()],s);
    //     // assert postB == [s] + [postB[1]] + evalCodeRE(Block(remainder) ,last(step));
    //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
    //     assert remainder == all_but_first(c.block);
    //     assert |remainder| == 2;
    //     assert remainder == [patchBlock(),postfixCode()];
    //     assert step == [s];
    //             // assert postB[2] == last(step);

    //     assert NextStep(postB[1],last(step),Step.stutterStep());
    //     assert last(step) == postB[1];
    //     // assert StateNext(postB[1],postB[2]);
        
    //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
    //     // assert remainder == [patchBlock(),postfixCode()];


    //     // assert postB[2] == evalInsRe(CALL(D(Void),delete_connection()),postB[1]);
    //     // assert NextStep(postB[1],postB[2],Step.stutterStep());
    //     // assert StateNext(postB[1],postB[2]); 
    //     // assert |preB| == 5;
    //     // assert ValidBehaviorNonTrivial(postB); 
    // }

    //     // benignPatch: "The patch does not add any NEW behaviors"
    // predicate benignPatch(pre:set<behavior>,post:set<behavior>)
    // {
    //     var preOutput := allBehaviorOutputSet(pre);
    //     var postOutput := allBehaviorOutputSet(post);
    //     forall postB :: postB in postOutput ==> postB in preOutput
    // }

    // lemma equalPrefixBlocksEvalEquallyAndAreBenign(blockA:codeRe,blockB:codeRe)
    //     requires blockA == blockB
    //     ensures forall s :: ValidState(s) ==> evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    //     ensures forall s :: ValidState(s) ==> benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
    // {
    //     forall s | ValidState(s)
    //         ensures evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    //         ensures benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
    //     {
    //         var b_a := evalCodeRE(blockA,s);
    //         var b_b := evalCodeRE(blockB,s);
    //         assert b_a == b_b;
    //         assert benignPatch({b_a},{b_b});
    //     }
    // }

    // // Proof
    // function vulnified(s:state) : (s_vuln:state)
    // {
    //     // assume exists vuln :: BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln) && |vuln| > 0;
    //     // var vuln :| BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln);
    //     // assume exists s_vuln :: s_vuln in vuln;
    //     // var s_vuln :| s_vuln in vuln;
    //     // s_vuln
    //     s
    // }

    // function patchified(s:state) : state
    // {
    //     s
    // }

    // function mapPatchedToVuln(patchedBehavior:behavior) : (mappedBehavior:behavior)
    //     // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),patchedBehavior)
    //     ensures |patchedBehavior| == |mappedBehavior|
    //     ensures forall i :: (i >= 0 && i < |patchedBehavior|) ==> mappedBehavior[i] == vulnified(patchedBehavior[i])
    //     //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    // {
    //     //placeholder
    //     if(|patchedBehavior| == 0) then
    //         var mappedBehavior := [];
    //         mappedBehavior
    //     else 
    //         var rest := mapPatchedToVuln(all_but_first(patchedBehavior));
    //         var mappedBehavior := [vulnified(patchedBehavior[0])] + rest;
    //         mappedBehavior
        
    // }

    //  function mapVulnToPatched(vulnBehaviors:behavior) : (mappedBehavior:behavior)
    //     // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),patchedBehavior)
    //     ensures |vulnBehaviors| == |mappedBehavior|
    //     ensures forall i :: (i >= 0 && i < |vulnBehaviors|) ==> mappedBehavior[i] == patchified(vulnBehaviors[i])
    //     //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patched(),mappedBehavior)
    // {
    //     //placeholder
    //     if(|vulnBehaviors| == 0) then
    //         var mappedBehavior := [];
    //         mappedBehavior
    //     else 
    //         var rest := mapVulnToPatched(all_but_first(vulnBehaviors));
    //         var mappedBehavior := [patchified(vulnBehaviors[0])] + rest;
    //         mappedBehavior
        
    // }

    // predicate canMapToVuln(patchedBehavior:behavior)
    // {
    //     var mappedBehavior := mapPatchedToVuln(patchedBehavior);
    //     BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    // }

    // predicate canMapToPatch(vulnBehavior:behavior)
    // {
    //     var mappedBehavior := mapVulnToPatched(vulnBehavior);
    //     BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),mappedBehavior)
    // }

    // lemma patchIsBenign(vuln:codeRe,patch:codeRe)
    //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     //ensures forall b :: BehaviorEvalsCode(patch,b) ==> canMapToVuln(b)
    // {

    // }

    // predicate miniSpec(b:behavior)
    // {
    //     true
    // }

    // lemma patchIsSuccesful(patch:codeRe)
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     // ensures forall b :: BehaviorEvalsCode(patch,b) ==> !miniSpec(b)
    // {

    // }
    
    // //     predicate completePatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    // // {
    // //     // forall p :: (p in a && !MiniSpec(p)) ==> p in b

    // //     var preOutput := allBehaviorOutputSet(pre);
    // //     var postOutput := allBehaviorOutputSet(post);
    // //     forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) ==> behaviorOutput(preB) in postOutput
    // // }

    // lemma patchIsComplete(vuln:codeRe,patch:codeRe)
    //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     // ensures forall b :: BehaviorEvalsCode(vuln,b) && !miniSpec(b) ==> canMapToPatch(b);
    // {

    // }

    // // lemma patchIsBenign(s:state,vuln:codeRe,patch:codeRe)
    // //     requires ValidState(s)
    // //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    // //     requires patch == challenge_8_transport_handler_create_conn_patch();
    // //     // requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    // //     // ensures benignPatch(vulnBehaviors,patchBehaviors)
    // // {
    // //     prefixAndPostfixAreEqual();
    // //     assert benignPatch({evalCodeRE(vuln.block[0],s)},{evalCodeRE(patch.block[0],s)});
    // //     assert |vuln.block| == |patch.block|;
    // //     var prefix_vuln_s := last(evalCodeRE(vuln.block[0],s));
    // //     var prefix_patch_s := last(evalCodeRE(patch.block[0],s));
    // //     assert prefix_vuln_s == prefix_patch_s;
    // //     var evalVuln := evalCodeRE(vuln,s);
    // //     // assert forall r :: r in evalVuln ==> r == s;
    // //     // assert forall i :: (&& i >= 0 
    // //     //                    && i < |vuln.block|
    // //     //                    && benignPatch({evalCodeRE(vuln.block[i],s)},{evalCodeRE(patch.block[i],s)}))
    // //     //                    ==> benignPatch({evalCodeRE(vuln,s)},{evalCodeRE(patch,s)});
        
    // // }

}

