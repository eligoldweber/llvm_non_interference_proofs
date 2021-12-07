include "simpleBugBenignLemmas.i.dfy"
include "simpleBugCompleteLemmasV2.i.dfy"
include "simpleBugCode.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "simpleBugGeneral.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"


module simpleBugProperties{
    import opened simpleBugBenignLemmas
    import opened simpleBugCompleteLemmasV2
    import opened simpleBugCode
    import opened LLVM_defRE
    import opened types
    import opened simpleBugGeneral
    import opened Collections__Seqs_s
    import opened Collections__Sets_i






///////////////////////////////


    lemma patchIsBenign(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        ensures benignPatch(vulnBehaviors,patchBehaviors)
    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        
        var vulnOut := allBehaviorOutputSet(vulnBehaviors);
        var patchOut :=  allBehaviorOutputSet(patchBehaviors);
        if (|patchBehaviors| == 0){
            patchIsBenignTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall p :: p in patchOut ==> p in vulnOut;
        }else{
            assert |patchBehaviors| > 0;
            patchIsBenignNonTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall p :: p in patchOut ==> p in vulnOut;
        }
    }


//  predicate successfulPatch(b:set<behavior>)
//     {
//         forall p :: MiniSpec(p) ==> !(p in b)
//     }

 lemma patchIsSuccessful(s:state,patchBehaviors:set<behavior>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors)
        ensures successfulPatch(patchBehaviors)
    {    
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        
        var result := LV("result");
         if (|patchBehaviors| == 0){
             assert forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
         } else {
             assert |patchBehaviors| > 0;
             assert forall q :: MiniSpec(q) ==> RemovedBehaviors(q);
             forall p | p in patchBehaviors
                ensures !MiniSpec(p);
                {  
                    var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
                    var b' := unwrapPatchBehaviors(s,input);
                    behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codePatch(input),b');
                    assert !RemovedBehaviors(p);
                    assert !MiniSpec(p);
                }
                
                assert forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
             }
         }

    lemma patchIsComplete(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |patchBehaviors| > 0;
        ensures completePatchMS(vulnBehaviors,patchBehaviors);
    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        reveal_behaviorOutput();

        var vulnModMs := findModMsSet(s,vulnBehaviors);
        var vulnModMsOut := allBehaviorOutputSet(vulnModMs);
        var patchOut :=  allBehaviorOutputSet(patchBehaviors);

        assert vulnModMs ==  MakeSubset(vulnBehaviors, x => !MiniSpec(x));
         if(|vulnBehaviors| == 0)
         {
            patchIsCompleteEmptyVulnSet(s,vulnModMs,patchBehaviors,vulnModMsOut,patchOut);
            assert completePatchMS(vulnBehaviors,patchBehaviors);
        }else{
            assert |vulnBehaviors| > 0;
            assert |vulnBehaviors| >= |patchBehaviors|;
            if(|vulnModMs| == 0)
            {
                patchIsCompleteEmptyVulnSet(s,vulnModMs,patchBehaviors,vulnModMsOut,patchOut);
                assert completePatchMS(vulnBehaviors,patchBehaviors);
            }else{
                assert |patchBehaviors| > 0;
                assert |vulnModMs| > 0;
                patchIsCompleteNonTrivial(s,vulnModMs,patchBehaviors,vulnModMsOut,patchOut);
                assert completePatchMS(vulnBehaviors,patchBehaviors);

            }
        }
       
    }


    lemma fullPatch(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires benignPatch(vulnBehaviors,patchBehaviors);
        requires successfulPatch(patchBehaviors);
        requires completePatchMS(vulnBehaviors,patchBehaviors);

        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |patchBehaviors|  > 0
        // requires completePatch(vulnBehaviors,patchBehaviors);
        //
        // requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)

        // ensures safePatch(a,b);
    {
        var aModuloMS := findModMsSet(s,vulnBehaviors);
        // var aModuloMS := MakeSubset(vulnBehaviors, x => !MiniSpec(x));
        var aOutMS := allBehaviorOutputSet(aModuloMS);
        var aOut := allBehaviorOutputSet(vulnBehaviors);
        var bOut := allBehaviorOutputSet(patchBehaviors);

        assert forall p :: behaviorOutput(p) in aOutMS ==> behaviorOutput(p) in bOut;
        // assert (forall p :: behaviorOutput(p) in bOut ==> behaviorOutput(p) in aOutMS) ==> safePatchMS(vulnBehaviors,patchBehaviors);

        assert forall p :: behaviorOutput(p) in bOut ==> behaviorOutput(p) in aOut;
        assert  forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
        subsetOfBehaviorImpliesSubsetOfOutputFull(vulnBehaviors,aModuloMS,aOut,aOutMS,x => !MiniSpec(x));
        assert forall p :: p in aOutMS ==> p in aOut;

        // assert (forall p :: behaviorOutput(p) in bOut ==> behaviorOutput(p) in aOut) ;
        // assert aOutMS == allBehaviorOutputSet(aModuloMS);
        // assert bOut ==  allBehaviorOutputSet(patchBehaviors);
        // assert ValidState(s);
        // assert forall p :: p in aModuloMS ==> !MiniSpec(p);
        // assert forall b :: b in aModuloMS ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s);
        // assert nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);
        // assert |patchBehaviors|  > 0;
        if(|aModuloMS| > 0)
        {
            patchBehaviorsInVulnModMSBehaviors(s,aModuloMS,patchBehaviors,aOutMS,bOut);
            assert forall p :: p in bOut  ==> p in aOutMS; 
            assert safePatchMS(vulnBehaviors,patchBehaviors);
        }
        // patchIsSafeHelper(s,aModuloMS,patchBehaviors,aOutMS,bOut);
        // assert |aModuloMS| > 0 ==>
        // assert (|aModuloMS| > 0) ==> (forall p :: p in bOut  ==> p in aOutMS); 
        // assert (|aModuloMS| > 0) ==>  safePatchMS(vulnBehaviors,patchBehaviors);

        // assert false;
        // assert |patchBehaviors|  > 0;
        // assert forall p :: behaviorOutput(p) in bOut ==> MiniSpec(p);


        // assert safePatchMS(vulnBehaviors,patchBehaviors);

    }


    // lemma patchIsSafeHelper(s:state,aModuloMS:set<behavior>,patchBehaviors:set<behavior>,vulnModMsOut:set<seq<output>>,patchOut:set<seq<output>>)
    //     requires vulnModMsOut == allBehaviorOutputSet(aModuloMS);
    //     requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
    //     requires ValidState(s);
    //     requires forall p :: p in aModuloMS ==> !MiniSpec(p);
    //     requires forall b :: b in aModuloMS ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
    //     requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors);
    //     requires |patchBehaviors|  > 0
    //     ensures (|aModuloMS| > 0) ==> (forall p :: p in patchOut  ==> p in vulnModMsOut);
    //     // ensures benignPatch(vulnBehaviors,patchBehaviors)
    // {
    //     reveal_nonTrivialBehaviorPreconditionsVuln();
    //     reveal_nonTrivialBehaviorPreconditionsPatch();
    //     // reveal_BehaviorEvalsCode();
    //     // reveal_ValidBehavior();
    //     reveal_behaviorOutput();
    //     // var vulnModMs := findModMsSet(s,vulnBehaviors);
    //     // var vulnModMsOut := allBehaviorOutputSet(aModuloMS);
    //     // var patchOut :=  allBehaviorOutputSet(patchBehaviors);

    //     // assert vulnModMs ==  MakeSubset(vulnBehaviors, x => !MiniSpec(x));
    //      if(|aModuloMS| == 0)
    //      {
    //         //   assert  forall p :: p in patchOut  ==> p in vulnModMsOut;
    //      }
    //     else{
    //         assert |aModuloMS| > 0;
    //         patchBehaviorsInVulnModMSBehaviors(s,aModuloMS,patchBehaviors,vulnModMsOut,patchOut);
    //         assert  forall p :: p in patchOut  ==> p in vulnModMsOut;
    //     }
    // }

    // forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) ==> behaviorOutput(p) in bOut
    // lemma patchIsComplete(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
    //     requires ValidState(s);
    //     requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    //     // ensures completePatch(vulnBehaviors,patchBehaviors)
    // {
    //     reveal_nonTrivialBehaviorPreconditionsVuln();
    //     reveal_nonTrivialBehaviorPreconditionsPatch();
    //     reveal_behaviorOutput();
    //     // reveal_BehaviorEvalsCode();
    //     var vulnOut := allBehaviorOutput(vulnBehaviors);
    //     var patchOut :=  allBehaviorOutput(patchBehaviors);
    //     // assert forall p :: behaviorOutput(p) in vulnOut <==> (exists i :: (i >= 0 && i < |vulnBehaviors|) && vulnOut[i] == behaviorOutput(vulnBehaviors[i]));
    //     if(|vulnBehaviors| == 0){
    //         patchIsCompleteTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
    //         assert (forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut);

    //     }
    //      if (|patchBehaviors| > 0){
    //         patchIsCompleteNonTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
    //         // assert (forall p :: (p in vulnBehaviors && !MiniSpec(p)) ==> p in patchBehaviors);
    //         // assert (forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut);
    //      }
    // }
    

}