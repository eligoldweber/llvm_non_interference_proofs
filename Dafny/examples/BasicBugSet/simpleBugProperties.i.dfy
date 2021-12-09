include "simpleBugBenignLemmas.i.dfy"
include "simpleBugCompleteLemmas.i.dfy"
include "simpleBugGeneral.i.dfy"
include "simpleBugCode.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"


module simpleBugProperties{
    import opened simpleBugBenignLemmas
    import opened simpleBugCompleteLemmas
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i
    import opened behavior_lemmas

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
            assert forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut;
        }else{
            assert |patchBehaviors| > 0;
            patchIsBenignNonTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall postOutput :: postOutput in patchOut ==> postOutput in vulnOut;
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
             assert forall behavior :: MiniSpec(behavior) ==> !(behavior in patchBehaviors);
         } else {
             assert |patchBehaviors| > 0;
             assert forall behavior :: MiniSpec(behavior) ==> RemovedBehaviors(behavior);
             forall postB | postB in patchBehaviors
                ensures !MiniSpec(postB);
                {  
                    var input :| BehaviorEvalsCode(codePatch(input),postB) && |postB| > 0 && validInput(postB[0],input);
                    var postBWitness := unwrapPatchBehaviors(s,input);
                    behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codePatch(input),postBWitness);
                    assert !RemovedBehaviors(postB);
                    assert !MiniSpec(postB);
                }
                
                assert forall behavior :: MiniSpec(behavior) ==> !(behavior in patchBehaviors);
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
        //
        ensures |MakeSubset(vulnBehaviors, x => !MiniSpec(x))|> 0 ==> safePatchMS(vulnBehaviors,patchBehaviors); 
    {
        var aModuloMS := findModMsSet(s,vulnBehaviors);
        var aOutMS := allBehaviorOutputSet(aModuloMS);
        var aOut := allBehaviorOutputSet(vulnBehaviors);
        var bOut := allBehaviorOutputSet(patchBehaviors);

        assert forall p :: behaviorOutput(p) in aOutMS ==> behaviorOutput(p) in bOut;

        assert forall p :: behaviorOutput(p) in bOut ==> behaviorOutput(p) in aOut;
        assert  forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
        // subsetOfBehaviorImpliesSubsetOfOutputFull(vulnBehaviors,aModuloMS,aOut,aOutMS,x => !MiniSpec(x));
        // assert forall p :: p in aOutMS ==> p in aOut;
 
        if(|aModuloMS| > 0)
        {
            patchBehaviorsInVulnModMSBehaviors(s,aModuloMS,patchBehaviors,aOutMS,bOut);
            assert forall p :: p in bOut  ==> p in aOutMS; 
            assert safePatchMS(vulnBehaviors,patchBehaviors);
        }

    }

    lemma fullPatchNonTrivial(vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires |patchBehaviors|  > 0
        requires |MakeSubset(vulnBehaviors, x => !MiniSpec(x))| > 0
        ensures forall s :: nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors) ==> safePatchMS(vulnBehaviors,patchBehaviors); 
    {
        forall s | nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
            ensures safePatchMS(vulnBehaviors,patchBehaviors); 
            {
                patchIsBenign(s,vulnBehaviors,patchBehaviors);
                patchIsSuccessful(s,patchBehaviors);
                patchIsComplete(s,vulnBehaviors,patchBehaviors);
                assert benignPatch(vulnBehaviors,patchBehaviors);
                assert successfulPatch(patchBehaviors);
                assert completePatchMS(vulnBehaviors,patchBehaviors); 
                fullPatch(s,vulnBehaviors,patchBehaviors);
            }
    }

}