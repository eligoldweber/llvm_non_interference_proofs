include "simpleBugBenignLemmas.i.dfy"
include "simpleBugCode.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "simpleBugGeneral.i.dfy"
include "../../Libraries/Seqs.s.dfy"


module simpleBugProperties{
    import opened simpleBugBenignLemmas
    import opened simpleBugCode
    import opened LLVM_defRE
    import opened types
    import opened simpleBugGeneral
    import opened Collections__Seqs_s






///////////////////////////////


    lemma patchIsBenign(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        ensures benignPatch(vulnBehaviors,patchBehaviors)
    {
        var vulnOut := allBehaviorOutput(vulnBehaviors);
        var patchOut :=  allBehaviorOutput(patchBehaviors);
        if (|patchBehaviors| == 0){
            patchIsBenignTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall p :: p in patchOut ==> p in vulnOut;
        }else{
            assert |patchBehaviors| > 0;
            patchIsBenignNonTrivial(s,vulnBehaviors,patchBehaviors,vulnOut,patchOut);
            assert forall p :: p in patchOut ==> p in vulnOut;
        }
    }


//  predicate successfulPatch(b:seq<behavior>)
//     {
//         forall p :: MiniSpec(p) ==> !(p in b)
//     }

 lemma patchIssuccessful(s:state,patchBehaviors:seq<behavior>)
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors)
        // ensures benignPatch(vulnBehaviors,patchBehaviors)
    {    
        var result := LV("result");
         if (|patchBehaviors| == 0){
             assert forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
         } else {
             assert |patchBehaviors| > 0;
             forall p | p in patchBehaviors
                {  
                    var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
                    var b' := unwrapPatchBehaviors(s,input);
                    // assert ValidOperand(last(p),result);
                    // assert !RemovedBehaviorsUpdated(p);
                    assert forall q :: MiniSpec(q) ==> RemovedBehaviors(q);
                    assert forall q :: MiniSpec(q) ==> (exists s:state,result:operand :: (&& s in q
                                                                                            && last(q) == s 
                                                                                            && ValidState(s)
                                                                                            && result.LV?
                                                                                            && result.l in s.lvs
                                                                                            && ValidOperand(s,result)
                                                                                            && OperandContents(s,result).Int?
                                                                                            && OperandContents(s,result).val == 0));
                }
                
                // assert forall p :: MiniSpec(p) ==> !(p in patchBehaviors);
             }
         }
    

}