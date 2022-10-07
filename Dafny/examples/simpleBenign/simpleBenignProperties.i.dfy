include "BenignCode.s.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Sets.i.dfy"

module simpleBenignProperties{
    import opened simpleBenignCode
    import opened behavior_lemmas
    import opened LLVM_defRE
    import opened types
    import opened Collections__Sets_i

    //PATCH PROPERTIES

    // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(pre:set<behavior>,post:set<behavior>)
    {
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall postB :: postB in postOutput ==> postB in preOutput
    }

    // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(post:set<behavior>)
    {
        forall postB :: MiniSpec(postB) ==> !(postB in post)
    }

    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatchMS(pre:set<behavior>,post:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b
        var preModMs := MakeSubset(pre, x => !MiniSpec(x));
        var preModMsOut := allBehaviorOutputSet(preModMs);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: behaviorOutput(preB) in preModMsOut ==> behaviorOutput(preB) in postOutput
    }

    predicate safePatchMS(pre:set<behavior>,post:set<behavior>)
    {           
    //  forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var preModMs := MakeSubset(pre, x => !MiniSpec(x));
        var preModMsOut := allBehaviorOutputSet(preModMs);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: behaviorOutput(preB) in preModMsOut <==> behaviorOutput(preB) in postOutput
    } 

    // Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
    predicate RemovedBehaviors(b:behavior)
    {
        true
    }

    predicate MiniSpec(b:behavior)
    {
        RemovedBehaviors(b)
    }


    // PROOF  

    lemma patchIsBenign(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        //ensures benignPatch(vulnBehaviors,patchBehaviors)
    {
    }

    lemma patchIsSuccesful(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
    requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    //ensures successfulPatch(patchBehaviors)
    {
    }
    
    lemma patchIsComplete(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
    requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    //ensures completePatchMS(patchBehaviors)
    {
    }

    // FINAL PROOF
    lemma fullPatch(pre:set<behavior>,post:set<behavior>)
        requires benignPatch(pre,post);
        requires successfulPatch(post);
        requires completePatchMS(pre,post);
        //ensures safePatchMS(pre,post);
    {
    }

  // UTILITY PREDICATE/LEMMAS
   predicate nonTrivialBehaviorPreconditions(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>)
    {
        && ValidState(s)
    }

        


}