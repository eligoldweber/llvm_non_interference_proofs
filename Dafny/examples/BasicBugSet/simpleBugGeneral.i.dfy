include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"
include "./simpleBugCode.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"

module simpleBugGeneral{
    import opened simpleBugCode
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i
    import opened behavior_lemmas

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
    predicate completePatch(pre:set<behavior>,post:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b

        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) ==> behaviorOutput(preB) in postOutput
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

    predicate safePatch(pre:set<behavior>,post:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) <==> behaviorOutput(preB) in postOutput
    }

    predicate safePatchMS(pre:set<behavior>,post:set<behavior>)
    {           
    //  forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var preModMs := MakeSubset(pre, x => !MiniSpec(x));
        var preModMsOut := allBehaviorOutputSet(preModMs);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: behaviorOutput(preB) in preModMsOut <==> behaviorOutput(preB) in postOutput
    }   


// lemma fullPatch(a:set<behavior>,b:set<behavior>)
//     requires benignPatch(a,b);
//     requires successfulPatch(b);
//     requires completePatch(a,b);
//     ensures safePatch(a,b);

// Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
    predicate RemovedBehaviors(b:behavior)
    {

       && ValidBehaviorNonTrivial(b)
        && exists s:state,result:operand :: (&& s in b
                                            && last(b) == s 
                                            && ValidState(s)
                                            && result.LV?
                                            && result.l == "result"
                                            && result.l in s.lvs
                                            && ValidOperand(s,result)
                                            && OperandContents(s,result).Int?
                                            && OperandContents(s,result).val == 0)
    }

    predicate MiniSpec(b:behavior)
    {
        RemovedBehaviors(b)
    }

  

/////////
    


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
        (forall b :: b in patchBehaviors <==> (exists input ::  && validInput(s,input) 
                                                                && ValidBehaviorNonTrivial(b) 
                                                                && BehaviorEvalsCode(codePatch(input),b) 
                                                                && b[0] == s))
    }
    
    predicate {:opaque} nonTrivialBehaviorPreconditionsVuln(s:state,vulnBehaviors:set<behavior>)
        requires ValidState(s)
    {
        (forall b :: b in vulnBehaviors <==> (exists input :: && validInput(s,input) 
                                                              && ValidBehaviorNonTrivial(b) 
                                                              && BehaviorEvalsCode(codeVuln(input),b) 
                                                              && b[0] == s))
    }

    predicate {:opaque} nonTrivialBehaviorPreconditionsVulnModMs(s:state,vulnBehaviorsModMs:set<behavior>)
        requires ValidState(s)
    {
        (forall b :: b in vulnBehaviorsModMs ==> (exists input :: && validInput(s,input) 
                                                                  && ValidBehaviorNonTrivial(b) 
                                                                  && BehaviorEvalsCode(codeVuln(input),b) 
                                                                  && b[0] == s))
    }

    predicate validPatchBehavior(b:behavior)
    {
        exists input :: BehaviorEvalsCode(codePatch(input),b) && |b| > 0 && ValidState(b[0]) && validInput(b[0],input)
    }

    predicate validVulnBehavior(b:behavior)
    {
        exists input :: BehaviorEvalsCode(codeVuln(input),b) && ValidBehaviorNonTrivial(b)
    }


   

    


}