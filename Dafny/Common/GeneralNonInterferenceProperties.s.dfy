include "System.s.dfy"
include "../Libraries/Sets.i.dfy"

abstract module GeneralNonInterferenceProperties {
        import opened System_s
        import opened Collections__Sets_i


    predicate RemovedBehaviors(b:System_s.behavior)
    
    // Describes 'bad' behavior that a safe patch should prune
    predicate MiniSpec(b:System_s.behavior)
    {
        RemovedBehaviors(b)
    }

// -- 
    // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    {
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall postB :: postB in postOutput ==> postB in preOutput
    }

    // // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(post:set<System_s.behavior>)
    {
        forall postB :: MiniSpec(postB) ==> !(postB in post)
    }

    // // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b

        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) ==> behaviorOutput(preB) in postOutput
    }
    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatchMS(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b
        var preModMs := MakeSubset(pre, x => !MiniSpec(x));
        var preModMsOut := allBehaviorOutputSet(preModMs);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: behaviorOutput(preB) in preModMsOut ==> behaviorOutput(preB) in postOutput
    }

    
    // // The conjuntion of benign, successful and complete imply that; that after apply the patch, b retains all good behavior from a and 
    // // is pruned of all bad behavior. 

    predicate safePatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var preOutput := allBehaviorOutputSet(pre);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) <==> behaviorOutput(preB) in postOutput
    }

    predicate safePatchMS(pre:set<System_s.behavior>,post:set<System_s.behavior>)
    {           
    //  forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var preModMs := MakeSubset(pre, x => !MiniSpec(x));
        var preModMsOut := allBehaviorOutputSet(preModMs);
        var postOutput := allBehaviorOutputSet(post);
        forall preB :: behaviorOutput(preB) in preModMsOut <==> behaviorOutput(preB) in postOutput
    } 

    lemma fullPatch(pre:set<System_s.behavior>,post:set<System_s.behavior>)
        requires benignPatch(pre,post);
        requires successfulPatch(post);
        requires completePatchMS(pre,post);
        ensures safePatchMS(pre,post);



//// Other General Functions

    function codePatch(input:System_s.operand):(out:System_s.codeRe)

    function codeVuln(input:System_s.operand):(out:System_s.codeRe)

    predicate validInput(s:System_s.state, input:System_s.operand)
        requires ValidState(s)

    function extractPatchBehavior(c:System_s.codeRe,s:System_s.state,input:System_s.operand) : (b:System_s.behavior)
        requires ValidState(s);
        requires c == codePatch(input);
        requires validInput(s,input);
        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(c,b);


    function extractVulnBehavior(c:System_s.codeRe,s:System_s.state,input:System_s.operand) : (b:System_s.behavior)
        requires ValidState(s);
        requires c == codeVuln(input);
        requires validInput(s,input);
        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(c,b);



// ** DAC only reasons about 'completePatch' rather than the biconditional
    // lemma DAC(a:set<abstractBehavior>,b:set<abstractBehavior>)
    // {
    //     assert completePatch(a,b) ==> (forall p :: (p in a && !MiniSpec(p)) ==> p in b);
    // }

// -- 


    // predicate benignPatch(a:set<abstractBehavior>,b:set<abstractBehavior>)
    // {
    //     forall p :: p in b ==> p in a
    // }

    // predicate successfulPatch(MiniSpec:set<abstractBehavior>,b:set<abstractBehavior>)
    // {
    //     forall p :: p in MiniSpec ==> !(p in b)
    // }

    // predicate completePatch(a:set<abstractBehavior>,b:set<abstractBehavior>,MiniSpec:set<abstractBehavior>)
    // {
    //     forall p :: (p in a && !(p in MiniSpec)) ==> p in b
    // }

    // lemma safePatch(a:set<abstractBehavior>,b:set<abstractBehavior>,MiniSpec:set<abstractBehavior>)
    // {
    //     assert benignPatch(a,b) && successfulPatch(MiniSpec,b) ==> (forall p :: p in b ==> (p in a && !(p in MiniSpec)));
    //     assert benignPatch(a,b) && successfulPatch(MiniSpec,b) && completePatch(a,b,MiniSpec) ==> (forall p :: (p in a && !(p in MiniSpec)) <==> p in b);
    // }

// -- 

}