include "System.s.dfy"

abstract module GeneralNonInterferenceProperties {
        import opened System_s

    // Describes 'bad' behavior that a safe patch should prune
    predicate MiniSpec(b:System_s.behavior)
    // {
    //     exists s :: s in b && !s.ok
    // }

// -- 
    // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(a:seq<System_s.behavior>,b:seq<System_s.behavior>)
    {
        // forall p :: p in b ==> p in a
       
        var aOut := allBehaviorOutput(a);
        var bOut := allBehaviorOutput(b);
        forall p :: p in bOut ==> p in aOut

    }

    // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(b:seq<System_s.behavior>)
    {
        forall p :: MiniSpec(p) ==> !(p in b)
       
    }    
    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatch(a:seq<System_s.behavior>,b:seq<System_s.behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b

        var aOut := allBehaviorOutput(a);
        var bOut := allBehaviorOutput(b);
        forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) ==> behaviorOutput(p) in bOut
    }

    //     // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    // predicate successfulPatch_Restricted(a:seq<System_s.behavior>,b:seq<System_s.behavior>)
    // {
    //     // forall p :: p in a && MiniSpec(p) ==> !(p in b)
    //     var aOut := allBehaviorOutput(a);
    //     var bOut := allBehaviorOutput(b);
    //     forall p :: (behaviorOutput(p) in aOut && MiniSpec(p)) ==> !(behaviorOutput(p) in bOut)

    // }
    
    // The conjuntion of benign, successful and complete imply that; that after apply the patch, b retains all good behavior from a and 
    // is pruned of all bad behavior. 
    predicate safePatch(a:seq<System_s.behavior>,b:seq<System_s.behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var aOut := allBehaviorOutput(a);
        var bOut := allBehaviorOutput(b);
        forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) <==> behaviorOutput(p) in bOut
    }

    lemma fullPatch(a:seq<System_s.behavior>,b:seq<System_s.behavior>)
        requires benignPatch(a,b);
        requires successfulPatch(b);
        requires completePatch(a,b);
        ensures safePatch(a,b);
        // {
        //     var aOut := allBehaviorOutput(a);
        //     var bOut := allBehaviorOutput(b);
        //     assert forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) <==> behaviorOutput(p) in bOut;
        // }


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