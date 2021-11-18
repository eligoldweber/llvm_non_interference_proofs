include "System.s.dfy"

abstract module GeneralNonInterferenceProperties {
        import opened System_s

    // datatype abstractState = abstractState(ok:bool)

    // type abstractBehavior = seq<abstractState>

    // Describes 'bad' behavior that a safe patch should prune
    predicate MiniSpec(b:behavior)
    // {
    //     exists s :: s in b && !s.ok
    // }

// -- 
    // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(a:set<behavior>,b:set<behavior>)
    {
        forall p :: p in b ==> p in a
    }

    // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(b:set<behavior>)
    {
        forall p :: MiniSpec(p) ==> !(p in b)
    }
    
    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatch(a:set<behavior>,b:set<behavior>)
    {
        forall p :: (p in a && !MiniSpec(p)) ==> p in b
    }

    // The conjuntion of benign, successful and complete imply that; that after apply the patch, b retains all good behavior from a and 
    // is pruned of all bad behavior. 
    predicate safePatch(a:set<behavior>,b:set<behavior>)
    {
        //assert benignPatch(a,b) && successfulPatch(b) && completePatch(a,b) ==> 
        forall p :: (p in a && !MiniSpec(p)) <==> p in b
    }

    lemma fullPatch(a:set<behavior>,b:set<behavior>)
        requires benignPatch(a,b);
        requires successfulPatch(b);
        requires completePatch(a,b);
        ensures safePatch(a,b);
        // {
        //     assert (forall p :: (p in a && !MiniSpec(p)) <==> p in b);
        // }


//// Helping General Functions

    function codePatch(input:operand):(out:codeRe)

    function codeVuln(input:operand):(out:codeRe)

    predicate validInput(s:state, input:operand)
        requires ValidState(s)

    function extractPatchBehavior(c:codeRe,s:state,input:operand) : (b:behavior)
        requires ValidState(s);
        requires c == codePatch(input);
        requires validInput(s,input);
        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(c,b);


    function extractVulnBehavior(c:codeRe,s:state,input:operand) : (b:behavior)
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