include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Sets.i.dfy"


module simpleBugGeneral{
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i

        // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(a:set<behavior>,b:set<behavior>)
    {
        var aOut := allBehaviorOutputSet(a);
        var bOut := allBehaviorOutputSet(b);
        forall p :: p in bOut ==> p in aOut

    }

  // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(b:set<behavior>)
    {
        forall p :: MiniSpec(p) ==> !(p in b)
    }

    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatch(a:set<behavior>,b:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b

        var aOut := allBehaviorOutputSet(a);
        var bOut := allBehaviorOutputSet(b);
        forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) ==> behaviorOutput(p) in bOut
    }
    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatchMS(a:set<behavior>,b:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b
        var aModuloMS := MakeSubset(a, x => !MiniSpec(x));
        var aOutMS := allBehaviorOutputSet(aModuloMS);
        var bOut := allBehaviorOutputSet(b);
        forall p :: behaviorOutput(p) in aOutMS ==> behaviorOutput(p) in bOut
    }

  predicate safePatch(a:set<behavior>,b:set<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var aOut := allBehaviorOutputSet(a);
        var bOut := allBehaviorOutputSet(b);
        forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) <==> behaviorOutput(p) in bOut
    }

predicate safePatchMS(a:set<behavior>,b:set<behavior>)
    {           
    //  forall p :: (p in a && !MiniSpec(p)) <==> p in b
        var aModuloMS := MakeSubset(a, x => !MiniSpec(x));
        var aOutMS := allBehaviorOutputSet(aModuloMS);
        var bOut := allBehaviorOutputSet(b);
        forall p :: behaviorOutput(p) in aOutMS <==> behaviorOutput(p) in bOut
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

  


    


   

   

    


}