include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBugGeneral{
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened Collections__Sets_i

        // benignPatch: "The patch does not add any NEW behaviors"
    predicate benignPatch(a:seq<behavior>,b:seq<behavior>)
    {
        var aOut := allBehaviorOutput(a);
        var bOut := allBehaviorOutput(b);
        forall p :: p in bOut ==> p in aOut

    }

  // successfulPatch: "The patch prunes the BAD (defined by MiniSpec) behaviors"
    predicate successfulPatch(b:seq<behavior>)
    {
        forall p :: MiniSpec(p) ==> !(p in b)
    }

    // completePatch: "The patch preserves the GOOD behavior" // Name; complete -> preserving ? 
    predicate completePatch(a:seq<behavior>,b:seq<behavior>)
    {
        // forall p :: (p in a && !MiniSpec(p)) ==> p in b

        var aOut := allBehaviorOutput(a);
        var bOut := allBehaviorOutput(b);
        forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) ==> behaviorOutput(p) in bOut
    }


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