// include "LLVM/llvm.i.dfy" // needs to be re-factored
include "LLVM/llvmREFACTOR.i.dfy" // needs to be re-factored
include "LLVM/control_flow.i.dfy"
include "LLVM/types.dfy"
include "LLVM/Operations/otherOperations.i.dfy"
include "Libraries/Seqs.s.dfy"

abstract module AbstractNonInterferenceProof {
    import opened LLVM_defRE
    import opened control_flow
    import opened Collections__Seqs_s

    // Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
    predicate RemovedBehaviors(b:behavior)

    // Describes/Excludes 'good' added behavior in Patched Code (ie postBehaviors)
    predicate AddedBehaviors(b:behavior)
   
    // The MiniSpec is a predicate over a behavior (finite seq of states [s to s']) 
    predicate MiniSpec(pre:behavior,post:behavior)
    {
        !RemovedBehaviors(pre) && !AddedBehaviors(post)
    }


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


    /*
        for all behaviors, pre(unpatched) and post(patched), such that the following is true:
            Both are a valid sequence of states
            The preBehavior is a valid behavior of the unpatched code
            The postBehavior is a valid behavior of the patched code
            The starting states are the same
            The preBehavior does not include any 'bad' behaviors as expressed in 'RemovedBehaviors'
            **The postBehavior does not include any 'good' added behavior as expressed in 'AddedBehaviors'
        Implies that:
            the final states of both behaviors are the same
    */


    lemma nonInterference(preCode:codeRe,postCode:codeRe)
         ensures forall input,s,pre,post :: (&& ValidState(s)
                                             && validInput(s,input)
                                             && preCode == codeVuln(input)
                                             && postCode == codePatch(input)
                                             && post == extractPatchBehavior(postCode,s,input)
                                             && pre == extractVulnBehavior(preCode,s,input)
                                             && MiniSpec(pre,post))
                                            ==> last(post) == last(pre) // behaviorOutput(post) == behaviorOutput(pre)
            

}










// abstract module AbstractNonInterferenceProof {
//     import opened LLVM_def
//     import opened control_flow


//     predicate MiniSpec(s:LLVM_def.state, s':LLVM_def.state)

//     predicate ModuloMiniSpec(code:lvm_code, s:LLVM_def.state, s':LLVM_def.state,stateSeqS:seq<state>){
//         && BehaviorDescribedByStates(s,s',stateSeqS) 
//         && ValidBehavior(stateSeqS) 
//         && BehaviorEvalsCode(code,stateSeqS)
//         && (forall i :: (i >=0 && i < |stateSeqS|-2) ==> !MiniSpec(stateSeqS[i],stateSeqS[i+1]))
//     }

//     lemma nonInterference(code:lvm_code, code':lvm_code,
//                           s:LLVM_def.state, s':LLVM_def.state, 
//                           r:LLVM_def.state, r':LLVM_def.state)
//         requires evalCode(code, s, s')
//         requires evalCode(code', r, r')
//         ensures forall stateSeqS:seq<state>, stateSeqR:seq<state> 
//                 ::  (&& BehaviorDescribedByStates(s,s',stateSeqS) 
//                     && ValidBehavior(stateSeqS) 
//                     && BehaviorDescribedByStates(r,r',stateSeqR) 
//                     && ValidBehavior(stateSeqR)
//                     && ModuloMiniSpec(code,s,s',stateSeqS)) ==> lvm_state_eq(s',r')
// }








    
