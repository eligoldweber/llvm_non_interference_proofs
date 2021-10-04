include "LLVM/llvm.i.dfy" // needs to be re-factored
include "LLVM/control_flow.i.dfy"
include "LLVM/types.dfy"
include "LLVM/Operations/otherOperations.i.dfy"

abstract module AbstractNonInterferenceProof {
    import opened LLVM_def
    import opened control_flow


    predicate MiniSpec(s:LLVM_def.state, s':LLVM_def.state)

    predicate ModuloMiniSpec(code:lvm_code, s:LLVM_def.state, s':LLVM_def.state,stateSeqS:seq<state>){
        && BehaviorDescribedByStates(s,s',stateSeqS) 
        && ValidBehavior(stateSeqS) 
        && BehaviorEvalsCode(code,stateSeqS)
        && (forall i :: (i >=0 && i < |stateSeqS|-2) ==> !MiniSpec(stateSeqS[i],stateSeqS[i+1]))
    }

    lemma nonInterference(code:lvm_code, code':lvm_code,
                          s:LLVM_def.state, s':LLVM_def.state, 
                          r:LLVM_def.state, r':LLVM_def.state)
        requires evalCode(code, s, s')
        requires evalCode(code', r, r')
        ensures forall stateSeqS:seq<state>, stateSeqR:seq<state> 
                ::  (&& BehaviorDescribedByStates(s,s',stateSeqS) 
                    && ValidBehavior(stateSeqS) 
                    && BehaviorDescribedByStates(r,r',stateSeqR) 
                    && ValidBehavior(stateSeqR)
                    && ModuloMiniSpec(code,s,s',stateSeqS)) ==> lvm_state_eq(s',r')
}

abstract module UpdatedAbstractNonInterferenceProof {
    import opened LLVM_def
    import opened control_flow

    // Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
    predicate RemovedBehaviors(b:behavior)

    // Describes/Excludes 'good' added behavior in Patched Code (ie postBehaviors)
    // [TODO] fix :: This is a placeholder for now -- ie this allows all executions of the patched code
    predicate AddedBehaviors(b:behavior)
    {
        false
    }

    // The MiniSpec is a predicate over a behavior (finite seq of states [s to s']) 
    predicate MiniSpec(b:behaviors)
    {
        match b
            case preBehavior(preB) => RemovedBehaviors(preB)
            case postBehavior(postB) => AddedBehaviors(postB)
    }

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
    lemma nonInterference(preCode:lvm_code, postCode:lvm_code)
        ensures forall pre:behavior, post:behavior ::
                   (&& ValidBehavior(pre) 
                    && ValidBehavior(post)  
                    && BehaviorEvalsCode(preCode,pre) 
                    && BehaviorEvalsCode(postCode,post)
                    && pre[0] == post[0] 
                    && !MiniSpec(preBehavior(pre))
                    && !MiniSpec(postBehavior(post)))
                    ==> lvm_state_eq(pre[|pre|-1],post[|post|-1])


}


/*


    predicate ModuloMiniSpec(code:lvm_code,b:behaviors)
    {
        var behavior := getBehavior(b);
        (ValidBehavior(behavior) && BehaviorEvalsCode(code,behavior)) ==> !MiniSpec(b)
    }



/////
    MiniSpec is a predicate over a behavior (finite seq of states [s to s']) that describes an incorrect action

/////
    MiniSpec is a two-state predicate (s,s') that describes both the incorrect behavior and that incorrect behavior 
    > dictates the state transition from s to s'
        
        This only reasons about the exections where a state s enters a 'danger' state *and* makes the 
        > corresponding transition 

//////        
    what is the MiniSpec?
    MiniSpec is a single state predicate that describes incorrect behavior (that is supposedly fixed by the patch)

        This would describe/preclude all exections where there is a state that enters a 'danger' or buggy state. but not 
        > necessarily 'acts' on it


*/
    
