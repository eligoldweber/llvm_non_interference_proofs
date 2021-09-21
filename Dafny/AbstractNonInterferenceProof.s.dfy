include "LLVM/llvm.i.dfy" // needs to be re-factored
include "LLVM/control_flow.i.dfy"
include "LLVM/types.dfy"
include "LLVM/Operations/otherOperations.i.dfy"

abstract module AbstractNonInterferenceProof {
    import opened LLVM_def
    import opened control_flow


    predicate MiniSpec(s:LLVM_def.state, s':LLVM_def.state)

    predicate ModuloMiniSpec(code:lvm_code, s:LLVM_def.state, s':LLVM_def.state,stateSeqS:seq<state>){
        && startAndEndState(s,s',stateSeqS) 
        && ValidStateSeq(stateSeqS) 
        && StateSeqEvalsCode(code,stateSeqS)
        && (forall i :: (i >=0 && i < |stateSeqS|-2) ==> !MiniSpec(stateSeqS[i],stateSeqS[i+1]))
    }

    lemma nonInterference(code:lvm_code, code':lvm_code,
                          s:LLVM_def.state, s':LLVM_def.state, 
                          r:LLVM_def.state, r':LLVM_def.state)
        requires evalCode(code, s, s')
        requires evalCode(code', r, r')
        ensures forall stateSeqS:seq<state>, stateSeqR:seq<state> 
                ::  (&& startAndEndState(s,s',stateSeqS) 
                    && ValidStateSeq(stateSeqS) 
                    && startAndEndState(r,r',stateSeqR) 
                    && ValidStateSeq(stateSeqR)
                    && ModuloMiniSpec(code,s,s',stateSeqS)) ==> lvm_state_eq(s',r')
}



/*
    what is the MiniSpec?
    MiniSpec is a single state predicate that describes incorrect behavior (that is supposedly fixed by the patch)

        This would preclude all exections where there is a state that enters a 'danger' state. but not 
        > necessarily 'act' on it

    MiniSpec is a two-state predicate (s,s') that describes both the incorrect behavior and that incorrect behavior 
    > dictates the state transition from s to s'
        
        This only reasons about the exections where a state s enters a 'danger' state *and* makes the 
        > corresponding transition 
*/
    
