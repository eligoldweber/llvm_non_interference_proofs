//// TEST EXAMPLES
include "./AbstractNonInterferenceProof.s.dfy" 
include "LLVM/control_flow.i.dfy"
include "LLVM/types.s.dfy"

module challenge5 refines AbstractNonInterferenceProof {
    import opened types
    import opened other_operations_i
    
    
     function {:opaque} encrypt(plainText:Data):codes
    {
        ForeignFunction
    }

    predicate MiniSpec(s:LLVM_def.state, s':LLVM_def.state)
    {
        reveal_encrypt();

        && StateNext(s,s') 
        && forall plainText :: evalBlock(encrypt(plainText),s,s') ==> s == s'
    }
    

        
    predicate MiniSpecCH_P1Single(s:LLVM_def.state)
    {
        && ValidState(s) 
        && (exists speed_value:operand ::
            (   && speed_value.LV?
                && ValidOperand(s,speed_value)
                && OperandContents(s,speed_value).Int?
                && typesMatch(OperandContents(s,speed_value),Int(0,IntType(2,false)))
                && OperandContents(s,speed_value).val > 0 
                && evalICMP(sgt,2,OperandContents(s,speed_value),Int(0,IntType(2,false))).val == 0))

    }

    predicate ModuloMiniCH_P1Single(code:lvm_code, stateSeq:seq<state>)
    {
        && StateSeqEvalsCode(code,stateSeq)
        && (forall i :: (i >=0 && i <|stateSeq|) ==> !MiniSpecCH_P1Single(stateSeq[i]))
    }



    predicate MiniSpecCH_P1Double(s:LLVM_def.state, s':LLVM_def.state)
    {
        && MiniSpecCH_P1Single(s)
        && StateNext(s,s') 
        && s != s'
        && exists cmp:ins :: (cmp.ICMP? && ValidInstruction(s,cmp) && evalIns(cmp, s, s'))
    }

    predicate ModuloMiniCH_P1Double(code:lvm_code, stateSeq:seq<state>)
    {
        && StateSeqEvalsCode(code,stateSeq)
        && (forall i :: (i >=0 && i <|stateSeq|-2) ==> !MiniSpecCH_P1Double(stateSeq[i],stateSeq[i+1]))
    }


    lemma nonInterferenceCH_P1Single(code:lvm_code, code':lvm_code,
                          s:LLVM_def.state, s':LLVM_def.state, 
                          r:LLVM_def.state, r':LLVM_def.state)
        requires evalCode(code, s, s')
        requires evalCode(code', r, r')
        ensures forall stateSeqS:seq<state>, stateSeqR:seq<state> 
                ::  (&& startAndEndState(s,s',stateSeqS) 
                    && ValidBehavior(stateSeqS) 
                    && startAndEndState(r,r',stateSeqR) 
                    && ValidBehavior(stateSeqR)
                    && ModuloMiniCH_P1Double(code,stateSeqS)) ==> lvm_state_eq(s',r') //might need to compare full seq?   
                    // {

                    // }

}