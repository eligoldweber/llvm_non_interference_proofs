include "BenignCode.s.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBenignIsBenign{
    import opened simpleBenignCode
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s


    lemma unwrapPatchBehaviors(s:state, input:operand) returns (b:behavior) 
        requires ValidState(s);
        requires validStartingState(s);
    {
        var var_z := LV(" var_z ");
        var var_cmp := LV(" var_cmp ");
        var var_cmp1 := LV(" var_cmp1 ");
        var var_add := LV(" var_add ");
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0 := LV(" var_0 ");
    
        //reveal_BehaviorEvalsCode();
        var c := benign_patch_code(input);

        assert |c.block| == 3;

        b := [s] + evalCodeRE(c,s);
        var step,remainder,subBehavior := unwrapBlockWitness(b,c.block,s);

        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            

        //var var_z:LV := s.lvs["var_z"];

        assert b[0] == s;
        assert "var_z" in s.lvs;
        assert c.block[0] == Ins(ALLOCA(var_z,4));
        //
        assert b[1] == evalInsRe(ALLOCA(var_z,4),s);
        assert ValidInstruction(s,ALLOCA(var_z,4));
        assert StateNext(b[0],b[1]);
        //assert ValidOperand(b[1],call);


    }
}