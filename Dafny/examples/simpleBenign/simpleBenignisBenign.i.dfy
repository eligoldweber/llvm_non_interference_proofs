include "BenignCode.s.dfy"
include "simpleBenignCommon.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBenignIsBenign{
    import opened simpleBenignCode
    import opened simpleBenignCommon
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s


    lemma unwrapPatchSOIBehaviors(s:state, input:operand) returns (b:behavior) 
        requires ValidState(s);
        requires SOI_ASSIMPTIONS(s);
    {
        reveal_ValidBehavior();
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";
    
        var c := benign_patch_SOI(s);
        // var if_end := Block([
        // Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        // IfElse(true,if_then3().block,if_end4().block)]);

        assert OperandContents(s,var_0).Int?;
        assert OperandContents(s,var_0).val >= 2147483646;


        assert |c.block| == 2;

        b := [s] + evalCodeRE(c,s);
       
        var step,remainder,subBehavior := unwrapBlockWitness(b,c.block,s);

        assert b[0] == s;

        assert ValidInstruction(s,ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false)))));
        assert NextStep(b[0],b[1],Step.evalInsStep(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))));
        assert StateNext(b[0],b[1]);

        assert step == [b[1]];
        assert remainder == [IfElse(true,if_then3().block,if_end4().block)];
        assert subBehavior == b[1..];
        assert first(remainder).IfElse?;
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        assert step == [b[1]];
        assert remainder == if_then3().block;
        assert subBehavior == [b[1]] + evalBlockRE(remainder, b[1]); // no state change, just control flow

        assert first(remainder).Ins?;
        assert first(remainder).ins == CALL(D(Void),printf_code(global_str()).block);
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        

        assert step == [b[2]];
        assert b[2] == evalInsRe(CALL(D(Void),printf_code(global_str()).block),b[1]);
        unwrapPrintf(b[1],b[2],global_str());
        assert NextStep(b[1],b[2],Step.evalInsStep(CALL(D(Void),printf_code(global_str()).block)));
        assert StateNext(b[1],b[2]); 
        assert remainder == [if_end4()];
        assert first(remainder).Block?;
        assert subBehavior == [b[2]] + evalBlockRE(remainder, b[2]);

        
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert step == [b[2]];
        assert remainder == if_end4().block;
        assert subBehavior == [b[2]] + evalBlockRE(remainder, b[2]); // no state change, just control flow

        assert first(remainder).Ins?;
        assert first(remainder).ins == CALL(D(Void),printf_code(global_str1()).block);

        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert step == [b[3]];
        assert b[3] == evalInsRe(CALL(D(Void),printf_code(global_str1()).block),b[2]);
        unwrapPrintf(b[2],b[3],global_str1());
        assert NextStep(b[2],b[3],Step.evalInsStep(CALL(D(Void),printf_code(global_str1()).block)));
        assert StateNext(b[2],b[3]); 
        assert remainder == [return_()];
        assert first(remainder).Block?;
        assert subBehavior == [b[3]] + evalBlockRE(remainder, b[3]);

        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert step == [b[3]];
        assert remainder == return_().block;
        assert subBehavior == [b[3]] + evalBlockRE(remainder, b[3]);// no state change, just control flow

        assert first(remainder).Ins?;
        assert first(remainder).ins == RET(D(Void));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert step == [b[4]];
        assert b[4] == evalInsRe(RET(D(Void)),b[3]);
        assert NextStep(b[3],b[4],Step.evalInsStep(RET(D(Void))));
        assert StateNext(b[3],b[4]);

        assert remainder == [];
        assert subBehavior == [b[4]] + evalBlockRE(remainder, b[4]);
        assert NextStep(b[4],b[5],Step.stutterStep());
        // assert |b| == 7;
        assert ValidBehavior(b);
    
    }
}