include "BenignCode.s.dfy"
include "simpleBenignCommon.i.dfy"
include "../../LLVM/llvmREFACTOR_Multi.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBenignIsBenign{
    import opened simpleBenignCode
    import opened simpleBenignCommon
    import opened LLVM_defRE_Multi
    import opened types
    import opened Collections__Seqs_s


lemma unwrapMultiBehaviors(var_x:operand,s:state,patched:bool) returns (b:behavior) 
        requires ValidState(s);
        requires SOI_ASSIMPTIONS(s);
        requires ValidOperand(s,var_x);
        requires isInt(OperandContents(s,var_x))
        requires OperandContents(s,var_x).itype.size == 4;
        requires !OperandContents(s,var_x).itype.signed
        requires OperandContents(s,var_x).val == 2 ==> patched

        
        // ensures exists var_cmp2:operand :: var_cmp2.LV? && var_cmp2.l in s.lvs && var_cmp2.l == "var_cmp2";
        ensures b == [s] + evalCodeRE(MergedTest(var_x,s,patched),s);
        // ensures ValidBehavior(b);
        // ensures forall r :: (ValidState(r) && SOI_ASSIMPTIONS(r) && s != r) ==> b == ([s] + evalCodeRE(benign_patch_SOI(r),r))
    {
        reveal_ValidBehavior();
         var var_cmp2 := LV(" var_cmp2 ");
        var var_add := LV(" var_add ");
        var var_z := LV(" var_z ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";
    
        var c := MergedTest(var_x,s,patched);
        // var if_end := Block([
        // Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        // IfElse(true,if_then3().block,if_end4().block)]);

        assert OperandContents(s,var_0).Int?;
        assert OperandContents(s,var_0).val >= 2147483646;


        assert |c.block| == 3;

        b := [s] + evalCodeRE(c,s);
        var step,remainder,subBehavior := unwrapBlockWitness(b,c.block,s);
         assert b[0] == s;
        // Ins(ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false)))))
        assert (var_add.LV? || var_add.GV?);
        assert ValidOperand(s,var_x);
        assert ValidOperand(s,D(Int(2147483646,IntType(4,false))));
        assert isInt(OperandContents(s,var_x));// && isInt(OperandContents(s,D(Int(2147483646,IntType(4,false)))));
        //&& typesMatch(OperandContents(s,var_x),OperandContents(s,D(Int(2147483646,IntType(4,false)))));
        assert ValidInstruction(s,ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false)))));
        assert NextStep(b[0],b[1],Step.evalInsStep(ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false))))));
        // assert OperandContents(b[0],var_0).val > 
        assert StateNext(b[0],b[1]);
        assert step == [b[1]];
        assert remainder == [Divergence([Ins(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false)))))], [Ins(ICMP(var_cmp2,ugt,4,var_add,D(Int(0,IntType(4,false)))))],patched),
        IfElse(var_cmp2,if_then3().block,if_end4().block)];
        assert first(remainder).Divergence?;
        assert subBehavior == b[1..];
        assert subBehavior == [b[1]] + evalBlockRE(remainder, b[1]); // no state change, just control flow
        assert b[2..] == evalBlockRE(remainder, b[1]);


        var tempB := evalCodeRE(first(remainder),b[1]);
        assert evalBlockRE(remainder, b[1]) == evalCodeRE(first(remainder),b[1]) + evalBlockRE(all_but_first(remainder),last(tempB));
        if patched{

        }else{
            assert !patched ==> evalCodeRE(first(remainder),b[1]) == evalBlockRE(first(remainder).pre,b[1]);

            assert subBehavior == [b[1]] + evalBlockRE(first(remainder).pre,b[1]) + evalBlockRE(all_but_first(remainder),last(tempB));

            assert b[1] in subBehavior;
            assert first(evalBlockRE(first(remainder).pre,b[1])) == b[2];
            assert |first(remainder).pre| == 1;//Ins?;
            assert first(remainder).pre[0].Ins?;
            var oldRemainder := remainder;
              //  assert evalBlockRE(first(remainder).pre,b[1]) == [evalInsRe(first(remainder).pre[0].ins,b[1])];
        // assert forall c :: (c >= 0 && c < |evalBlockRE(first(remainder).pre,b[1])|) ==> evalBlockRE(first(remainder).pre,b[1])[c] == b[2+c];

        // assert first(remainder) 
        
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        assert step == [b[1]];//evalCodeRE(Divergence([Ins(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false)))))], [Ins(ICMP(var_cmp2,ugt,4,var_add,D(Int(0,IntType(4,false)))))],false),b[1]);
                // step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        // assert remainder == [Ins(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false)))))] + 
        //                      [IfElse(var_cmp2,if_then3().block,if_end4().block)];
        // // assert subBehavior == [b[1]] + evalBlockRE(remainder, b[1]); // no state change, just control flow
        // //          assert all_but_first(oldRemainder) == all_but_first(remainder);
        // //          tempB := evalCodeRE(first(remainder),b[1]);
        // //          assert last(tempB) == b[1];
        // //          assert first(oldRemainder).pre == [first(remainder)];
        // //         //  assert evalBlockRE(first(oldRemainder).pre,b[1]) == evalBlockRE(first(remainder),b[1]) ;
        // //          assert subBehavior == [b[1]] + evalCodeRE(first(remainder),b[1]) + evalBlockRE(all_but_first(remainder),last(tempB));

        // // assert subBehavior == b[1..];
        // // // assert first(b[1..]) == b[1];
        // // assert first(remainder).Ins?;
 
        // // assert all_but_first(remainder) == [IfElse(var_cmp2,if_then3().block,if_end4().block)];
        // // assert first(remainder).ins == ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false))));


        // step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        // assert ValidInstruction(b[1],ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false)))));
        // assert NextStep(b[1],b[2],Step.evalInsStep(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false))))));
        // // assert OperandContents(b[0],var_0).val > 
        // assert StateNext(b[1],b[2]);

        // assert step == [b[2]];
        // assert remainder == [IfElse(var_cmp2,if_then3().block,if_end4().block)];
        // // // assert subBehavior == b[1..];
        // // assert first(remainder).IfElse?;
        // assert validIfCond(last(step),first(remainder).ifCond);
        // // // assert dataToBool(OperandContents(last(step),first(remainder).ifCond));
        // if dataToBool(OperandContents(last(step),first(remainder).ifCond)){ // True Branch
        //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        //     assert step == [b[2]];
        //     assert remainder == if_then3().block;
        //     assert subBehavior == [b[2]] + evalBlockRE(remainder, b[2]); // no state change, just control flow

        //     assert first(remainder).Ins?;
        //     assert first(remainder).ins == CALL(D(Void),printf_code(global_str()).block);
        // //     // assert 
        //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        // //     assert |step| == 1;
        //     // assert step == evalCodeRE(Ins(CALL(D(Void),printf_code(global_str()).block)),b[2]);
        //     // assert step == [b[2]];
        //     assert (step) == [evalInsRe(CALL(D(Void),printf_code(global_str()).block),b[2])];
        //                 //  assert step == [b[3]];

        // //     // unwrapPrintf(b[2],b[3],global_str());
        // //     // assert NextStep(b[2],b[3],Step.evalInsStep(CALL(D(Void),printf_code(global_str()).block)));
        // //     // assert StateNext(b[2],b[3]); 
        // //     assert remainder == [if_end4()];
        // //     assert first(remainder).Block?;
        // //     // assert subBehavior == [b[3]] + evalBlockRE(remainder, b[3]);

            
        // //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        // //     // assert step == [b[3]];
        // //     assert remainder == if_end4().block;
        // //     // assert subBehavior == [b[3]] + evalBlockRE(remainder, b[3]); // no state change, just control flow

        // }
        }
        
      

    }

    lemma unwrapPatchSOIBehaviors(s:state) returns (b:behavior) 
        requires ValidState(s);
        requires SOI_ASSIMPTIONS(s);
        // ensures exists var_cmp2:operand :: var_cmp2.LV? && var_cmp2.l in s.lvs && var_cmp2.l == "var_cmp2";
        ensures b == [s] + evalCodeRE(benign_patch_SOI(s),s);
        // ensures ValidBehavior(b);
        // ensures forall r :: (ValidState(r) && SOI_ASSIMPTIONS(r) && s != r) ==> b == ([s] + evalCodeRE(benign_patch_SOI(r),r))
    {
        reveal_ValidBehavior();
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";
    
        var c := benign_patch_SOI(s);
        // var if_end := Block([
        // Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        // IfElse(true,if_then3().block,if_end4().block)]);

        assert OperandContents(s,var_0).Int?;
        assert OperandContents(s,var_0).itype.size == 4;
        assert OperandContents(s,var_0).val >= 2147483646;


        assert |c.block| == 2;

        b := [s] + evalCodeRE(c,s);
       
        var step,remainder,subBehavior := unwrapBlockWitness(b,c.block,s);

        assert b[0] == s;

        assert ValidInstruction(s,ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false)))));
        assert NextStep(b[0],b[1],Step.evalInsStep(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))));
        // assert OperandContents(b[0],var_0).val > 
        assert StateNext(b[0],b[1]);

        assert step == [b[1]];
        assert remainder == [IfElse(var_cmp2,if_then3().block,if_end4().block)];
        assert subBehavior == b[1..];
        assert first(remainder).IfElse?;
        assert validIfCond(last(step),first(remainder).ifCond);
        assert dataToBool(OperandContents(last(step),first(remainder).ifCond));
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
        // step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        // assert NextStep(b[5],b[6],Step.stutterStep());
        //   step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        // assert |b| == 7;
        assert |b| >  |[b[0],b[1],b[2],b[3],b[4]]|;
        var simplified := Block([Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
                            Ins(CALL(D(Void),printf_code(global_str()).block)),
                            Ins(CALL(D(Void),printf_code(global_str1()).block)),
                            Ins(RET(D(Void)))]);

        assert s == b[0];
        assert NextStep(b[0],b[1],Step.evalInsStep(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))));
        assert StateNext(b[0],b[1]);
        assert NextStep(b[1],b[2],Step.evalInsStep(CALL(D(Void),printf_code(global_str()).block)));
        assert StateNext(b[1],b[2]); 
        assert NextStep(b[2],b[3],Step.evalInsStep(CALL(D(Void),printf_code(global_str1()).block)));
        assert StateNext(b[2],b[3]); 
        assert NextStep(b[3],b[4],Step.evalInsStep(RET(D(Void))));
        assert StateNext(b[3],b[4]);
        assert NextStep(b[4],b[5],Step.stutterStep());
        assert StateNext(b[4],b[5]);
        // assert [s] + evalCodeRE(simplified,s) == [b[0],b[1],b[2],b[3],b[4],b[5]];

        // assert evalCodeRE(Block([Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false)))))]),s)
        assert ValidBehavior(b);
    
    }

    // lemma PatchAlwaysIsCorrect()
    // {
    //      forall s:state | ValidState(s) && SOI_ASSIMPTIONS(s)
    //         // ensures behaviorOutput(postB) == validBehaviorsOuts();
    //     {
    //         var b := uunwrapPatchSOIBehaviors(s);
    //         assert dataToBool(OperandContents(b[1],IfElse(var_cmp2,if_then3().block,if_end4().block).ifCond)); 
    //     }
    // }


    lemma unwrapVulnSOIBehaviors(s:state) returns (b:behavior) 
        requires ValidState(s);
        requires SOI_ASSIMPTIONS(s);
    {
        reveal_ValidBehavior();
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";
    
        var c := benign_vuln_SOI(s);
        // var if_end := Block([
        // Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        // IfElse(true,if_then3().block,if_end4().block)]);

        assert OperandContents(s,var_0).Int?;
        assert OperandContents(s,var_0).val >= 2147483646;


        assert |c.block| == 2;

        b := [s] + evalCodeRE(c,s);
       
        var step,remainder,subBehavior := unwrapBlockWitness(b,c.block,s);

        assert b[0] == s;

        assert ValidInstruction(s,ICMP(var_cmp2,sgt,4,var_0,D(Int(0,IntType(4,false)))));
        assert NextStep(b[0],b[1],Step.evalInsStep(ICMP(var_cmp2,sgt,4,var_0,D(Int(0,IntType(4,false))))));
        // assert OperandContents(b[0],var_0).val > 
        assert StateNext(b[0],b[1]);

        assert step == [b[1]];
        assert remainder == [IfElse(var_cmp2,if_then3().block,if_end4().block)];
        assert subBehavior == b[1..];
        assert first(remainder).IfElse?;
        assert validIfCond(last(step),first(remainder).ifCond);
        // assert dataToBool(OperandContents(last(step),first(remainder).ifCond));
        if dataToBool(OperandContents(last(step),first(remainder).ifCond)){ // True Branch
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

            assert step == [b[1]];
            assert remainder == if_then3().block;
            assert subBehavior == [b[1]] + evalBlockRE(remainder, b[1]); // no state change, just control flow
            // assert subBehavior == b[1..];

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
            assert ValidBehavior(b);
        }else{ //FALSE BRANCH
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

            assert step == [b[1]];
            assert remainder == if_end4().block;
            assert subBehavior == [b[1]] + evalBlockRE(remainder, b[1]); // no state change, just control flow
            assert first(remainder).Ins?;
            assert first(remainder).ins == CALL(D(Void),printf_code(global_str1()).block);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            assert step == [b[2]];
            assert b[2] == evalInsRe(CALL(D(Void),printf_code(global_str1()).block),b[1]);
            unwrapPrintf(b[1],b[2],global_str1());
            assert NextStep(b[1],b[2],Step.evalInsStep(CALL(D(Void),printf_code(global_str1()).block)));
            assert StateNext(b[1],b[2]); 
            assert remainder == [return_()];
            assert first(remainder).Block?;
            assert subBehavior == [b[2]] + evalBlockRE(remainder, b[2]);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            assert step == [b[2]];
            assert remainder == return_().block;
            assert subBehavior == [b[2]] + evalBlockRE(remainder, b[2]);// no state change, just control flow

            assert first(remainder).Ins?;
            assert first(remainder).ins == RET(D(Void));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            assert step == [b[3]];
            assert b[3] == evalInsRe(RET(D(Void)),b[2]);
            assert NextStep(b[2],b[3],Step.evalInsStep(RET(D(Void))));
            assert StateNext(b[2],b[3]);

            assert remainder == [];
            assert subBehavior == [b[3]] + evalBlockRE(remainder, b[3]);
            assert NextStep(b[3],b[4],Step.stutterStep());
            assert ValidBehavior(b);
            
        }
       
    
    }

    // lemma PatchAlwaysIsCorrect()
    // {
    //     forall s,r | ValidState(s) && SOI_ASSIMPTIONS(s) && ValidState(r) && SOI_ASSIMPTIONS(r) 
    //         // ensures behaviorOutput(postB) == validBehaviorsOuts();
    //     {
    //         var b_patch := unwrapPatchSOIBehaviors(s);
    //         var b_vuln := unwrapPatchSOIBehaviors(r);

    //         // assert b_patch == b_vuln;
    //     }


    //      forall s:state | ValidState(s) && SOI_ASSIMPTIONS(s) && s.lvs["var_0"].val == 2147483646
    //         // ensures behaviorOutput(postB) == validBehaviorsOuts();
    //     {
    //         var b_patch := unwrapPatchSOIBehaviors(s);
    //         var b_vuln := unwrapVulnSOIBehaviors(s);

    //         assert b_patch == b_vuln;
    //     }
    // }


}