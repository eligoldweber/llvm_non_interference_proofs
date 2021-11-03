
include "../AbstractNonInterferenceProof.s.dfy"
include "llvmREFACTOR.i.dfy"
include "./types.dfy"
include "./Operations/binaryOperations.i.dfy"
include "../Libraries/Seqs.s.dfy"


module basicNonInterferenceExample refines AbstractNonInterferenceProof{
    import opened types
    import opened binary_operations_i

//Simpliefied Challenge Problem 1 code

// lvm_Block(lvm_Codes(Ins(GETELEMENTPTR(var_5,1,var_0,index3)),                         // %5 = getelementptr inbounds i8, i8* %0, i64 3
//               lvm_Codes(Ins(LOAD(var_6,1,var_5)),                                       // %6 = load i8, i8* %2, align 1, !tbaa !4
//               lvm_Codes(Ins(ZEXT(var_7,1,var_6,2)),                                       // %7 = zext i8 %3 to i16
//               lvm_Codes(Ins(SHL(var_8,var_7,shl_amount)),                                 // %8 = shl i16 %7, 8
//               lvm_Codes(Ins(GETELEMENTPTR(var_10,1,var_0,index2)),                        // %10 = getelementptr inbounds i8, i8* %0, i64 2
//               lvm_Codes(Ins(LOAD(var_11,1,var_10)),                                     // %11 = load i8, i8* %10, align 1
//               lvm_Codes(Ins(ZEXT(var_12,1,var_11,2)),                                     // %12 = zext i8 %11 to i16
//               lvm_Codes(Ins(ADD(speed_value,2,var_8,var_12)),                             // %13 = add nsw i16 %8, %12
//               lvm_Codes(Ins(ICMP(var_17,ugt,2,speed_value,D(Int(0,IntType(2,false))))),   // %17 = icmp ugt i16 %13, 0  <--------
//               lvm_Codes(Ins(RET(D(Void))),lvm_CNil())))))))))))    

// ---- Code representation ----
    function codePatch(input:operand):(out:codeRe)
        ensures out.Block?;
        ensures forall c :: c in out.block ==> c.Ins?;
    {
        var speed_value := LV("speed_value");
        var result := LV("result");

        var op1 := D(Int(0,IntType(2,false)));

        var cSeq := [Ins(ADD(speed_value,2,op1,input)),
                     Ins(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }

    function codeVuln(input:operand):codeRe
    {
        var speed_value := LV("speed_value");
        var result := LV("result");

        var op1 := D(Int(0,IntType(2,false)));

        var cSeq := [Ins(ADD(speed_value,2,op1,input)),
                     Ins(ICMP(result,sgt,2,speed_value,D(Int(0,IntType(2,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }

// ---- Extract behavior  ----

    predicate validInput(s:state, input:operand)
    {
        && s.output == []
        && ValidOperand(s,input)
        && isInt(OperandContents(s,input))
        && typesMatch(OperandContents(s,D(Int(0,IntType(2,false)))),OperandContents(s,input))
    }

    // lemma unwrapPatchBehaviorTest(c:codeRe,s:state, input:operand) returns (b:behavior)
    //     requires ValidState(s);
    //     requires c == codePatch(input);

    //     // -- input is valid -- ie. valid 16 bit integer 
    //     requires validInput(s,input);
    //     ensures |b| == 4;
    //     ensures b[0] == s;
    //     ensures forall i :: i > 0 && i < |b|-1 ==> b[i] == evalInsRe(c.block[i-1].ins,b[i-1]);
    //     ensures b[|b|-1] == b[|b|-2];
    //     ensures b == [s] + evalCodeRE(c,s)
    //     // ensures ValidBehaviorNonTrivial(b);
    //     // ensures BehaviorEvalsCode(c,b);
    //     {
    //         assert forall cs :: cs in c.block ==> !cs.CNil?;
    //         assert |c.block| == 3;
    //         b := [s] + evalCodeRE(c,s);
            
    //         var step,remainder, subBehavior := unwrapBlock(b,c.block,s);
    //         // assert |step| == 1;
    //         // assert step[0] == evalInsRe(first(c.block).ins,s);
    //         // assert b == [s] + step + evalCodeRE(Block(remainder),last(step));
    //         // assert b[0] == s;
    //         // assert b[1] ==  evalInsRe(first(c.block).ins,s);
    //         // assert b == [s] + step + all_but_first(subBehavior);
    //         // assert |remainder| == 1;
    //         // assert remainder == all_but_first(c.block);
    //         // assert !first(remainder).CNil?;
    //         step,remainder,subBehavior := unwrapBlock(subBehavior,remainder,last(step));
    //         // assert remainder == [];
    //         // assert |b| > 0;
    //         // assert ValidBehaviorNonTrivial(b);
    //         // assert subBehavior == [];
            
    //         // step,remainder,subBehavior := unwrapBlock(subBehavior,remainder,last(step));
    //         // assert subBehavior == [last(step)] + [last(step)];
    //         // assert |b| == 4;

    //         // assert remainder == [];

    //     }


    
    
    


    function extractPatchBehavior(c:codeRe,s:state, input:operand) : (b:behavior)

        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(c,b);


    {
        var speed_value := LV("speed_value");
        var result := LV("result");
        var op1 := D(Int(0,IntType(2,false)));

        assert c == Block([Ins(ADD(speed_value,2,op1,input)),
                     Ins(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false))))),
                     Ins(RET(result))]);

        var b := [s] + evalCodeRE(c,s);
        assert c.Block?;
       
        assert b == [s] + evalBlockRE(c.block,s);
        var metaBehavior := evalCodeRE(first(c.block),s);
        var theRest := evalBlockRE(all_but_first(c.block),last(metaBehavior));
        // assert b == [s] + metaBehavior + theRest;
        // assert |all_but_first(c.block)| == 1;
        // assert all_but_first(c.block)[0] == Ins(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))));
        var metaBehavior' := evalCodeRE(first(all_but_first(c.block)),last(metaBehavior));

        var theRest' := evalBlockRE(all_but_first(all_but_first(c.block)),last(metaBehavior'));

        var metaBehavior'' := evalCodeRE(first(all_but_first(all_but_first(c.block))),last(metaBehavior'));

        assert all_but_first(all_but_first(all_but_first(c.block))) == [];
        assert [last(metaBehavior'')] == evalBlockRE(all_but_first(all_but_first(all_but_first(c.block))),last(metaBehavior''));
        // assert theRest[0] == evalInsRe(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))),last(metaBehavior));

        assert b[0] == s;
        assert b[1] == evalInsRe(ADD(speed_value,2,op1,input),s);
        
        // ADD
        assert ValidInstruction(s,ADD(speed_value,2,op1,input));
        assert NextStep(s,b[1], Step.evalInsStep(ADD(speed_value,2,op1,input))); 
        assert StateNext(b[0],b[1]);
        assert ValidState(b[1]);
        assert b[1] == stateUpdateVar(s,speed_value,evalADD(2,OperandContents(s,D(Int(0,IntType(2,false)))),OperandContents(s,input)));
        assert OperandContents(b[1],speed_value).Int?;
        assert ToTwosComp(OperandContents(b[1],speed_value)).val == (Int(0,IntType(2,false)).val + OperandContents(s,input).val) % Pow256(2); 
        
        // ICMP
        assert ValidOperand(b[1],speed_value);
        assert ValidOperand(b[1],D(Int(0,IntType(2,false))));
        assert isInt(OperandContents(b[1],speed_value)) && isInt(OperandContents(b[1],D(Int(0,IntType(2,false)))));
        assert typesMatch(OperandContents(b[1],speed_value),OperandContents(b[1],D(Int(0,IntType(2,false)))));
        assert 2 == OperandContents(b[1],speed_value).itype.size;
        assert ValidInstruction(b[1],ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))));
        assert NextStep(b[1],b[2],Step.evalInsStep(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false))))));
        assert StateNext(b[1],b[2]);
        assert ValidState(b[2]);



//
        assert ValidOperand(b[2],result);
        assert ValidInstruction(b[2],RET(result));
        assert NextStep(b[2],b[3],Step.evalInsStep(RET(result)));
        assert StateNext(b[2],b[3]);
        assert ValidState(b[3]);

        // LAST STEP
        assert b[3] == b[4];
        assert ValidState(b[4]);
        assert NextStep(b[3],b[4],Step.stutterStep());
        assert StateNext(b[3],b[4]);
        
        // Properties
        assert ValidBehaviorNonTrivial(b);
        assert BehaviorEvalsCode(c,b);
        assert OperandContents(b[1],speed_value).val > 0 ==> OperandContents(b[2],result).val == 1;
        assert ValidOperand(last(b),speed_value);
        assert OperandContents(s,input).val > 0 ==> OperandContents(last(b),speed_value).val > 0;

        b

    }        



    function extractVulnBehavior(c:codeRe,s:state, input:operand) : (b:behavior)

        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(c,b);

    {
        var speed_value := LV("speed_value");
        var result := LV("result");
        var op1 := D(Int(0,IntType(2,false)));

        assert c == Block([Ins(ADD(speed_value,2,op1,input)),
                     Ins(ICMP(result,sgt,2,speed_value,D(Int(0,IntType(2,false))))),
                     Ins(RET(result))]);

                var b := [s] + evalCodeRE(c,s);
        assert c.Block?;
       
        assert b == [s] + evalBlockRE(c.block,s);
        var metaBehavior := evalCodeRE(first(c.block),s);
        var theRest := evalBlockRE(all_but_first(c.block),last(metaBehavior));
        // assert b == [s] + metaBehavior + theRest;
        // assert |all_but_first(c.block)| == 1;
        // assert all_but_first(c.block)[0] == Ins(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))));
        var metaBehavior' := evalCodeRE(first(all_but_first(c.block)),last(metaBehavior));

        var theRest' := evalBlockRE(all_but_first(all_but_first(c.block)),last(metaBehavior'));

        var metaBehavior'' := evalCodeRE(first(all_but_first(all_but_first(c.block))),last(metaBehavior'));

        assert all_but_first(all_but_first(all_but_first(c.block))) == [];
        assert [last(metaBehavior'')] == evalBlockRE(all_but_first(all_but_first(all_but_first(c.block))),last(metaBehavior''));
        // assert theRest[0] == evalInsRe(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))),last(metaBehavior));


        assert b[0] == s;
        assert b[1] == evalInsRe(ADD(speed_value,2,op1,input),s);
        
        // ADD
        assert ValidInstruction(s,ADD(speed_value,2,op1,input));
        assert NextStep(s,b[1], Step.evalInsStep(ADD(speed_value,2,op1,input))); 
        assert StateNext(b[0],b[1]);
        assert ValidState(b[1]);
        assert b[1] == stateUpdateVar(s,speed_value,evalADD(2,OperandContents(s,D(Int(0,IntType(2,false)))),OperandContents(s,input)));
        assert OperandContents(b[1],speed_value).Int?;
        assert ToTwosComp(OperandContents(b[1],speed_value)).val == (Int(0,IntType(2,false)).val + OperandContents(s,input).val) % Pow256(2); 
        
        // ICMP
        assert ValidOperand(b[1],speed_value);
        assert ValidOperand(b[1],D(Int(0,IntType(2,false))));
        assert isInt(OperandContents(b[1],speed_value)) && isInt(OperandContents(b[1],D(Int(0,IntType(2,false)))));
        assert typesMatch(OperandContents(b[1],speed_value),OperandContents(b[1],D(Int(0,IntType(2,false)))));
        assert 2 == OperandContents(b[1],speed_value).itype.size;
        assert ValidInstruction(b[1],ICMP(result,sgt,2,speed_value,D(Int(0,IntType(2,false)))));
        assert NextStep(b[1],b[2],Step.evalInsStep(ICMP(result,sgt,2,speed_value,D(Int(0,IntType(2,false))))));
        assert StateNext(b[1],b[2]);
        assert ValidState(b[2]);

        assert ValidOperand(b[2],result);
        assert ValidInstruction(b[2],RET(result));
        assert NextStep(b[2],b[3],Step.evalInsStep(RET(result)));
        assert b[3].output == [OperandContents(b[2],result)];
        assert StateNext(b[2],b[3]);
        assert ValidState(b[3]);

        // LAST STEP
        assert b[3] == b[4];
        assert ValidState(b[4]);
        assert NextStep(b[3],b[4],Step.stutterStep());
        assert StateNext(b[3],b[4]);
        
        // Properties
        assert ValidBehaviorNonTrivial(b);
        assert BehaviorEvalsCode(c,b);
        assert (OperandContents(b[1],speed_value).val > 0  && OperandContents(b[1],speed_value).val <= 0x80 )==> OperandContents(b[2],result).val == 1;
        assert b[0].output == [];
        assert b[1].output == [];
        assert b[2].output == [];
        assert b[3].output == [OperandContents(b[2],result)];
        assert b[4].output == [OperandContents(b[2],result)];
        assert |b| == 5;
        // bOut(b);
        // assert ([] + [] + [] + [OperandContents(b[2],result)] + [OperandContents(b[2],result)]) == [OperandContents(b[2],result),OperandContents(b[2],result)];
        // assert behaviorOutput(b) == [OperandContents(b[2],result),OperandContents(b[2],result)];
        b

    }        

// MINI SPEC

    // Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
    predicate RemovedBehaviors(b:behavior)
    {
        var speed_value := LV("speed_value"); 
        && ValidBehaviorNonTrivial(b)
        && exists s:state :: (&& s in b 
                              && ValidState(s)
                              && ValidOperand(s,speed_value)
                              && OperandContents(s,speed_value).Int?
                              && OperandContents(s,speed_value).val > 0x80)
    }

    // Describes/Excludes 'good' added behavior in Patched Code (ie postBehaviors)
    predicate AddedBehaviors(b:behavior)
    {
        false
    }

    lemma nonInterference(preCode:codeRe,postCode:codeRe)
    {
         forall input,s,pre,post | && ValidState(s)
                                   && validInput(s,input)
                                   && preCode == codeVuln(input)
                                   && postCode == codePatch(input)
                                   && post == extractPatchBehavior(postCode,s,input)
                                   && pre == extractVulnBehavior(preCode,s,input)
                                   && MiniSpec(pre,post)
            ensures last(post) == last(pre)
                        // ensures behaviorOutput(post) == behaviorOutput(pre)

            {
                var speed_value := LV("speed_value");
                var result := LV("result");
                var op1 := D(Int(0,IntType(2,false)));

                var c := codeVuln(input);
                assert pre == [s] + evalCodeRE(codeVuln(input),s);
                assert pre == [s] + evalBlockRE(c.block,s);
                var metaBehavior := evalCodeRE(first(c.block),s);
                var theRest := evalBlockRE(all_but_first(c.block),last(metaBehavior));

                var metaBehavior' := evalCodeRE(first(all_but_first(c.block)),last(metaBehavior));

                assert ValidBehavior(pre);
                //

                var c' := codePatch(input);
                assert post == [s] + evalCodeRE(codePatch(input),s);
                assert post == [s] + evalBlockRE(c'.block,s);
                var metaBehaviorPost := evalCodeRE(first(c'.block),s);
                var theRestPost := evalBlockRE(all_but_first(c'.block),last(metaBehaviorPost));
                assert post == [s] + metaBehaviorPost + theRestPost;
                // assert |all_but_first(c'.block)| == 1;
                assert all_but_first(c'.block)[0] == Ins(ICMP(result,ugt,2,speed_value,D(Int(0,IntType(2,false)))));
                var metaBehaviorPost' := evalCodeRE(first(all_but_first(c'.block)),last(metaBehaviorPost));

                assert last(post) == last(pre);
                                // assert behaviorOutput(post) == behaviorOutput(pre);
// 

            }
    }

}
