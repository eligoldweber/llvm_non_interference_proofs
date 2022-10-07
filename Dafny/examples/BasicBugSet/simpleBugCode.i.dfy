include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/Operations/binaryOperations.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"

module simpleBugCode{

    import opened types
    import opened LLVM_defRE
    import opened binary_operations_i
    import opened Collections__Seqs_s
    import opened behavior_lemmas

// c function //
// int testOverflow(int x)
// {
//   if (x < 0 || x > 2){
//     return -2;
//   }
//   int y = INT_MAX-1;
//   int z = x + y;
//   if(z > 0){
//     return 42;
//   }else{
//     return -1;
//   }

// ---------------------------------------------------
// -03
// ; Function Attrs: nofree norecurse nosync nounwind readnone uwtable willreturn mustprogress
// define dso_local i32 @testOverflow(i32 %x) local_unnamed_addr #2 {
// entry:
//   %0 = icmp ugt i32 %x, 2
//   %retval.1 = select i1 %0, i32 -2, i32 42
//   ret i32 %retval.1
// }
// ---------------------------------------------------
// No Opt
// ; Function Attrs: noinline nounwind optnone uwtable
// define dso_local i32 @testOverflow(i32 %x) #0 {
// entry:
//   %retval = alloca i32, align 4
//   %x.addr = alloca i32, align 4
//   %y = alloca i32, align 4
//   %z = alloca i32, align 4
//   store i32 %x, i32* %x.addr, align 4
//   %0 = load i32, i32* %x.addr, align 4
//   %cmp = icmp slt i32 %0, 0
//   br i1 %cmp, label %if.then, label %lor.lhs.false

// lor.lhs.false:                                    ; preds = %entry
//   %1 = load i32, i32* %x.addr, align 4
//   %cmp1 = icmp sgt i32 %1, 2
//   br i1 %cmp1, label %if.then, label %if.end

// if.then:                                          ; preds = %lor.lhs.false, %entry
//   store i32 -2, i32* %retval, align 4
//   br label %return

// if.end:                                           ; preds = %lor.lhs.false
//   store i32 2147483646, i32* %y, align 4
//   %2 = load i32, i32* %x.addr, align 4
//   %3 = load i32, i32* %y, align 4
//   %add = add nsw i32 %2, %3
//   store i32 %add, i32* %z, align 4
//   %4 = load i32, i32* %z, align 4
//   %cmp2 = icmp sgt i32 %4, 0
//   br i1 %cmp2, label %if.then3, label %if.else

// if.then3:                                         ; preds = %if.end
//   store i32 42, i32* %retval, align 4
//   br label %return

// if.else:                                          ; preds = %if.end
//   store i32 -1, i32* %retval, align 4
//   br label %return

// return:                                           ; preds = %if.else, %if.then3, %if.then
//   %5 = load i32, i32* %retval, align 4
//   ret i32 %5
// }
// ---------------------------------------------------
// Mixed
// ; Function Attrs: nofree norecurse nosync nounwind readnone uwtable willreturn mustprogress
// define dso_local i32 @testOverflow(i32 %x) local_unnamed_addr #2 {
// entry:
    // %cmp = icmp slt i32 %x, 0



    predicate validInput(s:state, input:operand)
        requires ValidState(s)
    {
        && s.o.Nil?
        && ValidOperand(s,input)
        && isInt(OperandContents(s,input))
        && typesMatch(OperandContents(s,D(Int(0,IntType(4,false)))),OperandContents(s,input))
        && OperandContents(s,input).val >= 0 
        && OperandContents(s,input).val <= 2
    }


    function codeVuln(x:operand):codeRe
    {
        var z := LV("z");
        var result := LV("result");

        var y := D(Int(2147483646,IntType(4,false)));

        var cSeq := [Ins(ADD(z,4,x,y)),
                     Ins(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }
    
    function codePatch(x:operand):codeRe
    {
        var z := LV("z");
        var result := LV("result");

        var y := D(Int(2147483646,IntType(4,false)));

        var cSeq := [Ins(ADD(z,4,x,y)),
                     Ins(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }


    lemma unwrapPatchBehaviors(s:state, input:operand) returns (postB:behavior)
        requires ValidState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        ensures |postB| == 5;
        ensures postB[0] == s;
        ensures postB[|postB|-1] == postB[|postB|-2];


        ensures ValidBehaviorNonTrivial(postB);
        ensures BehaviorEvalsCode(codePatch(input),postB);


        ensures ValidBehaviorNonTrivial(postB);
        ensures BehaviorEvalsCode(codePatch(input),postB);
        // ensures forall b' :: (BehaviorEvalsCode(codePatch(input),b')  && b'[0] == b[0]) ==> b' == b

        ensures exists patchB :: BehaviorEvalsCode(codePatch(input),patchB) && postB == patchB;
        // ensures forall b' :: (|b'| > 0 && BehaviorEvalsCode(codePatch(input),b')  && b'[0] == b[0]) ==> b' == b

        ensures  !(exists s:state,result:operand :: (&& s in postB
                                                        && last(postB) == s 
                                                        && ValidState(s)
                                                        && result.LV?
                                                        && result.l == "result"
                                                        && result.l in s.lvs
                                                        && ValidOperand(s,result)
                                                        && OperandContents(s,result).Int?
                                                        && OperandContents(s,result).val == 0 ));
        ensures (behaviorOutput(postB) == validOutput());

        {
            reveal_BehaviorEvalsCode();
            var c := codePatch(input);
            assert forall cs :: cs in c.block ==> !cs.CNil?;
            assert |c.block| == 3;
            postB := [s] + evalCodeRE(c,s);
            
            var step,remainder, subBehavior := unwrapBlockWitness(postB,c.block,s);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
  
            var z := LV("z");   
            var result := LV("result");
            
            var y := D(Int(2147483646,IntType(4,false)));


            assert c == Block([Ins(ADD(z,4,input,y)),
                            Ins(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))),
                            Ins(RET(result))]);


            assert postB[0] == s;
            assert postB[1] == evalInsRe(ADD(z,4,input,y),s);
            
            // ADD
            assert ValidInstruction(s,ADD(z,4,input,y));
            assert NextStep(s,postB[1], Step.evalInsStep(ADD(z,4,input,y))); 
            assert StateNext(postB[0],postB[1]);
            assert ValidState(postB[1]);
            assert postB[1] == stateUpdateVar(s,z,evalADD(4,OperandContents(s,D(Int(2147483646,IntType(4,false)))),OperandContents(s,input)));
            assert OperandContents(postB[1],z).Int?;
            assert ToTwosComp(OperandContents(postB[1],z)).val == (Int(2147483646,IntType(4,false)).val + OperandContents(s,input).val) % Pow256(4); 
            assert OperandContents(s,input).val > 0 ==> OperandContents(postB[1],z).val > 0;
        
            // ICMP
            assert ValidOperand(postB[1],z);
            assert ValidOperand(postB[1],D(Int(0,IntType(4,false))));
            assert isInt(OperandContents(postB[1],z)) && isInt(OperandContents(postB[1],D(Int(0,IntType(4,false)))));
            assert typesMatch(OperandContents(postB[1],z),OperandContents(postB[1],D(Int(0,IntType(4,false)))));
            assert 4 == OperandContents(postB[1],z).itype.size;
            assert ValidInstruction(postB[1],ICMP(result,ugt,4,z,D(Int(0,IntType(4,false)))));
            assert NextStep(postB[1],postB[2],Step.evalInsStep(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))));
            assert StateNext(postB[1],postB[2]);
            assert ValidState(postB[2]);
    //
            assert ValidOperand(postB[2],result);
            assert OperandContents(postB[2],result).Int?;
            assert OperandContents(postB[2],result).val == 1;
            assert ValidInstruction(postB[2],RET(result));
            assert NextStep(postB[2],postB[3],Step.evalInsStep(RET(result)));
            assert StateNext(postB[2],postB[3]);
            assert OperandContents(postB[2],result) == OperandContents(postB[3],result);
            assert ValidState(postB[3]);

            // LAST STEP
            assert postB[3] == postB[4];
            assert ValidState(postB[4]);
            assert NextStep(postB[3],postB[4],Step.stutterStep());
            assert StateNext(postB[3],postB[4]);
            
            // Properties
            assert ValidBehaviorNonTrivial(postB);
            assert BehaviorEvalsCode(c,postB);
            assert OperandContents(postB[1],z).val > 0 ==> OperandContents(postB[2],result).val == 1;
            assert ValidOperand(last(postB),z);
            assert OperandContents(s,input).val > 0 ==> OperandContents(postB[1],z).val > 0;
            assert |postB| == 5;
            // assert forall b' :: (b' in b && ValidOperand(b',result) && OperandContents(b',result).Int?) ==> OperandContents(b',result).val != 0;
            assert Out(OperandContents(postB[2],result)) in behaviorOutput(postB);
            assert OperandContents(postB[2],result) == (Int(1,IntType(1,false)));
            // assert OperandContents(b[2],result) == (Int(1,IntType(1,false)));
            assert behaviorOutput(postB) == validOutput();
            // outputIsEqual(behaviorOutput(b) , [Nil,Nil,Nil,Out(OperandContents(b[2],result)),Out(OperandContents(b[2],result))]);
         
            assert OperandContents(last(postB),result).val == 1;
            uniqueOperandContent(last(postB),result);
            assert !(OperandContents(last(postB),result).val == 0);
            uniqueOperandInState(last(postB),result);


        }

     lemma unwrapVulnBehaviors(s:state, input:operand) returns (preB:behavior)
        requires ValidState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        ensures |preB| == 5;
        ensures preB[0] == s;

        ensures ValidBehaviorNonTrivial(preB);
        ensures BehaviorEvalsCode(codeVuln(input),preB);

        ensures exists input :: |preB| > 0 && validInput(s,input) && BehaviorEvalsCode(codeVuln(input),preB) && preB[0] == s

        ensures ValidBehaviorNonTrivial(preB);
        ensures BehaviorEvalsCode(codeVuln(input),preB);
        ensures (behaviorOutput(preB) == validOutput())
                || (behaviorOutput(preB) == invalidOutput());
        ensures (OperandContents(s,input).val < 2) ==> (behaviorOutput(preB) == validOutput());
        ensures (OperandContents(s,input).val >= 2) ==> (behaviorOutput(preB) == invalidOutput());
        ensures OperandContents(s,input).val == 2 ==>(exists result:operand :: 
                                                            (&& ValidState(last(preB))
                                                            && result.LV?
                                                            && result.l == "result"
                                                            && result.l in last(preB).lvs
                                                            && ValidOperand(last(preB),result)
                                                            && OperandContents(last(preB),result).Int?
                                                            && OperandContents(last(preB),result).val == 0));
        ensures OperandContents(s,input).val < 2 ==> !(exists result:operand :: 
                                                            (&& ValidState(last(preB))
                                                            && result.LV?
                                                            && result.l == "result"
                                                            && result.l in last(preB).lvs
                                                            && ValidOperand(last(preB),result)
                                                            && OperandContents(last(preB),result).Int?
                                                            && OperandContents(last(preB),result).val == 0));
        {
            reveal_BehaviorEvalsCode();
            var c := codeVuln(input);
            assert forall cs :: cs in c.block ==> !cs.CNil?;
            assert |c.block| == 3;
            preB := [s] + evalCodeRE(c,s);
            
            var step,remainder, subBehavior := unwrapBlockWitness(preB,c.block,s);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
  
            var z := LV("z");
            var result := LV("result");
            var y := D(Int(2147483646,IntType(4,false)));


            assert c == Block([Ins(ADD(z,4,input,y)),
                            Ins(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))),
                            Ins(RET(result))]);


            assert preB[0] == s;
            assert preB[1] == evalInsRe(ADD(z,4,input,y),s);
            
            // ADD
            assert ValidInstruction(s,ADD(z,4,input,y));
            assert NextStep(s,preB[1], Step.evalInsStep(ADD(z,4,input,y))); 
            assert StateNext(preB[0],preB[1]);
            assert ValidState(preB[1]);
            assert preB[1] == stateUpdateVar(s,z,evalADD(4,OperandContents(s,D(Int(2147483646,IntType(4,false)))),OperandContents(s,input)));
            assert OperandContents(preB[1],z).Int?;
            assert ToTwosComp(OperandContents(preB[1],z)).val == (Int(2147483646,IntType(4,false)).val + OperandContents(s,input).val) % Pow256(4);
            assert OperandContents(s,input).val == 2 ==>   OperandContents(preB[1],z).val == 2147483648;
            assert OperandContents(s,input).val == 2 ==>  FromTwosComp(OperandContents(preB[1],z)).val < 0;
            assert OperandContents(s,input).val > 0 ==> OperandContents(preB[1],z).val > 0;
        
            // ICMP
            assert ValidOperand(preB[1],z);
            assert ValidOperand(preB[1],D(Int(0,IntType(4,false))));
            assert isInt(OperandContents(preB[1],z)) && isInt(OperandContents(preB[1],D(Int(0,IntType(4,false)))));
            assert typesMatch(OperandContents(preB[1],z),OperandContents(preB[1],D(Int(0,IntType(4,false)))));
            assert 4 == OperandContents(preB[1],z).itype.size;
            assert ValidInstruction(preB[1],ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))));
            assert NextStep(preB[1],preB[2],Step.evalInsStep(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))));
            assert StateNext(preB[1],preB[2]);
            assert ValidState(preB[2]);
            assert (OperandContents(preB[1],z).val <= 2147483647) ==> OperandContents(preB[2],result).val == 1;
    //
            assert ValidOperand(preB[2],result);
            assert ValidInstruction(preB[2],RET(result));
            assert NextStep(preB[2],preB[3],Step.evalInsStep(RET(result)));
            assert StateNext(preB[2],preB[3]);
            assert OperandContents(preB[2],result) == OperandContents(preB[3],result);

            assert ValidState(preB[3]);

            // LAST STEP
            assert preB[3] == preB[4];
            assert ValidState(preB[4]);
            assert NextStep(preB[3],preB[4],Step.stutterStep());
            assert StateNext(preB[3],preB[4]);
            
            // Properties
            assert ValidBehaviorNonTrivial(preB);
            assert BehaviorEvalsCode(c,preB);
            assert OperandContents(s,input).val < 2 ==> OperandContents(preB[2],result).val == 1;
            assert OperandContents(s,input).val == 2 ==> OperandContents(last(preB),result).val == 0;
            assert ValidOperand(last(preB),z);
            assert OperandContents(s,input).val > 0 ==> OperandContents(preB[1],z).val > 0;
            assert |preB| == 5;
            assert (OperandContents(preB[2],result) == (Int(1,IntType(1,false)))) || (OperandContents(preB[2],result) == (Int(0,IntType(1,false))));

            assert behaviorOutput(preB) == [Nil,Nil,Nil,Out(OperandContents(preB[2],result)),Out(OperandContents(preB[2],result))];


        }

    lemma validInputPatchImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: |b| > 0 && BehaviorEvalsCode(codePatch(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: |b| > 0 && BehaviorEvalsCode(codePatch(input),b) && b[0] == s
        {
            var b := unwrapPatchBehaviors(s,input);
            assert exists b' :: |b'| > 0 && BehaviorEvalsCode(codePatch(input),b') && b'[0] == s;
        }
    }

    lemma validInputVulnImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: |b| > 0 && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: |b| > 0 && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s
        {
            var b := unwrapVulnBehaviors(s,input);
            assert exists b' :: |b'| > 0 && BehaviorEvalsCode(codeVuln(input),b') && b'[0] == s;
        }
    }

    function validOutput():(validOut:seq<output>)
    {
        [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]
    }

    function invalidOutput():(invalidOut:seq<output>)
    {
        [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]
    }

    
}