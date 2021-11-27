include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/Operations/binaryOperations.i.dfy"

module simpleBugCode{

    import opened types
    import opened LLVM_defRE
    import opened binary_operations_i
    import opened Collections__Seqs_s

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
        // var result := LV("result");
        && s.o.Nil?
        && ValidOperand(s,input)
        && isInt(OperandContents(s,input))
        && typesMatch(OperandContents(s,D(Int(0,IntType(4,false)))),OperandContents(s,input))
        && OperandContents(s,input).val >= 0 
        && OperandContents(s,input).val <= 2
        // && ValidOperand(s,result)
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


    lemma unwrapPatchBehaviors(s:state, input:operand) returns (b:behavior)
        requires ValidState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        ensures |b| == 5;
        ensures b[0] == s;
        ensures forall i :: i > 0 && i < |b|-1 ==> b[i] == evalInsRe(codePatch(input).block[i-1].ins,b[i-1]);
        ensures b[|b|-1] == b[|b|-2];
        // ensures b == [s] + evalCodeRE(c,s)


        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(codePatch(input),b);


        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(codePatch(input),b);
        ensures forall b' :: (BehaviorEvalsCode(codePatch(input),b')  && b'[0] == b[0]) ==> b' == b

        ensures exists patch :: BehaviorEvalsCode(codePatch(input),patch) && b == patch;
        // ensures  exists result :: (
        //                 && ValidOperand(last(b),result)
        //                 && OperandContents(last(b),result).Int?
        //                 && OperandContents(last(b),result).val == 1);
        ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

        {
            var c := codePatch(input);
            assert forall cs :: cs in c.block ==> !cs.CNil?;
            assert |c.block| == 3;
            b := [s] + evalCodeRE(c,s);
            
            var step,remainder, subBehavior := unwrapBlockWitness(b,c.block,s);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
  
            var z := LV("z");
            var result := LV("result");
            
            var y := D(Int(2147483646,IntType(4,false)));


            assert c == Block([Ins(ADD(z,4,input,y)),
                            Ins(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))),
                            Ins(RET(result))]);


            assert b[0] == s;
            assert b[1] == evalInsRe(ADD(z,4,input,y),s);
            
            // ADD
            assert ValidInstruction(s,ADD(z,4,input,y));
            assert NextStep(s,b[1], Step.evalInsStep(ADD(z,4,input,y))); 
            assert StateNext(b[0],b[1]);
            assert ValidState(b[1]);
            assert b[1] == stateUpdateVar(s,z,evalADD(4,OperandContents(s,D(Int(2147483646,IntType(4,false)))),OperandContents(s,input)));
            assert OperandContents(b[1],z).Int?;
            assert ToTwosComp(OperandContents(b[1],z)).val == (Int(2147483646,IntType(4,false)).val + OperandContents(s,input).val) % Pow256(4); 
            assert OperandContents(s,input).val > 0 ==> OperandContents(b[1],z).val > 0;
        
            // ICMP
            assert ValidOperand(b[1],z);
            assert ValidOperand(b[1],D(Int(0,IntType(4,false))));
            assert isInt(OperandContents(b[1],z)) && isInt(OperandContents(b[1],D(Int(0,IntType(4,false)))));
            assert typesMatch(OperandContents(b[1],z),OperandContents(b[1],D(Int(0,IntType(4,false)))));
            assert 4 == OperandContents(b[1],z).itype.size;
            assert ValidInstruction(b[1],ICMP(result,ugt,4,z,D(Int(0,IntType(4,false)))));
            assert NextStep(b[1],b[2],Step.evalInsStep(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))));
            assert StateNext(b[1],b[2]);
            assert ValidState(b[2]);
    //
            assert ValidOperand(b[2],result);
            assert OperandContents(b[2],result).Int?;
            assert OperandContents(b[2],result).val == 1;
            assert ValidInstruction(b[2],RET(result));
            assert NextStep(b[2],b[3],Step.evalInsStep(RET(result)));
            assert StateNext(b[2],b[3]);
            assert OperandContents(b[2],result) == OperandContents(b[3],result);
            assert ValidState(b[3]);

            // LAST STEP
            assert b[3] == b[4];
            assert ValidState(b[4]);
            assert NextStep(b[3],b[4],Step.stutterStep());
            assert StateNext(b[3],b[4]);
            
            // Properties
            assert ValidBehaviorNonTrivial(b);
            assert BehaviorEvalsCode(c,b);
            assert OperandContents(b[1],z).val > 0 ==> OperandContents(b[2],result).val == 1;
            assert ValidOperand(last(b),z);
            assert OperandContents(s,input).val > 0 ==> OperandContents(b[1],z).val > 0;
            assert |b| == 5;
            // assert forall b' :: (b' in b && ValidOperand(b',result) && OperandContents(b',result).Int?) ==> OperandContents(b',result).val != 0;
            assert Out(OperandContents(b[2],result)) in behaviorOutput(b);
            assert OperandContents(b[2],result) == (Int(1,IntType(1,false)));
            // assert OperandContents(b[2],result) == (Int(1,IntType(1,false)));
            assert behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))];
            // outputIsEqual(behaviorOutput(b) , [Nil,Nil,Nil,Out(OperandContents(b[2],result)),Out(OperandContents(b[2],result))]);
         
            assert OperandContents(last(b),result).val == 1;
            uniqueOperandContent(last(b),result);
            assert !(OperandContents(last(b),result).val == 0);
            uniqueOperandInState(last(b),result);
            // assert (exists s:state :: (s == last(b) && s in b 
            //                   && ValidState(s)
            //                   && ValidOperand(s,result)
            //                   && OperandContents(s,result).Int?
            //                   && OperandContents(s,result).val == 1));

            // assert (exists s:state,result:operand :: (&& s in b
            //                                         && last(b) == s 
            //                                         && ValidState(s)
            //                                         && result.LV?
            //                                         && result.l in s.lvs
            //                                         && ValidOperand(s,result)
            //                                         && OperandContents(s,result).Int?
            //                                         && OperandContents(s,result).val == 1));


        }

     lemma unwrapVulnBehaviors(s:state, input:operand) returns (b:behavior)
        requires ValidState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        ensures |b| == 5;
        ensures b[0] == s;
        ensures forall i :: i > 0 && i < |b|-1 ==> b[i] == evalInsRe(codeVuln(input).block[i-1].ins,b[i-1]);
        ensures b[|b|-1] == b[|b|-2];
        // ensures b == [s] + evalCodeRE(c,s)


        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(codeVuln(input),b);
        ensures forall b' :: (BehaviorEvalsCode(codeVuln(input),b')  && b'[0] == b[0]) ==> b' == b

        ensures exists input :: validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s

        ensures ValidBehaviorNonTrivial(b);
        ensures BehaviorEvalsCode(codeVuln(input),b);
        ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))])
                || (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        ensures (OperandContents(s,input).val < 2) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures (OperandContents(s,input).val >= 2) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
         ensures OperandContents(s,input).val == 2 ==>( exists result:operand :: 
                                                            (&& ValidState(last(b))
                                                            && result.LV?
                                                            && result.l in last(b).lvs
                                                            && ValidOperand(last(b),result)
                                                            && OperandContents(last(b),result).Int?
                                                            && OperandContents(last(b),result).val == 0));
        {
            var c := codeVuln(input);
            assert forall cs :: cs in c.block ==> !cs.CNil?;
            assert |c.block| == 3;
            b := [s] + evalCodeRE(c,s);
            
            var step,remainder, subBehavior := unwrapBlockWitness(b,c.block,s);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
  
            var z := LV("z");
            var result := LV("result");
            var y := D(Int(2147483646,IntType(4,false)));


            assert c == Block([Ins(ADD(z,4,input,y)),
                            Ins(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))),
                            Ins(RET(result))]);


            assert b[0] == s;
            assert b[1] == evalInsRe(ADD(z,4,input,y),s);
            
            // ADD
            assert ValidInstruction(s,ADD(z,4,input,y));
            assert NextStep(s,b[1], Step.evalInsStep(ADD(z,4,input,y))); 
            assert StateNext(b[0],b[1]);
            assert ValidState(b[1]);
            assert b[1] == stateUpdateVar(s,z,evalADD(4,OperandContents(s,D(Int(2147483646,IntType(4,false)))),OperandContents(s,input)));
            assert OperandContents(b[1],z).Int?;
            assert ToTwosComp(OperandContents(b[1],z)).val == (Int(2147483646,IntType(4,false)).val + OperandContents(s,input).val) % Pow256(4);
            assert OperandContents(s,input).val == 2 ==>   OperandContents(b[1],z).val == 2147483648;
            assert OperandContents(s,input).val == 2 ==>  FromTwosComp(OperandContents(b[1],z)).val < 0;
            assert OperandContents(s,input).val > 0 ==> OperandContents(b[1],z).val > 0;
        
            // ICMP
            assert ValidOperand(b[1],z);
            assert ValidOperand(b[1],D(Int(0,IntType(4,false))));
            assert isInt(OperandContents(b[1],z)) && isInt(OperandContents(b[1],D(Int(0,IntType(4,false)))));
            assert typesMatch(OperandContents(b[1],z),OperandContents(b[1],D(Int(0,IntType(4,false)))));
            assert 4 == OperandContents(b[1],z).itype.size;
            assert ValidInstruction(b[1],ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))));
            assert NextStep(b[1],b[2],Step.evalInsStep(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))));
            assert StateNext(b[1],b[2]);
            assert ValidState(b[2]);
            assert (OperandContents(b[1],z).val <= 2147483647) ==> OperandContents(b[2],result).val == 1;
    //
            assert ValidOperand(b[2],result);
            assert ValidInstruction(b[2],RET(result));
            assert NextStep(b[2],b[3],Step.evalInsStep(RET(result)));
            assert StateNext(b[2],b[3]);
            assert OperandContents(b[2],result) == OperandContents(b[3],result);

            assert ValidState(b[3]);

            // LAST STEP
            assert b[3] == b[4];
            assert ValidState(b[4]);
            assert NextStep(b[3],b[4],Step.stutterStep());
            assert StateNext(b[3],b[4]);
            
            // Properties
            assert ValidBehaviorNonTrivial(b);
            assert BehaviorEvalsCode(c,b);
            assert OperandContents(s,input).val < 2 ==> OperandContents(b[2],result).val == 1;
            assert OperandContents(s,input).val == 2 ==> OperandContents(last(b),result).val == 0;
            assert ValidOperand(last(b),z);
            assert OperandContents(s,input).val > 0 ==> OperandContents(b[1],z).val > 0;
            assert |b| == 5;
            assert Out(OperandContents(b[2],result)) in behaviorOutput(b);
            assert (OperandContents(b[2],result) == (Int(1,IntType(1,false)))) || (OperandContents(b[2],result) == (Int(0,IntType(1,false))));

            assert behaviorOutput(b) == [Nil,Nil,Nil,Out(OperandContents(b[2],result)),Out(OperandContents(b[2],result))];

            assert OperandContents(s,input).val == 2 ==>( exists result:operand :: 
                                                            (&& ValidState(last(b))
                                                            && result.LV?
                                                            && result.l in last(b).lvs
                                                            && ValidOperand(last(b),result)
                                                            && OperandContents(last(b),result).Int?
                                                            && OperandContents(last(b),result).val == 0));

        }

    lemma validInputPatchImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: BehaviorEvalsCode(codePatch(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: BehaviorEvalsCode(codePatch(input),b) && b[0] == s
        {
            var b := unwrapPatchBehaviors(s,input);
            assert exists b' :: BehaviorEvalsCode(codePatch(input),b') && b'[0] == s;
        }
    }

    lemma validInputVulnImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: BehaviorEvalsCode(codeVuln(input),b) && b[0] == s
        {
            var b := unwrapVulnBehaviors(s,input);
            assert exists b' :: BehaviorEvalsCode(codeVuln(input),b') && b'[0] == s;
        }
    }

    predicate nonTrivialBehaviorPreconditions(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>)
    {
        && ValidState(s)
        && nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors)
        && nonTrivialBehaviorPreconditionsPatch(s,patchBehaviors)
        && |vulnBehaviors| >= |patchBehaviors|
      
    }

    predicate nonTrivialBehaviorPreconditionsPatch(s:state,patchBehaviors:seq<behavior>)
        requires ValidState(s)
    {   
        (forall b :: b in patchBehaviors <==> (exists input :: validInput(s,input) && BehaviorEvalsCode(codePatch(input),b) && b[0] == s))
    }
    
    predicate nonTrivialBehaviorPreconditionsVuln(s:state,vulnBehaviors:seq<behavior>)
        requires ValidState(s)
    {
        (forall b :: b in vulnBehaviors <==> (exists input :: validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s))
    }

    predicate validPatchBehavior(b:behavior)
    {
        exists input :: BehaviorEvalsCode(codePatch(input),b) && |b| > 0 && ValidState(b[0]) && validInput(b[0],input)
    }

    predicate validVulnBehavior(b:behavior)
    {
        exists input :: BehaviorEvalsCode(codeVuln(input),b) && ValidBehaviorNonTrivial(b)
    }

}