include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"
include "Challenge6Code.s.dfy"

module challenge6CodeLemmas{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory
    import opened challenge6Code


// -- hechenxi@umich : chenxi

lemma unwrapVulnBehaviors(s:state, input:operand, c:codeRe) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_prob_5_code_write_encrypted_simple();

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        
        // ensures ValidBehaviorNonTrivial(preB);
        ensures BehaviorEvalsCode(challenge_prob_5_code_write_encrypted_simple(),preB);
        ensures |preB| == 10;
        ensures preB[0] == s;
        
        ensures StateNext(preB[0],preB[1]);
        ensures StateNext(preB[1],preB[2]);
        ensures ValidState(preB[0]);
        ensures ValidState(preB[1]);
        ensures ValidState(preB[2]);
        ensures preB[2] == preB[3];
        ensures ValidState(preB[3]);
        ensures preB[3] == preB[4];
        ensures ValidState(preB[4]);
        ensures ValidState(preB[5]);
        ensures StateNext(preB[0],preB[1]);
        ensures StateNext(preB[1],preB[2]);
        ensures StateNext(preB[2],preB[3]);
        ensures StateNext(preB[3],preB[4]);
        ensures StateNext(preB[4],preB[5]);
        ensures StateNext(preB[5],preB[6]);
        ensures ValidState(preB[6]);
        ensures StateNext(preB[6],preB[7]);
        ensures ValidState(preB[7]);
        ensures StateNext(preB[7],preB[8]);
        ensures ValidState(preB[8]);
        ensures StateNext(preB[8],preB[9]);
        ensures ValidState(preB[9]);
        // ensures preB == [s] + evalCodeRE(c,s);
        // ensures 
        ensures behaviorOutput(preB) == [Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        SubOut([Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false)))]),
                                        SubOut([Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false)))])];



    {
        reveal_BehaviorEvalsCode();
        // reveal_ValidBehavior();

        var call:operand := LV("call");
        var call1:operand := LV("call1");
        var mblock:operand := LV("mblock");
        var call2 :=LV("call2");
        var call3 := LV("call3");
        assert OperandContents(s,call3).itype.size == 4;

        var cmp := LV("cmp");
        var INTEGRITY_SIZE := LV("INTEGRITY_SIZE");

        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        // var c := challenge_prob_5_code_write_encrypted_simple();
        assert |c.block| == 8;
        preB := [s] + evalCodeRE(c,s);
       
        var step,remainder,subBehavior := unwrapBlockWitness(preB,c.block,s);

            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        assert preB[0] == s;
        assert preB[1] == evalInsRe(CALL(call,malloc(Int(0,IntType(8,false)))),s);
        assert ValidOperand(preB[1],call);

        assert NextStep(preB[1],preB[2],Step.evalInsStep(LLVM_MEMCPY(call,mblock,1,false)));
        assert StateNext(preB[1],preB[2]);
        assert ValidState(preB[2]);
        assert preB[2] == evalInsRe(LLVM_MEMCPY(call,mblock,1,false),preB[1]);
// 
        assert preB[2] == preB[3];
        assert NextStep(preB[2],preB[3],Step.evalInsStep(CALL(call1,malloc(Ptr(0,0,0,1)))));
        assert ValidState(preB[3]);

        assert NextStep(preB[3],preB[4],Step.evalInsStep(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))));
        assert preB[3] == preB[4];
        assert ValidState(preB[4]);
        
        assert NextStep(preB[4],preB[5],Step.evalInsStep(STORE(call2,bytes_written)));
        assert ValidState(preB[5]);
        

        assert ValidInstruction(preB[5],CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
        assert preB[6] == evalInsRe(CALL(call3,fwrite_empty(bytes_written,4,1,D(Ptr(0,0,0,1)))),preB[5]);
        assert preB[5] == preB[6];
        assert ValidState(preB[6]);

        assert StateNext(preB[5],preB[6]);
        assert ValidState(preB[6]);
        
        assert cmp.LV?;
        // var r := D(Int(0,IntType(4,false)));
        // assert  IntFits(r.d.val,r.d.itype);
        var src2 := validZero16bitInt(preB[6]);
        assert ValidOperand(preB[6],call3);// 
        assert ValidOperand(preB[6],src2);
        assert && isInt(OperandContents(preB[6],call3));// 
        assert && isInt(OperandContents(preB[6],src2));
        assert OperandContents(preB[6],call3).itype.size == 4;
        assert !OperandContents(preB[6],call3).itype.signed;
        intsTypeMatch(OperandContents(preB[6],call3),OperandContents(preB[6],src2));
        assert typesMatch(OperandContents(preB[6],call3),OperandContents(preB[6],src2));

        // assert (Int(1,IntType(4,false))) == OperandContents(preB[6],call3);
        assert ValidInstruction(preB[6],ICMP(cmp,eq,4,call3,src2));

        assert preB[7] == evalInsRe(ICMP(cmp,eq,4,call3,src2),preB[6]);
        // var s' := stateUpdateVar(preB[6],cmp,evalICMP(eq,4,OperandContents(preB[6],call3),OperandContents(preB[6],src2)));


        assert NextStep(preB[6],preB[7],Step.evalInsStep(ICMP(cmp,eq,4,call3,src2)));
        assert StateNext(preB[6],preB[7]);
        assert ValidState(preB[7]);

        assert ValidInstruction(preB[7],CALL(D(Void),stateOutputDump(KEY.d,IV_SIZE.d)));
        // assert c[7] == CALL(D(Void),stateOutputDump(KEY,IV_SIZE));
        assert preB[8] == evalInsRe(CALL(D(Void),stateOutputDump(KEY.d,IV_SIZE.d)),preB[7]);
        var dump := unwrapDumpWitness(preB[7],KEY.d,IV_SIZE.d,preB[8]);
        assert NextStep(preB[7],preB[8],Step.evalInsStep(CALL(D(Void),stateOutputDump(KEY.d,IV_SIZE.d))));   
        assert preB[8].o == SubOut([Out((Int(16,IntType(4,false)))),Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false)))]);

        // // // LAST STEP
        assert preB[8] == preB[9];
        equalStatesAreStutter(preB[8],preB[9]);
        // assert ValidState(preB[8]);
        // assert NextStep(preB[7],preB[8],Step.stutterStep());
        assert StateNext(preB[8],preB[9]);

        // // assert ValidBehaviorNonTrivial(preB);
        // // assert BehaviorEvalsCode(c,preB);
        assert |preB| == 10;
        assert behaviorOutput(preB) == [Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        SubOut([Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false)))]),
                                        SubOut([Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false))),Out(Int(16,IntType(4,false)))])];


    }



 lemma vulnBehaviorIsValid(s:state, input:operand) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);

    {
        reveal_ValidBehavior();
        reveal_BehaviorEvalsCode();
        var c := challenge_prob_5_code_write_encrypted_simple();
        var x := unwrapVulnBehaviors(s,input,c);
        assert ValidBehaviorNonTrivial(x);
        assert BehaviorEvalsCode(c,x);

        // assert behaviorOutput(x) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(x[5].lvs["bytes_written"]),Nil,Nil];

        // assert BehaviorEvalsCode(c,preB);
    }


    lemma equalStatesAreStutter(s:state,s':state)
        requires s==s'
        requires ValidState(s);
        ensures ValidState(s');
        ensures NextStep(s,s',Step.stutterStep());
        ensures StateNext(s,s');
    {
         assert ValidState(s');
         assert NextStep(s,s',Step.stutterStep());
         assert StateNext(s,s');
    }

    lemma intsTypeMatch(x:Data,y:Data)
        requires (isInt(x) && isInt(y))
        requires x.itype.size == y.itype.size
        requires x.itype.signed == y.itype.signed
        ensures typesMatch(x,y);
    {
        assert typesMatch(x,y);
    }

    function validZero16bitInt(s:state) : (val:operand)
        ensures val.D?;
        ensures val.d.Int?;
        ensures ValidData(s, val.d)
        ensures !val.d.itype.signed
        ensures val.d.itype.size == 4
    {
        var val := D(Int(0,IntType(4,false)));
        assert  IntFits(val.d.val,val.d.itype);
        val
    }

    lemma unwrapDumpWitness(s:state,op1:Data,op2:Data,sNext:state) returns (b:behavior)
        requires ValidState(s)
        requires ValidData(s,op1)
        requires ValidData(s,op2)
        requires sNext == evalInsRe(CALL(D(Void),stateOutputDump(op1,op2)),s)
        requires ValidInstruction(s,CALL(D(Void),stateOutputDump(op1,op2)));
        requires s.o == Nil

        ensures |b| == 4
        ensures ValidBehavior(b);
        ensures ValidOperand(last(b),D(Void));
        // ensures ValidOperand(b[1],op2);
        ensures behaviorOutput(b) == [Nil,Out(op1),Out(op2),Out(op2)];
        ensures NextStep(s,sNext,Step.evalInsStep(CALL(D(Void),stateOutputDump(op1,op2))));
        ensures StateNext(s,sNext);
        ensures ValidState(sNext);
        ensures sNext.o == SubOut([Out(op1),Out(op2),Out(op2)]);

    {
        reveal_behaviorOutput();
        var subB := [s] + evalCodeRE(Block(stateOutputDump(op1,op2)),s);// alBlockRE(stateOutputDump(op1,op2),s);
        assert stateOutputDump(op1,op2) == [Ins(RET(D(op1))),Ins(RET(D(op2)))];

        var step,remainder,subBehavior := unwrapBlockWitness(subB,stateOutputDump(op1,op2),s);
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        
        assert subB[0] == s;
        assert NextStep(subB[0],subB[1],Step.evalInsStep(RET(D(op1))));
        assert ValidState(subB[1]);
        assert subB[1].o == Out(op1);
        assert NextStep(subB[1],subB[2],Step.evalInsStep(RET(D(op2))));
        assert ValidState(subB[2]);
        assert subB[2].o == Out(op2);
        assert subB[2] == subB[3];
        equalStatesAreStutter(subB[2],subB[3]);
        assert StateNext(subB[2],subB[3]);
        assert behaviorOutput(subB) == [Nil,Out(op1),Out(op2),Out(op2)];
        assert sNext == evalInsRe(CALL(D(Void),stateOutputDump(op1,op2)),s);
        assert sNext.ok;
        var rest := evalBlockRE(stateOutputDump(op1,op2),s);
        assert subB == [s] + rest;
        assert behaviorOutput(rest) == [Out(op1),Out(op2),Out(op2)];
        assert sNext.o == SubOut(behaviorOutput(rest));
        return subB;
    }



    lemma unwrapFwriteWitness(s:state,dst:operand,ptr:operand, size:nat, cnt:nat, file:operand,sNext:state) returns (b:behavior)
        requires ValidState(s)
        requires ValidOperand(s,ptr)
        requires ValidOperand(s,dst)
        requires isInt(OperandContents(s,dst));
        requires sNext == evalInsRe(CALL(dst,fwrite(ptr,size,cnt,file)),s)
        requires ValidInstruction(s,CALL(dst,fwrite(ptr,size,cnt,file)));
        // ensures 
        ensures |b| > 0
        ensures ValidBehavior(b);
        ensures ValidOperand(last(b),dst);
        ensures behaviorOutput(b) == [Out(OperandContents(s,ptr)),Out(OperandContents(s,ptr))];
        ensures b == evalBlockRE(fwrite(ptr,size,cnt,file),s);
        ensures NextStep(s,sNext,Step.evalInsStep(CALL(dst,fwrite(ptr,size,cnt,file))));
        ensures StateNext(s,sNext);
        ensures ValidState(sNext);
        ensures isInt(OperandContents(sNext,dst));
        ensures OperandContents(sNext,dst).itype.size == OperandContents(s,dst).itype.size;
        ensures OperandContents(sNext,dst).itype.signed == OperandContents(s,dst).itype.signed;


    {
        // assert ValidInstruction(s,CALL(dst,fwrite(ptr,size,cnt,file)));
        var subB := evalBlockRE(fwrite(ptr,size,cnt,file),s);
        assert fwrite(ptr,size,cnt,file) == [Ins(RET(ptr)),CNil];
        var metaB := evalCodeRE(Ins(RET(ptr)),s);
        assert ValidInstruction(s,RET(ptr));
        assert metaB == [evalInsRe(RET(ptr),s)];
        var s' := s.(o := Out(OperandContents(s,ptr)));
        assert metaB == [s'];
        assert ValidState(s');
        var theRest := evalBlockRE([CNil],s');
        assert theRest == [s'];
        assert subB == [s',s'];
        assert NextStep(subB[0],subB[1],Step.stutterStep());
        // assert validEvalIns(ins,s,s');
        assert sNext.ok ==> NextStep(s,sNext,Step.evalInsStep(CALL(dst,fwrite(ptr,size,cnt,file))));
        return subB;
    }


}

//  lemma unwrapVulnBehaviors(s:state, input:operand, c:codeRe) returns (preB:behavior)
//         requires ValidState(s);
//         requires validStartingState(s);
//         requires c == challenge_prob_5_code_write_encrypted_simple();

//         // -- input is valid -- ie. valid 16 bit integer 
//         requires validInput(s,input);
        
//         // ensures ValidBehaviorNonTrivial(preB);
//         ensures BehaviorEvalsCode(challenge_prob_5_code_write_encrypted_simple(),preB);
//         ensures |preB| == 9;
//         ensures preB[0] == s;
//                 ensures StateNext(preB[0],preB[1]);

//         ensures StateNext(preB[1],preB[2]);
//                 ensures ValidState(preB[0]);
//         ensures ValidState(preB[1]);

//         ensures ValidState(preB[2]);
//         ensures preB[2] == preB[3];
//         ensures ValidState(preB[3]);
//         ensures preB[3] == preB[4];
//         ensures ValidState(preB[4]);
//         ensures ValidState(preB[5]);
//         ensures StateNext(preB[0],preB[1]);

//         ensures StateNext(preB[1],preB[2]);

//         ensures StateNext(preB[2],preB[3]);

//         ensures StateNext(preB[3],preB[4]);
//         ensures StateNext(preB[4],preB[5]);

//         ensures StateNext(preB[5],preB[6]);
//         ensures ValidState(preB[6]);
//         ensures StateNext(preB[6],preB[7]);
//         ensures ValidState(preB[7]);
//         ensures StateNext(preB[7],preB[8]);
//         ensures ValidState(preB[8]);
//         ensures preB == [s] + evalCodeRE(c,s);
//         // ensures 
//         ensures behaviorOutput(preB) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(Ptr(0,0,0,1)),Nil,Nil];


//     {
//         reveal_BehaviorEvalsCode();
//         // reveal_ValidBehavior();

//         var call:operand := LV("call");
//         var call1:operand := LV("call1");
//         var mblock:operand := LV("mblock");
//         var call2 :=LV("call2");
//         var call3 := LV("call3");
//                 assert OperandContents(s,call3).itype.size == 4;

//         var cmp := LV("cmp");
//         var IV_SIZE := D(Int(16,IntType(4,false)));
//         var KEY := D(Int(16,IntType(4,false)));
//         var cipherText := D(Ptr(0,0,0,1));
//         var bytes_written := D(Ptr(0,0,0,1));

//         // var c := challenge_prob_5_code_write_encrypted_simple();
//         assert |c.block| == 7;
//         preB := [s] + evalCodeRE(c,s);
       
//         var step,remainder,subBehavior := unwrapBlockWitness(preB,c.block,s);

//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
//             step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        
//         assert preB[0] == s;
//         assert preB[1] == evalInsRe(CALL(call,malloc(Int(0,IntType(8,false)))),s);
//         assert ValidOperand(preB[1],call);

//         assert NextStep(preB[1],preB[2],Step.evalInsStep(LLVM_MEMCPY(call,mblock,1,false)));
//         assert StateNext(preB[1],preB[2]);
//         assert ValidState(preB[2]);
//         assert preB[2] == evalInsRe(LLVM_MEMCPY(call,mblock,1,false),preB[1]);
// // 
//         assert preB[2] == preB[3];
//         assert NextStep(preB[2],preB[3],Step.evalInsStep(CALL(call1,malloc(Ptr(0,0,0,1)))));
//         assert ValidState(preB[3]);

//         assert NextStep(preB[3],preB[4],Step.evalInsStep(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))));
//         assert preB[3] == preB[4];
//         assert ValidState(preB[4]);
        
//         assert NextStep(preB[4],preB[5],Step.evalInsStep(STORE(call2,bytes_written)));
//         assert ValidState(preB[5]);
        

//         assert ValidInstruction(preB[5],CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
//         assert preB[6] == evalInsRe(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))),preB[5]);
//         var subB := unwrapFwriteWitness(preB[5],call3,bytes_written,4,1,D(Ptr(0,0,0,1)),preB[6]);

//         assert behaviorOutput(subB) == [Out(OperandContents(preB[5],bytes_written)),Out(OperandContents(preB[5],bytes_written))];
//         assert OperandContents(preB[5],bytes_written) == Ptr(0,0,0,1);
//         assert ValidBehavior(subB);
//         assert ValidOperand(last(subB),call3);

//         assert NextStep(preB[5],preB[6],Step.evalInsStep(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))));
//         // assert preB[6].ok;

//         // assert preB[6].o == Out(OperandContents(preB[5],bytes_written));// == stateUpdateVar(last(subB),call3,OperandContents(last(subB),call3));
//         assert StateNext(preB[5],preB[6]);
//         assert ValidState(preB[6]);
        
//         assert cmp.LV?;
//         // var r := D(Int(0,IntType(4,false)));
//         // assert  IntFits(r.d.val,r.d.itype);
//         var src2 := validZero16bitInt(preB[6]);
//         assert ValidOperand(preB[6],call3);// 
//         assert ValidOperand(preB[6],src2);
//         assert && isInt(OperandContents(preB[6],call3));// 
//         assert && isInt(OperandContents(preB[6],src2));
//         assert OperandContents(preB[6],call3).itype.size == 4;
//         assert !OperandContents(preB[6],call3).itype.signed;
//         intsTypeMatch(OperandContents(preB[6],call3),OperandContents(preB[6],src2));
//         assert typesMatch(OperandContents(preB[6],call3),OperandContents(preB[6],src2));

//         // assert (Int(1,IntType(4,false))) == OperandContents(preB[6],call3);
//         assert ValidInstruction(preB[6],ICMP(cmp,eq,4,call3,src2));

//         assert preB[7] == evalInsRe(ICMP(cmp,eq,4,call3,src2),preB[6]);
//         // var s' := stateUpdateVar(preB[6],cmp,evalICMP(eq,4,OperandContents(preB[6],call3),OperandContents(preB[6],src2)));


//         assert NextStep(preB[6],preB[7],Step.evalInsStep(ICMP(cmp,eq,4,call3,src2)));
//         assert StateNext(preB[6],preB[7]);
//         assert ValidState(preB[7]);

//         // // // // LAST STEP
//         assert preB[7] == preB[8];
//         equalStatesAreStutter(preB[7],preB[8]);
//         // assert ValidState(preB[8]);
//         // assert NextStep(preB[7],preB[8],Step.stutterStep());
//         assert StateNext(preB[7],preB[8]);

//         // assert ValidBehaviorNonTrivial(preB);
//         // assert BehaviorEvalsCode(c,preB);
//         assert |preB| == 9;
//         assert behaviorOutput(preB) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(preB[5].lvs["bytes_written"]),Nil,Nil];


//     }

    // lemma test(s:state, input:operand) returns (preB:behavior)
    //     requires ValidState(s);
    //     requires validStartingState(s);

    //     // -- input is valid -- ie. valid 16 bit integer 
    //     requires validInput(s,input);

    // {
    //     reveal_ValidBehavior();
    //     reveal_BehaviorEvalsCode();
    //     var c := challenge_prob_5_code_write_encrypted_simple();
    //     var x := unwrapVulnBehaviors(s,input,c);
    //     assert ValidBehaviorNonTrivial(x);
    //     assert BehaviorEvalsCode(c,x);

    //     // assert behaviorOutput(x) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(x[5].lvs["bytes_written"]),Nil,Nil];

    //     // assert BehaviorEvalsCode(c,preB);
    // }
