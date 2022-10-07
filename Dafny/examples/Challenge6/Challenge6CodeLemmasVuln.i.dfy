include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"
include "Challenge6Code.s.dfy"
include "Challenge6Common.i.dfy"

module challenge6CodeLemmasVuln{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory
    import opened challenge6Code
    import opened challenge6common



lemma unwrapVulnBehaviors(s:state, c:codeRe) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_prob_6_code_write_encrypted_simple_vuln();
        requires validInput(s); // trivial -- no input
        
        ensures BehaviorEvalsCode(challenge_prob_6_code_write_encrypted_simple_vuln(),preB);
        ensures |preB| == 11;
        ensures preB[0] == s;
        ensures validPracticalBehavior(preB);

        ensures behaviorOutput(preB) == [Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))]),
                                        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))])];



    {
        reveal_BehaviorEvalsCode();
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
        assert |c.block| == 9;
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
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));

        assert preB[0] == s;
        assert preB[1] == evalInsRe(CALL(call,malloc(Int(0,IntType(8,false)))),s);
        assert ValidOperand(preB[1],call);

        assert NextStep(preB[1],preB[2],Step.evalInsStep(CALL(D(Void),crc32(INTEGRITY_SIZE,mblock))));
        assert StateNext(preB[1],preB[2]);
        assert ValidState(preB[2]);
        assert preB[2].o == SubOut([Nil]);
        
        assert NextStep(preB[2],preB[3],Step.evalInsStep(LLVM_MEMCPY(call,mblock,1,false)));
        assert StateNext(preB[2],preB[3]);
        assert ValidState(preB[3]);
        assert preB[3] == evalInsRe(LLVM_MEMCPY(call,mblock,1,false),preB[2]);
// 
        // assert preB[3] == preB[4];
        assert NextStep(preB[3],preB[4],Step.evalInsStep(CALL(call1,malloc(Ptr(0,0,0,1)))));
        assert ValidState(preB[4]);

        assert NextStep(preB[4],preB[5],Step.evalInsStep(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))));
        assert preB[4] == preB[5];
        assert ValidState(preB[5]);
        
        assert NextStep(preB[5],preB[6],Step.evalInsStep(STORE(call2,bytes_written)));
        assert ValidState(preB[6]);
        

        assert ValidInstruction(preB[6],CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
        assert preB[6] == evalInsRe(CALL(call3,fwrite_empty(bytes_written,4,1,D(Ptr(0,0,0,1)))),preB[6]);
        assert preB[6] == preB[7];
        assert ValidState(preB[7]);

        assert StateNext(preB[6],preB[7]);
        assert ValidState(preB[7]);
        
        assert cmp.LV?;

        var src2 := validZero16bitInt(preB[7]);
        assert ValidOperand(preB[7],call3);// 
        assert ValidOperand(preB[7],src2);
        assert && isInt(OperandContents(preB[7],call3));// 
        assert && isInt(OperandContents(preB[7],src2));
        assert OperandContents(preB[7],call3).itype.size == 4;
        assert !OperandContents(preB[7],call3).itype.signed;
        intsTypeMatch(OperandContents(preB[7],call3),OperandContents(preB[7],src2));
        assert typesMatch(OperandContents(preB[7],call3),OperandContents(preB[7],src2));

        assert ValidInstruction(preB[7],ICMP(cmp,eq,4,call3,src2));

        assert preB[8] == evalInsRe(ICMP(cmp,eq,4,call3,src2),preB[7]);

        assert NextStep(preB[7],preB[8],Step.evalInsStep(ICMP(cmp,eq,4,call3,src2)));
        assert StateNext(preB[7],preB[8]);
        assert ValidState(preB[8]);

        assert ValidInstruction(preB[8],CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE)));
        assert preB[9] == evalInsRe(CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE)),preB[8]);
        var dump := unwrapDumpWitness(preB[8],KEY,INTEGRITY_SIZE,preB[9]);
        assert NextStep(preB[8],preB[9],Step.evalInsStep(CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE))));   
        assert preB[9].o == SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))]);

//       // // // LAST STEP
        assert preB[9] == preB[10];
        equalStatesAreStutter(preB[9],preB[10]);

        assert StateNext(preB[9],preB[10]);

        assert behaviorOutput(preB) == [Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        Nil,
                                        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))]),
                                        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))])];


    }



 lemma vulnBehaviorIsValid(s:state) returns (preB:behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires validInput(s);
        // ensures ValidBehaviorNonTrivial(x);
        // ensures BehaviorEvalsCode(c,x);
    {
        reveal_ValidBehavior();
        reveal_BehaviorEvalsCode();
        var c := challenge_prob_6_code_write_encrypted_simple_vuln();
        var x := unwrapVulnBehaviors(s,c);
        assert ValidBehaviorNonTrivial(x);
        assert BehaviorEvalsCode(c,x);


    }

}
