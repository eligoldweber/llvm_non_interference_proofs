include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"


module challenge6Code{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory


    function challenge_prob_5_code_write_encrypted_simple():codeRe
    {

       // [temp] dummy ptrs
        // var call := D(Ptr(0,0,0,1));
        var call := LV("call");

        var mblock := D(Ptr(0,0,0,1));
        var call1 := LV("call1");
        // var call2 := D(Ptr(0,0,0,1));
        var call2 := LV("call2");//D(Int(0,IntType(1,false)));
        var call3 := LV("call3");//D(Int(1,IntType(4,false)));

        // var call3 := D(Ptr(0,0,0,1));
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := LV("cmp");//D(Int(0,IntType(1,false)));
        var cmp5 := D(Int(0,IntType(1,false)));
 
        var var_1 := D(Ptr(0,0,0,1));
        var var_2 := D(Int(0,IntType(4,false)));
        var var_3 := D(Ptr(0,0,0,1));
    
        var conv := D(Int(0,IntType(8,false)));


    //   %bytes_written = alloca i32, align 4
    //   call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %0) #24
    //   %call = tail call noalias align 16 dereferenceable_or_null(112) i8* @malloc(i64 112) #24
    //   tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* noundef nonnull align 16 dereferenceable(112) %call, i8* noundef nonnull align 8 dereferenceable(112) getelementptr inbounds (%struct.MBlock, %struct.MBlock* @mblock, i64 0, i32 0, i64 0), i64 112, i1 false)
    //   %call1 = tail call noalias align 16 dereferenceable_or_null(120) i8* @malloc(i64 120) #24
    //   %call2 = tail call i32 @encrypt(i8* %call, i32 112, i8* getelementptr inbounds ([32 x i8], [32 x i8]* @KEY, i64 0, i64 0), i8* getelementptr inbounds ([16 x i8], [16 x i8]* @IV, i64 0, i64 0), i8* %call1) #24
    //   store i32 %call2, i32* %bytes_written, align 4, !tbaa !3
    //   %1 = load %struct._IO_FILE*, %struct._IO_FILE** @wfd, align 8, !tbaa !14
    //   %call3 = call i64 @fwrite(i8* nonnull %0, i64 4, i64 1, %struct._IO_FILE* %1)
    //   %cmp = icmp eq i64 %call3, 0
    //   br i1 %cmp, label %if.then, label %if.end
    
    //main function block
       Block([Ins(CALL(call,malloc(Int(0,IntType(8,false))))),
              Ins(LLVM_MEMCPY(call,mblock,1,false)),
              Ins(CALL(call1,malloc(Ptr(0,0,0,1)))),
              Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))),
              Ins(STORE(call2,bytes_written)),
              Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))),
              Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false)))))])
    }

 
    function encrypt(plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand):codeSeq
    {
        [CNil]
    }

    function encrypt_side_effects(plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand):codeSeq
    {

        [Ins(LLVM_MEMCPY(KEY,D(Ptr(0,0,0,1)),1,false))] + encrypt(plainText,size,KEY,IV,cipherText)
        // lvm_Codes(Ins(LLVM_MEMCPY(KEY,D(Ptr(0,0,0,1)),1,false)),
        //           encrypt(plainText,size,KEY,IV,cipherText))    
    }


    function initialize_write(char_ptr:Data, size:Data):codeSeq
    {
        [CNil]
    }

       function encryptEmpty():codeSeq
    {
        [CNil]
    }

    function perror():codeSeq
    {
        [CNil]
    }

    function free(ptr:Data):codeSeq
    {
        [CNil]
    }

    function malloc(ptr:Data):codeSeq
    {
        [CNil]
    }

    function fwrite(ptr:operand, size:nat, cnt:nat, file:operand):codeSeq
    {
        [Ins(RET(ptr)),CNil]
    }

///////////////////////////////////////

    predicate validInput(s:state, input:operand)
        requires ValidState(s)
    {
        && s.o.Nil?
    }


    predicate validStartingState(s:state)
    {
        var call := LV("call");
        var call1 := LV("call1");
        var call2 := LV("call2");
        var call3 := LV("call3");
        var mblock := LV("mblock");
        var bytes_written := LV("bytes_written");
        var cmp := LV("cmp");
        && ValidOperand(s,call)
        && ValidOperand(s,call1)
        && ValidOperand(s,call2)
        && ValidOperand(s,call3)
        && ValidOperand(s,mblock)
        && ValidOperand(s,cmp)
        && ValidOperand(s,bytes_written)
        && s.lvs["call"].Ptr?
        && s.lvs["call1"].Ptr?
        && s.lvs["call2"].Int?
        && s.lvs["call3"].Int?
        && s.lvs["mblock"].Ptr?
        && s.lvs["bytes_written"].Ptr?
        && s.lvs["cmp"].Int?
        && s.lvs["call"] == (Ptr(0,0,0,1))
        && s.lvs["call1"] == (Ptr(0,0,0,1))
        && s.lvs["call2"] == (Int(0,IntType(1,false)))
        && s.lvs["mblock"] == (Ptr(0,0,0,1))
        && s.lvs["bytes_written"] == (Ptr(0,0,0,1))
        && s.lvs["call3"] == (Int(1,IntType(4,false)))
        && s.lvs["cmp"] == Int(0,IntType(1,false))
        && s.m.mem[0][0].mb? 
        && s.m.mem[0][0].size == 1
        
    }

    lemma unwrapVulnBehaviors(s:state, input:operand) returns (postB:behavior)
        requires ValidState(s);
        requires validStartingState(s);

        // -- input is valid -- ie. valid 16 bit integer 
        requires validInput(s,input);
        
        ensures ValidBehaviorNonTrivial(postB);
        ensures BehaviorEvalsCode(challenge_prob_5_code_write_encrypted_simple(),postB);
        ensures |postB| == 9;
        ensures behaviorOutput(postB) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(s.lvs["bytes_written"]),Nil,Nil];

    {
        reveal_BehaviorEvalsCode();
        // var call := "call";
        reveal_ValidBehavior();
        // reveal_ValidData();
        var call:operand := LV("call");
        var call1:operand := LV("call1");

        var mblock:operand := LV("mblock");
        var call2 :=LV("call2");
        var call3 := LV("call3");
        var cmp := LV("cmp");

        // assert ValidOperand(s,call2);
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var c := challenge_prob_5_code_write_encrypted_simple();
        assert forall cs :: cs in c.block ==> !cs.CNil?;
        assert |c.block| == 7;
        postB := [s] + evalCodeRE(c,s);
       
        var step,remainder, subBehavior := unwrapBlockWitness(postB,c.block,s);
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        
        assert postB[0] == s;
        assert postB[1] == evalInsRe(CALL(call,malloc(Int(0,IntType(8,false)))),s);
        assert ValidOperand(postB[1],call);

        assert NextStep(postB[1],postB[2],Step.evalInsStep(LLVM_MEMCPY(call,mblock,1,false)));
        assert StateNext(postB[1],postB[2]);
        assert ValidState(postB[2]);
        assert postB[2] == evalInsRe(LLVM_MEMCPY(call,mblock,1,false),postB[1]);
// 
        assert postB[2] == postB[3];
        //  assert ValidData(postB[3],OperandContents(postB[3],call1));
        // assert validEvalIns(CALL(call1,malloc(Ptr(0,0,0,1))),postB[2],postB[3]);
        assert NextStep(postB[2],postB[3],Step.evalInsStep(CALL(call1,malloc(Ptr(0,0,0,1)))));
        assert ValidState(postB[3]);

        // assert ValidInstruction(postB[3],CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText)));
        // assert c.block[3] == Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText)));
        assert NextStep(postB[3],postB[4],Step.evalInsStep(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))));
        assert postB[3] == postB[4];
        assert ValidState(postB[4]);
        
        // assert ValidInstruction(postB[4],STORE(call2,bytes_written));
        // assert c.block[4] == Ins(STORE(call2,bytes_written));
        // var s' := postB[4].(m := evalStore(postB[4].m,OperandContents(postB[4],bytes_written).bid,OperandContents(postB[4],bytes_written).offset,OperandContents(postB[4],call2)));
        // assert MemValid(s'.m);
        assert NextStep(postB[4],postB[5],Step.evalInsStep(STORE(call2,bytes_written)));
        assert ValidState(postB[5]);
        

        assert ValidInstruction(postB[5],CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
        assert postB[6] == evalInsRe(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))),postB[5]);
        var subB := unwrapFwriteWitness(postB[5],call3,bytes_written,4,1,D(Ptr(0,0,0,1)),postB[6]);
        // var subB := evalBlockRE(fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))),postB[5]);
        // assert fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))) == [Ins(RET(bytes_written)),CNil];
        // var metaB := evalCodeRE(Ins(RET(bytes_written)),postB[5]);
        // var s' := postB[5].(o := Out(OperandContents(postB[5],bytes_written)));
        // assert metaB == [s'];
        // assert ValidState(s');
        // var theRest := evalBlockRE([CNil],s');
        // assert theRest == [s'];
        // assert subB == [s',s'];
        // assert NextStep(subB[0],subB[1],Step.stutterStep());
        assert behaviorOutput(subB) == [Out(OperandContents(postB[5],bytes_written)),Out(OperandContents(postB[5],bytes_written))];

        assert ValidBehavior(subB);
        assert ValidOperand(last(subB),call3);

        // var stepS,remainderS, subBehaviorS := unwrapBlockWitness(subB,(fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))),postB[5]);

        // assert subB == evalCodeRE(Ins(RET(bytes_written)),postB[5]);
        // assert |subB| == 2;
        // assert c.block[5] == Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
        assert NextStep(postB[5],postB[6],Step.evalInsStep(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))));
        assert postB[6].ok;

        assert postB[6].o == Out(OperandContents(postB[5],bytes_written));// == stateUpdateVar(last(subB),call3,OperandContents(last(subB),call3));
        // assert postB[6].o == Out(OperandContents(postB[5],bytes_written));
        assert StateNext(postB[5],postB[6]);
        assert ValidState(postB[6]);

        // // assert ValidInstruction(postB[6],ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false)))));
        // // assert c.block[6] == Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false)))));
        assert NextStep(postB[6],postB[7],Step.evalInsStep(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))));
        assert StateNext(postB[6],postB[7]);
        assert ValidState(postB[7]);

        // // LAST STEP
        assert postB[7] == postB[8];
        assert ValidState(postB[8]);
        assert NextStep(postB[7],postB[8],Step.stutterStep());
        assert StateNext(postB[7],postB[8]);

        assert ValidBehaviorNonTrivial(postB);
        assert BehaviorEvalsCode(c,postB);
        assert |postB| == 9;
        assert behaviorOutput(postB) == [Nil,Nil,Nil,Nil,Nil,Nil,Out(postB[5].lvs["bytes_written"]),Nil,Nil];
        // assert NextStep(postB[5],postB[6],Step.evalInsStep(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))));


                // assert postB[3] == evalInsRe(CALL(call1,malloc(Ptr(0,0,0,1))),s);

        // assert NextStep(postB[2],postB[3],Step.evalInsStep(CALL(call1,malloc(Ptr(0,0,0,1)))));
        // assert StateNext(postB[2],postB[3]);


    }

    lemma unwrapFwriteWitness(s:state,dst:operand,ptr:operand, size:nat, cnt:nat, file:operand,sNext:state) returns (b:behavior)
        requires ValidState(s)
        requires ValidOperand(s,ptr)
        requires ValidOperand(s,dst)
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
// **** MAIN.C MAIN WHILE LOOP ****

