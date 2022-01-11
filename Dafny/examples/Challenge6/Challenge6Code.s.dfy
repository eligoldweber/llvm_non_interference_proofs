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


    function challenge_prob_6_code_write_encrypted_simple_vuln():codeRe
    {


        var call := LV("call");
        var mblock := LV("mblock");
        var call1 := LV("call1");
        var call2 := LV("call2");
        var call3 := LV("call3");
        var INTEGRITY_SIZE := LV("INTEGRITY_SIZE");
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := LV("cmp");
        var cmp5 := D(Int(0,IntType(1,false)));
 
        var var_1 := D(Ptr(0,0,0,1));
        var var_2 := D(Int(0,IntType(4,false)));
        var var_3 := D(Ptr(0,0,0,1));
    
        var conv := D(Int(0,IntType(8,false)));


    //   %bytes_written = alloca i32, align 4
    //   call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %0) #24
    //   %call = tail call noalias align 16 dereferenceable_or_null(112) i8* @malloc(i64 112) #24
    //   call void @crc32(i8* %call, i64 %conv, i8* %1)
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
              Ins(CALL(D(Void),crc32(INTEGRITY_SIZE,mblock))),
              Ins(LLVM_MEMCPY(call,mblock,1,false)),
              Ins(CALL(call1,malloc(Ptr(0,0,0,1)))),
              Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))),
              Ins(STORE(call2,bytes_written)),
              Ins(CALL(call3,fwrite_empty(bytes_written,4,1,D(Ptr(0,0,0,1))))),
              Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),
              Ins(CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE)))])
    }

    function challenge_prob_6_code_write_encrypted_simple_patch():codeRe
    {

       // [temp] dummy ptrs
       
        var call := LV("call");

        var mblock := LV("mblock");
        var call1 := LV("call1");
        var call2 := LV("call2");
        var call3 := LV("call3");
        var INTEGRITY_SIZE := LV("INTEGRITY_SIZE");
        var digestLength :=  LV("digestLength");
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := LV("cmp");
        var cmp5 := D(Int(0,IntType(1,false)));
 


    //   %bytes_written = alloca i32, align 4
    //   call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %0) #24
    //   %call = tail call noalias align 16 dereferenceable_or_null(112) i8* @malloc(i64 112) #24
    //   call void @crc32(i8* %call, i64 %conv, i8* %1)
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
              Ins(CALL(D(Void),digest(digestLength,INTEGRITY_SIZE,mblock))),
              Ins(LLVM_MEMCPY(call,mblock,1,false)),
              Ins(CALL(call1,malloc(Ptr(0,0,0,1)))),
              Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))),
              Ins(STORE(call2,bytes_written)),
              Ins(CALL(call3,fwrite_empty(bytes_written,4,1,D(Ptr(0,0,0,1))))),
              Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),
              Ins(CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE)))])
    }


    function challenge_prob_6_code_write_encrypted_simple_patch_side_effect():codeRe
    {

        var call := LV("call");

        var mblock := D(Ptr(0,0,0,1));
        var call1 := LV("call1");
        var call2 := LV("call2");
        var call3 := LV("call3");
        var INTEGRITY_SIZE := LV("INTEGRITY_SIZE");
        var digestLength :=  LV("digestLength");

        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := LV("cmp");



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
            Ins(CALL(digestLength,digest_side_effects(digestLength,INTEGRITY_SIZE,mblock))),
            Ins(LLVM_MEMCPY(call,mblock,1,false)),
            Ins(CALL(call1,malloc(Ptr(0,0,0,1)))),
            Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))),
            Ins(STORE(call2,bytes_written)),
            Ins(CALL(call3,fwrite_empty(bytes_written,4,1,D(Ptr(0,0,0,1))))),
            Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),
            Ins(CALL(D(Void),stateOutputDump(KEY,INTEGRITY_SIZE)))])
    }

    function digest_side_effects(digestLength:operand,INTEGRITY_SIZE:operand,mblock:operand):codeSeq
    {

        [Ins(SUB(INTEGRITY_SIZE,1,INTEGRITY_SIZE,D(Int(1,IntType(1,false)))))] + digest(digestLength,INTEGRITY_SIZE,mblock)
    }
    
    function stateOutputDump(op1:operand,op2:operand):codeSeq
    {
        [Ins(RET(op1)),
         Ins(RET(op2))]
    }
 
    function encrypt(plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand):codeSeq
    {
        [CNil]
    }

     
    function crc32(INTEGRITY_SIZE:operand,mblock:operand):codeSeq //stub
    {
        [CNil]
    }

    function digest(digest:operand,INTEGRITY_SIZE:operand,mblock:operand):codeSeq //stub
    {
        [CNil]
    }

    function encrypt_side_effects(INTEGRITY_SIZE:operand):codeSeq
    {

        [Ins(SUB(INTEGRITY_SIZE,1,INTEGRITY_SIZE,D(Int(1,IntType(1,false)))))] + [CNil]
        // [Ins(LLVM_MEMCPY(KEY,D(Ptr(0,0,0,1)),1,false))] + encrypt(plainText,size,KEY,IV,cipherText)
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

    function fwrite_empty(ptr:operand, size:nat, cnt:nat, file:operand):codeSeq
    {
        [CNil]
    }

///////////////////////////////////////

    predicate validInput(s:state)
        requires ValidState(s)
    {
        && s.o.Nil?
    }


    predicate validStartingState(s:state)
        // requires ValidState(s)
    {
        var call := LV("call");
        var call1 := LV("call1");
        var call2 := LV("call2");
        var call3 := LV("call3");
        var call4 := LV("call4");
        var mblock := LV("mblock");
        var bytes_written := LV("bytes_written");
        var cmp := LV("cmp");
        var INTEGRITY_SIZE := LV("INTEGRITY_SIZE");
        var digestLength := LV("digestLength");
        && ValidOperand(s,call)
        && ValidOperand(s,call1)
        && ValidOperand(s,call2)
        && ValidOperand(s,call3)
        && ValidOperand(s,call4)
        && ValidOperand(s,mblock)
        && ValidOperand(s,cmp)
        && ValidOperand(s,bytes_written)
        && ValidOperand(s,INTEGRITY_SIZE)
        && ValidOperand(s,digestLength)
        && s.lvs["call"].Ptr?
        && s.lvs["call1"].Ptr?
        && s.lvs["call2"].Int?
        && s.lvs["call3"].Int?
        && s.lvs["call4"].Int?
        && s.lvs["mblock"].Ptr?
        && s.lvs["bytes_written"].Ptr?
        && s.lvs["cmp"].Int?
        && s.lvs["INTEGRITY_SIZE"].Int?
        && s.lvs["digestLength"].Int?
        && s.lvs["call"] == (Ptr(0,0,0,1))
        && s.lvs["call1"] == (Ptr(0,0,0,1))
        && s.lvs["call2"] == (Int(0,IntType(1,false)))
        && s.lvs["mblock"] == (Ptr(0,0,0,1))
        && s.lvs["bytes_written"] == (Ptr(0,0,0,1))
        && s.lvs["call3"] == (Int(1,IntType(4,false)))
        && s.lvs["call4"] == (Int(1,IntType(4,false)))
        && s.lvs["cmp"] == Int(0,IntType(1,false))
        && s.lvs["INTEGRITY_SIZE"] == Int(4,IntType(1,false))
        && s.lvs["digestLength"] == Int(0,IntType(1,false))
        && s.m.mem[0][0].mb? 
        && s.m.mem[0][0].size == 1
        
    }

   
}
// **** MAIN.C MAIN WHILE LOOP ****

