include "../../LLVM/llvm.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"


module challenge5Code{
    import opened control_flow
    import opened LLVM_def
    import opened types

    function challenge_prob_5_code_write_encrypted():lvm_code
    {

       // [temp] dummy ptrs
        var call := D(Ptr(0,0,0,1));
        var mblock := D(Ptr(0,0,0,1));
        var call1 := D(Ptr(0,0,0,1));
        // var call2 := D(Ptr(0,0,0,1));
        var call2 := D(Int(0,IntType(1,false)));
        var call3 := D(Int(1,IntType(4,false)));

        // var call3 := D(Ptr(0,0,0,1));
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := Int(16,IntType(4,false));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := D(Int(0,IntType(1,false)));
        var cmp5 := D(Int(0,IntType(1,false)));
 
        var var_1 := D(Ptr(0,0,0,1));
        var var_2 := D(Int(0,IntType(4,false)));
        var var_3 := D(Ptr(0,0,0,1));
    
        var conv := D(Int(0,IntType(8,false)));

        // if.end8:                                          ; preds = %if.then7, %if.end
        //   tail call void @free(i8* nonnull %call) #24
        //   tail call void @free(i8* %call1) #24
        //   tail call void @initialize_write(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @IV, i64 0, i64 0), i32 16)
        //   call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %0) #24
        //   ret void
        var if_end8:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),free(call.d))),
                                      lvm_Codes(Ins(CALL(D(Void),free(call1.d))),  
                                      lvm_Codes(Ins(CALL(D(Void),initialize_write(call1.d,IV_SIZE))),  
                                      lvm_Codes(Ins(RET(D(Void))),lvm_CNil()))))); 

        // if.then7:                                         ; preds = %if.end
        //   tail call void @perror(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.5, i64 0, i64 0)) #23
        //   br label %if.end8
        var if_then7:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end8,lvm_CNil()))), lvm_CNil())));
        
        // if.end:                                           ; preds = %if.then, %entry
        //   %2 = load i32, i32* %bytes_written, align 4, !tbaa !3
        //   %conv = sext i32 %2 to i64
        //   %3 = load %struct._IO_FILE*, %struct._IO_FILE** @wfd, align 8, !tbaa !14
        //   %call4 = tail call i64 @fwrite(i8* %call1, i64 1, i64 %conv, %struct._IO_FILE* %3)
        //   %cmp5 = icmp eq i64 %call4, 0
        //   br i1 %cmp5, label %if.then7, label %if.end8
        var if_end:code := lvm_Block(lvm_Codes(Ins(LOAD(var_2,4,bytes_written)),
                                     lvm_Codes(Ins(SEXT(conv,8,var_2,8)),
                                     lvm_Codes(Ins(LOAD(var_3,4,D(Ptr(0,0,0,1)))),
                                     lvm_Codes(Ins(CALL(call4,fwrite(call1,1,conv.d.val,D(Ptr(0,0,0,1))))),
                                     lvm_Codes(Ins(ICMP(cmp5,eq,8,call4,D(Int(0,IntType(8,false))))),
                                     lvm_Codes(Ins(BR(cmp,                                          
                                        lvm_Codes(if_then7,lvm_CNil()),
                                        lvm_Codes(if_end8,lvm_CNil()))),lvm_CNil())))))));


        // if.then:                                          ; preds = %entry
        //   tail call void @perror(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.4, i64 0, i64 0)) #23
        //   br label %if.end
        var if_then:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end,lvm_CNil()))), lvm_CNil())));

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
        lvm_Block(lvm_Codes(Ins(CALL(call,malloc(Int(0,IntType(8,false))))),
                  lvm_Codes(Ins(LLVM_MEMCPY(call,mblock,1,false)),
                  lvm_Codes(Ins(CALL(call1,malloc(call1.d))),
                  lvm_Codes(Ins(CALL(call2,encryptEmpty())),
                  lvm_Codes(Ins(STORE(call2,bytes_written)),
                  lvm_Codes(Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))),
                  lvm_Codes(Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),
                  lvm_Codes(Ins(BR(cmp,                                          
                    lvm_Codes(if_then,lvm_CNil()),
                    lvm_Codes(if_end,lvm_CNil()))),lvm_CNil())))))))))                           

    }

    function challenge_prob_5_code_write_encrypted_simple():lvm_code
    {

       // [temp] dummy ptrs
        var call := D(Ptr(0,0,0,1));
        var mblock := D(Ptr(0,0,0,1));
        var call1 := D(Ptr(0,0,0,1));
        // var call2 := D(Ptr(0,0,0,1));
        var call2 := D(Int(0,IntType(1,false)));
        var call3 := D(Int(1,IntType(4,false)));

        // var call3 := D(Ptr(0,0,0,1));
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := D(Int(0,IntType(1,false)));
        var cmp5 := D(Int(0,IntType(1,false)));
 
        var var_1 := D(Ptr(0,0,0,1));
        var var_2 := D(Int(0,IntType(4,false)));
        var var_3 := D(Ptr(0,0,0,1));
    
        var conv := D(Int(0,IntType(8,false)));

        // if.end8:                                          ; preds = %if.then7, %if.end
        //   tail call void @free(i8* nonnull %call) #24
        //   tail call void @free(i8* %call1) #24
        //   tail call void @initialize_write(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @IV, i64 0, i64 0), i32 16)
        //   call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %0) #24
        //   ret void
        var if_end8:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),free(call.d))),
                                      lvm_Codes(Ins(CALL(D(Void),free(call1.d))),  
                                      lvm_Codes(Ins(CALL(D(Void),initialize_write(call1.d,IV_SIZE.d))),  
                                      lvm_Codes(Ins(RET(D(Void))),lvm_CNil()))))); 

        // if.then7:                                         ; preds = %if.end
        //   tail call void @perror(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.5, i64 0, i64 0)) #23
        //   br label %if.end8
        var if_then7:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end8,lvm_CNil()))), lvm_CNil())));
        
        // if.end:                                           ; preds = %if.then, %entry
        //   %2 = load i32, i32* %bytes_written, align 4, !tbaa !3
        //   %conv = sext i32 %2 to i64
        //   %3 = load %struct._IO_FILE*, %struct._IO_FILE** @wfd, align 8, !tbaa !14
        //   %call4 = tail call i64 @fwrite(i8* %call1, i64 1, i64 %conv, %struct._IO_FILE* %3)
        //   %cmp5 = icmp eq i64 %call4, 0
        //   br i1 %cmp5, label %if.then7, label %if.end8
        var if_end:code := lvm_Block(lvm_Codes(Ins(LOAD(var_2,4,bytes_written)),
                                     lvm_Codes(Ins(SEXT(conv,8,var_2,8)),
                                     lvm_Codes(Ins(LOAD(var_3,4,D(Ptr(0,0,0,1)))),
                                     lvm_Codes(Ins(CALL(call4,fwrite(call1,1,conv.d.val,D(Ptr(0,0,0,1))))),
                                     lvm_Codes(Ins(ICMP(cmp5,eq,8,call4,D(Int(0,IntType(8,false))))),
                                     lvm_Codes(Ins(BR(cmp,                                          
                                        lvm_Codes(if_then7,lvm_CNil()),
                                        lvm_Codes(if_end8,lvm_CNil()))),lvm_CNil())))))));


        // if.then:                                          ; preds = %entry
        //   tail call void @perror(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.4, i64 0, i64 0)) #23
        //   br label %if.end
        var if_then:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end,lvm_CNil()))), lvm_CNil())));

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
        lvm_Block(lvm_Codes(Ins(CALL(call,malloc(Int(0,IntType(8,false))))),
                  lvm_Codes(Ins(LLVM_MEMCPY(call,mblock,1,false)),
                  lvm_Codes(Ins(CALL(call1,malloc(call1.d))),
                  lvm_Codes(Ins(CALL(call2,encrypt(call,4,KEY,IV_SIZE,cipherText))),
                  lvm_Codes(Ins(STORE(call2,bytes_written)),
                  lvm_Codes(Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))),
                  lvm_Codes(Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),lvm_CNil()))))))))                         



    }

function challenge_prob_5_code_write_encrypted_simple_side_effect():lvm_code
    {

       // [temp] dummy ptrs
        var call := D(Ptr(0,0,0,1));
        var mblock := D(Ptr(0,0,0,1));
        var call1 := D(Ptr(0,0,0,1));
        // var call2 := D(Ptr(0,0,0,1));
        var call2 := D(Int(0,IntType(1,false)));
        var call3 := D(Int(1,IntType(4,false)));

        // var call3 := D(Ptr(0,0,0,1));
        var call4 := D(Ptr(0,0,0,1));
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var bytes_written := D(Ptr(0,0,0,1));

        var cmp := D(Int(0,IntType(1,false)));
        var cmp5 := D(Int(0,IntType(1,false)));
 
        var var_1 := D(Ptr(0,0,0,1));
        var var_2 := D(Int(0,IntType(4,false)));
        var var_3 := D(Ptr(0,0,0,1));
    
        var conv := D(Int(0,IntType(8,false)));

        // if.end8:                                          ; preds = %if.then7, %if.end
        //   tail call void @free(i8* nonnull %call) #24
        //   tail call void @free(i8* %call1) #24
        //   tail call void @initialize_write(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @IV, i64 0, i64 0), i32 16)
        //   call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %0) #24
        //   ret void
        var if_end8:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),free(call.d))),
                                      lvm_Codes(Ins(CALL(D(Void),free(call1.d))),  
                                      lvm_Codes(Ins(CALL(D(Void),initialize_write(call1.d,IV_SIZE.d))),  
                                      lvm_Codes(Ins(RET(D(Void))),lvm_CNil()))))); 

        // if.then7:                                         ; preds = %if.end
        //   tail call void @perror(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.5, i64 0, i64 0)) #23
        //   br label %if.end8
        var if_then7:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end8,lvm_CNil()))), lvm_CNil())));
        
        // if.end:                                           ; preds = %if.then, %entry
        //   %2 = load i32, i32* %bytes_written, align 4, !tbaa !3
        //   %conv = sext i32 %2 to i64
        //   %3 = load %struct._IO_FILE*, %struct._IO_FILE** @wfd, align 8, !tbaa !14
        //   %call4 = tail call i64 @fwrite(i8* %call1, i64 1, i64 %conv, %struct._IO_FILE* %3)
        //   %cmp5 = icmp eq i64 %call4, 0
        //   br i1 %cmp5, label %if.then7, label %if.end8
        var if_end:code := lvm_Block(lvm_Codes(Ins(LOAD(var_2,4,bytes_written)),
                                     lvm_Codes(Ins(SEXT(conv,8,var_2,8)),
                                     lvm_Codes(Ins(LOAD(var_3,4,D(Ptr(0,0,0,1)))),
                                     lvm_Codes(Ins(CALL(call4,fwrite(call1,1,conv.d.val,D(Ptr(0,0,0,1))))),
                                     lvm_Codes(Ins(ICMP(cmp5,eq,8,call4,D(Int(0,IntType(8,false))))),
                                     lvm_Codes(Ins(BR(cmp,                                          
                                        lvm_Codes(if_then7,lvm_CNil()),
                                        lvm_Codes(if_end8,lvm_CNil()))),lvm_CNil())))))));


        // if.then:                                          ; preds = %entry
        //   tail call void @perror(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.4, i64 0, i64 0)) #23
        //   br label %if.end
        var if_then:code := lvm_Block(lvm_Codes(Ins(CALL(D(Void),perror())),
                                      lvm_Codes(Ins(UNCONDBR(lvm_Codes(if_end,lvm_CNil()))), lvm_CNil())));

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
        lvm_Block(lvm_Codes(Ins(CALL(call,malloc(Int(0,IntType(8,false))))),
                  lvm_Codes(Ins(LLVM_MEMCPY(call,mblock,1,false)),
                  lvm_Codes(Ins(CALL(call1,malloc(call1.d))),
                  lvm_Codes(Ins(CALL(call2,encrypt_side_effects(call,4,KEY,IV_SIZE,cipherText))),
                  lvm_Codes(Ins(STORE(call2,bytes_written)),
                  lvm_Codes(Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1))))),
                  lvm_Codes(Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false))))),lvm_CNil()))))))))                         



    }

    function encryptEmpty():codes
    {
        ForeignFunction
    }

    function encrypt(plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand):codes
    {
        ForeignFunction
    }

    function encrypt_side_effects(plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand):codes
    {

        lvm_Codes(Ins(LLVM_MEMCPY(plainText,cipherText,1,false)),
                  encrypt(plainText,size,KEY,IV,cipherText))    
    }


    function initialize_write(char_ptr:Data, size:Data):codes
    {
        ForeignFunction
    }

    function perror():codes
    {
        ForeignFunction
    }

    function free(ptr:Data):codes
    {
        ForeignFunction
    }

    function malloc(ptr:Data):codes
    {
        ForeignFunction
    }

    function fwrite(ptr:operand, size:nat, cnt:nat, file:operand):codes
    {
        ForeignFunction
    }

}
// **** MAIN.C MAIN WHILE LOOP ****

// do.body:                                          ; preds = %schedule_timer.exit, %cleanup
//   %report_timer.0295 = phi i64 [ %report_timer.2, %cleanup ], [ %call44, %schedule_timer.exit ]
//   %84 = call { i64, i64* } asm sideeffect "cld; rep; stosq", "={cx},={di},{ax},0,1,~{memory},~{dirflag},~{fpsr},~{flags}"(i32 0, i64 16, i64* nonnull %arrayidx47) #24, !srcloc !35
//   %85 = load i64, i64* %arrayidx51, align 8, !tbaa !36
//   %or = or i64 %85, %shl
//   store i64 %or, i64* %arrayidx51, align 8, !tbaa !36
//   store <2 x i64> <i64 0, i64 50>, <2 x i64>* %timeout, align 16, !tbaa !36
//   %call52 = call i32 @select(i32 %add, %struct.__sigset_t* nonnull %readfds, %struct.__sigset_t* null, %struct.__sigset_t* null, %struct.timeval* nonnull %tmpcast303) #24
//   %cmp53 = icmp sgt i32 %call52, 0
//   br i1 %cmp53, label %if.then55, label %if.end86

// if.then55:                                        ; preds = %do.body
//   %call56 = call i64 @read(i32 %call8, i8* nonnull %80, i64 16) #24
//   %cmp57 = icmp slt i64 %call56, 0
//   br i1 %cmp57, label %cleanup.thread, label %if.end60

// cleanup.thread:                                   ; preds = %if.then55
//   call void @perror(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.8, i64 0, i64 0)) #23
//   br label %cleanup176

// if.end60:                                         ; preds = %if.then55
//   %86 = load i64, i64* %81, align 8
//   %87 = load i64, i64* %82, align 8
//   call void @logging_handler(i64 %86, i64 %87) #24
//   %88 = trunc i64 %86 to i32
//   %and61 = and i32 %88, 536870911
//   store i32 %and61, i32* %can_id, align 8, !tbaa !37
//   %89 = and i32 %88, 15728640
//   %cmp.i261 = icmp eq i32 %89, 15728640
//   %and6.i = lshr i32 %88, 8
//   %shr7.i = and i32 %and6.i, 262143
//   %and3.i = lshr i32 %and61, 8
//   %shr10.i = and i32 %and3.i, 261888
//   %storemerge.i = select i1 %cmp.i261, i32 %shr7.i, i32 %shr10.i
//   %90 = lshr i64 %87, 16
//   %91 = trunc i64 %90 to i32
//   switch i32 %storemerge.i, label %if.end86 [
//     i32 65265, label %if.then65
//     i32 64972, label %if.then68
//     i32 60928, label %if.then74
//     i32 59904, label %if.then80
//   ]

// if.then65:                                        ; preds = %if.end60
//   %92 = and i64 %87, 51539607552
//   %tobool.not.i = icmp ne i64 %92, 0
//   %conv8.i263 = zext i1 %tobool.not.i to i8
//   store i8 %conv8.i263, i8* %brake_state.i, align 1, !tbaa !38
//   br i1 %tobool.not.i, label %if.then.i265, label %if.else.i266

// if.then.i265:                                     ; preds = %if.then65
//   %93 = lshr i64 %87, 16
//   %94 = trunc i64 %93 to i32
//   %shl.i = and i32 %94, 65280
//   %conv2.i = and i32 %91, 255
//   %add.i = or i32 %shl.i, %conv2.i
//   %cmp.not.i = icmp eq i32 %add.i, 0
//   br i1 %cmp.not.i, label %if.end86, label %land.lhs.true.i

// land.lhs.true.i:                                  ; preds = %if.then.i265
//   %95 = load i8, i8* %has_flashed17.i, align 4, !tbaa !40
//   %tobool14.not.i = icmp eq i8 %95, 0
//   br i1 %tobool14.not.i, label %if.then15.i, label %if.end86

// if.then15.i:                                      ; preds = %land.lhs.true.i
//   store i8 1, i8* %flash_lock16.i, align 2, !tbaa !41
//   br label %if.end86

// if.else.i266:                                     ; preds = %if.then65
//   store i8 0, i8* %flash_lock16.i, align 2, !tbaa !41
//   store i8 0, i8* %has_flashed17.i, align 4, !tbaa !40
//   br label %if.end86

// if.then68:                                        ; preds = %if.end60
//   %96 = lshr i64 %87, 12
//   %97 = trunc i64 %96 to i8
//   %98 = and i8 %97, 15
//   store i8 %98, i8* %signal.i, align 1, !tbaa !42
//   br label %if.end86

// if.then74:                                        ; preds = %if.end60
//   %conv12.i = trunc i64 %86 to i8
//   call void @rx_claim_routine(i8 zeroext %conv12.i, i8* nonnull %arraydecay76, i32 %call8, i32* %11)
//   br label %if.end86

// if.then80:                                        ; preds = %if.end60
//   %99 = and i32 %and3.i, 255
//   %conv81 = select i1 %cmp.i261, i32 255, i32 %99
//   %100 = load i8, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !28
//   %conv.i268 = zext i8 %100 to i32
//   %cmp.i269 = icmp eq i32 %conv81, %conv.i268
//   %cmp2.i = icmp eq i32 %conv81, 255
//   %or.cond.i = or i1 %cmp2.i, %cmp.i269
//   br i1 %or.cond.i, label %if.then.i271, label %if.end86

// if.then.i271:                                     ; preds = %if.then80
//   %call.i270 = call i64 @write(i32 %call8, i8* bitcast (%struct.can_frame* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 7) to i8*), i64 16) #24
//   %cmp4.not.i = icmp eq i64 %call.i270, 16
//   br i1 %cmp4.not.i, label %if.end86, label %if.then6.i

// if.then6.i:                                       ; preds = %if.then.i271
//   call void (i32, i8*, ...) @err(i32 1, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.14, i64 0, i64 0)) #25
//   unreachable

// if.end86:                                         ; preds = %if.then74, %if.then68, %if.end60, %if.then.i265, %land.lhs.true.i, %if.then15.i, %if.else.i266, %if.then80, %if.then.i271, %do.body
//   call void @turn_signal_routine(%struct.Bumper* %10) #24
//   call void @brake_routine(%struct.Bumper* %10) #24
//   %101 = load i8, i8* %outer_left, align 16, !tbaa !43
//   %102 = load i8, i8* %inner_left, align 1, !tbaa !44
//   %103 = load i8, i8* %inner_right, align 2, !tbaa !45
//   %104 = load i8, i8* %outer_right, align 1, !tbaa !46
//   %tobool88.not = icmp eq i8 %101, 0
//   %cond = select i1 %tobool88.not, i32 10, i32 100
//   call void @set_duty(i32 1, i32 %cond) #24
//   %tobool90.not = icmp eq i8 %102, 0
//   %cond91 = select i1 %tobool90.not, i32 10, i32 100
//   call void @set_duty(i32 2, i32 %cond91) #24
//   %tobool93.not = icmp eq i8 %103, 0
//   %cond94 = select i1 %tobool93.not, i32 10, i32 100
//   call void @set_duty(i32 3, i32 %cond94) #24
//   %tobool96.not = icmp eq i8 %104, 0
//   %cond97 = select i1 %tobool96.not, i32 10, i32 100
//   call void @set_duty(i32 4, i32 %cond97) #24
//   %cond100 = select i1 %tobool88.not, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.10, i64 0, i64 0)
//   %cond103 = select i1 %tobool90.not, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.10, i64 0, i64 0)
//   %cond106 = select i1 %tobool93.not, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.10, i64 0, i64 0)
//   %cond109 = select i1 %tobool96.not, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.11, i64 0, i64 0), i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.10, i64 0, i64 0)
//   %105 = load i32, i32* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 6), align 4, !tbaa !47
//   %106 = load i8, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !28
//   %conv110 = zext i8 %106 to i32
//   %call111 = call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([50 x i8], [50 x i8]* @.str.9, i64 0, i64 0), i8* %cond100, i8* %cond103, i8* %cond106, i8* %cond109, i32 %105, i32 %conv110)
//   %107 = load i32, i32* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 6), align 4, !tbaa !47
//   switch i32 %107, label %cleanup [
//     i32 1, label %if.then114
//     i32 2, label %if.then121
//   ]

// if.then114:                                       ; preds = %if.end86
//   %108 = load i32, i32* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 5), align 8, !tbaa !32
//   %tobool115.not = icmp eq i32 %108, 0
//   br i1 %tobool115.not, label %cleanup, label %if.then116

// if.then116:                                       ; preds = %if.then114
//   store i32 2, i32* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 6), align 4, !tbaa !47
//   br label %cleanup

// if.then121:                                       ; preds = %if.end86
//   store i8 0, i8* %arraydecay76, align 8, !tbaa !10
//   %not.tobool88.not = xor i1 %tobool88.not, true
//   %conv127 = sext i1 %not.tobool88.not to i8
//   store i8 %conv127, i8* %arrayidx129, align 1, !tbaa !10
//   store i8 0, i8* %arrayidx131, align 2, !tbaa !10
//   %not.tobool90.not = xor i1 %tobool90.not, true
//   %conv135 = sext i1 %not.tobool90.not to i8
//   store i8 %conv135, i8* %arrayidx137, align 1, !tbaa !10
//   store i8 0, i8* %arrayidx139, align 4, !tbaa !10
//   %not.tobool93.not = xor i1 %tobool93.not, true
//   %conv143 = sext i1 %not.tobool93.not to i8
//   store i8 %conv143, i8* %arrayidx145, align 1, !tbaa !10
//   store i8 0, i8* %arrayidx147, align 2, !tbaa !10
//   %not.tobool96.not = xor i1 %tobool96.not, true
//   %conv151 = sext i1 %not.tobool96.not to i8
//   store i8 %conv151, i8* %arrayidx153, align 1, !tbaa !10
//   %109 = load i8, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !28
//   %conv154 = zext i8 %109 to i32
//   %or157 = or i32 %conv154, -1661059072
//   store i32 %or157, i32* %can_id, align 8, !tbaa !37
//   store i8 8, i8* %can_dlc, align 4, !tbaa !48
//   %call159 = call i64 @clock() #24
//   %sub = sub nsw i64 %call159, %report_timer.0295
//   %cmp161 = icmp sgt i64 %sub, 100000
//   br i1 %cmp161, label %if.then163, label %cleanup

// if.then163:                                       ; preds = %if.then121
//   %call164 = call i64 @write(i32 %call8, i8* nonnull %80, i64 16) #24
//   %cmp165.not = icmp eq i64 %call164, 16
//   br i1 %cmp165.not, label %if.end168, label %if.then167

// if.then167:                                       ; preds = %if.then163
//   call void (i32, i8*, ...) @err(i32 1, i8* getelementptr inbounds ([31 x i8], [31 x i8]* @.str.7.12, i64 0, i64 0)) #25
//   unreachable

// if.end168:                                        ; preds = %if.then163
//   %call169 = call i64 @clock() #24
//   br label %cleanup

// cleanup:                                          ; preds = %if.then116, %if.then114, %if.then121, %if.end168, %if.end86
//   %report_timer.2 = phi i64 [ %report_timer.0295, %if.then116 ], [ %report_timer.0295, %if.then114 ], [ %call169, %if.end168 ], [ %report_timer.0295, %if.then121 ], [ %report_timer.0295, %if.end86 ]
//   %110 = load i32, i32* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 4), align 4, !tbaa !34
//   %tobool.not = icmp eq i32 %110, 0
//   br i1 %tobool.not, label %do.body, label %while.end174, !llvm.loop !49

// **** END MAIN FOR LOOP ****

// **** LOGGING.C WRITE_ENCRYPTED() ****

// ; Function Attrs: nounwind uwtable
// define dso_local void @write_encrypted() local_unnamed_addr #5 {
// entry:
//   %bytes_written = alloca i32, align 4
//   %0 = bitcast i32* %bytes_written to i8*
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

// if.then:                                          ; preds = %entry
//   tail call void @perror(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.4, i64 0, i64 0)) #23
//   br label %if.end

// if.end:                                           ; preds = %if.then, %entry
//   %2 = load i32, i32* %bytes_written, align 4, !tbaa !3
//   %conv = sext i32 %2 to i64
//   %3 = load %struct._IO_FILE*, %struct._IO_FILE** @wfd, align 8, !tbaa !14
//   %call4 = tail call i64 @fwrite(i8* %call1, i64 1, i64 %conv, %struct._IO_FILE* %3)
//   %cmp5 = icmp eq i64 %call4, 0
//   br i1 %cmp5, label %if.then7, label %if.end8

// if.then7:                                         ; preds = %if.end
//   tail call void @perror(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.5, i64 0, i64 0)) #23
//   br label %if.end8

// if.end8:                                          ; preds = %if.then7, %if.end
//   tail call void @free(i8* nonnull %call) #24
//   tail call void @free(i8* %call1) #24
//   tail call void @initialize_write(i8* getelementptr inbounds ([16 x i8], [16 x i8]* @IV, i64 0, i64 0), i32 16)
//   call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %0) #24
//   ret void
// }


