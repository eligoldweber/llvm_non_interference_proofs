include "../LLVM/llvm.i.dfy"
include "../LLVM/control_flow.i.dfy"
include "../LLVM/generalInstructions.i.dfy"
include "../LLVM/types.dfy"
include "../LLVM/memory.i.dfy"
include "../LLVM/Operations/otherOperations.i.dfy"


module musings {
    import opened LLVM_def
    import opened control_flow
    import opened general_instructions
    import opened types
    import opened memory
    import opened other_operations_i


// VULN
// ; Function Attrs: nofree nosync nounwind uwtable
// define dso_local void @choose_new_sa(i32 %current_index, i32 %iterations, i32* nocapture %avail_addrs) local_unnamed_addr #12 {
// entry:
//   %cmp17 = icmp sgt i32 %iterations, 255
//   br i1 %cmp17, label %if.then, label %if.end

// if.then:                                          ; preds = %if.end5, %entry
//   store i8 -2, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !20
//   br label %return

// if.end:                                           ; preds = %entry, %if.end5
//   %iterations.tr19 = phi i32 [ %inc6, %if.end5 ], [ %iterations, %entry ]
//   %current_index.tr18 = phi i32 [ %rem, %if.end5 ], [ %current_index, %entry ]
//   %idxprom = sext i32 %current_index.tr18 to i64
//   %arrayidx = getelementptr inbounds i32, i32* %avail_addrs, i64 %idxprom
//   %0 = load i32, i32* %arrayidx, align 4, !tbaa !13
//   %cmp1 = icmp eq i32 %0, 1
//   br i1 %cmp1, label %if.then2, label %if.end5

// if.then2:                                         ; preds = %if.end
//   %arrayidx.le = getelementptr inbounds i32, i32* %avail_addrs, i64 %idxprom
//   %conv = trunc i32 %current_index.tr18 to i8
//   store i8 %conv, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !20
//   store i32 0, i32* %arrayidx.le, align 4, !tbaa !13
//   br label %return

// if.end5:                                          ; preds = %if.end
//   %inc = add nsw i32 %current_index.tr18, 1
//   %inc6 = add i32 %iterations.tr19, 1
//   %rem = srem i32 %inc, 254
//   %exitcond = icmp eq i32 %inc6, 256
//   br i1 %exitcond, label %if.then, label %if.end

// return:                                           ; preds = %if.then2, %if.then
//   ret void
// }

/// -------------------------------------------
//  Simplified.... 
/// -------------------------------------------


// define dso_local void @choose_new_sa(i32 %current_index, i32 %iterations, i32* nocapture %avail_addrs) local_unnamed_addr #12 {
// entry:
//   %cmp17 = icmp sgt i32 %iterations, 255
//   br i1 %cmp17, label %if.then, label %return

// if.then:                                          ; preds = %if.end5, %entry
//   store i8 -2, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !20
//   br label %return

// return:                                           ; preds = %if.then2, %if.then
//   ret void
// }


function {:opaque} demo_challenge_prob_4(s:MemState,current_index:lvm_operand_opr,
                                         iterations:lvm_operand_opr,avail_addrs:lvm_operand_opr,cmp17:lvm_operand_opr):lvm_code
{
    reveal_IntFits();
    var remaining := D(Int(255,IntType(4,false)));
    var current_sa := D(Ptr(0,0,0));
 
    var returnLabel:code := lvm_Block(lvm_Codes(Ins(RET(D(Void))),lvm_CNil()));         // return: 
                                                                                        //   ret void
    
    var ifThenLabel:code := lvm_Block(lvm_Codes(Ins(STORE(D(Int(2,IntType(1,false))),current_sa,s)),  //   store i8 -2, i8* getelementptr inbounds (%struct.conf_t, %struct.conf_t* @conf, i64 0, i32 3), align 8, !tbaa !20
                                       lvm_Codes(Ins(UNCONDBR(returnLabel.block)),lvm_CNil())));      //   br label %return
                                                                                                             
      
    lvm_Block(lvm_Codes(Ins(ICMP(cmp17,sgt,4,iterations,remaining)),             // %cmp17 = icmp sgt i32 %iterations, 255
              lvm_Codes(Ins(BR(cmp17,                                            // br i1 %cmp17, label %if.then, label %return
                lvm_Codes(ifThenLabel,lvm_CNil()),
                lvm_Codes(returnLabel,lvm_CNil()))),  
              lvm_Codes(Ins(RET(D(Void))),lvm_CNil()))))                           

}

}

