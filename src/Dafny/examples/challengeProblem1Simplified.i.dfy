include "../llvm.i.dfy"
include "../control_flow.i.dfy"

module challenge_problem_1_simplified {
    import opened LLVM_def
    import opened control_flow

// ; Function Attrs: norecurse nounwind readonly ssp uwtable
// define i32 @rx_message_routine(i8* nocapture readonly %0) local_unnamed_addr #1 {
//   %2 = getelementptr inbounds i8, i8* %0, i64 2
//   %3 = load i8, i8* %2, align 1, !tbaa !4
//   %4 = zext i8 %3 to i32
//   %5 = add nuw nsw i32 %4, 10
//   ret i32 %5
// }

function method{:opaque} lvm_simple_challenge1(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr):lvm_code
{
    //getelementptr
    reveal_IntFits();
    var void := D(Void);
    var ptrVar:lvm_operand_opr := D(Void);
    var index := D(Int(2,IntType(8,false)));

    lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(ptrVar,1,op1,index)),
              lvm_CCons(Ins(RET(void)),lvm_CNil())))
    // lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(dst,t,op1,op2)),
    //           lvm_CCons(Ins(RET(void)),lvm_CNil())))

}

lemma lvm_lemma_simple_challenge1(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires lvm_require(lvm_b0, lvm_simple_challenge1(dst,t,op1,op2), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,op2);
  requires OperandContents(lvm_s0,op1).Ptr?;

//   requires OperandContents(lvm_s0,src1).Int?;
//   requires lvm_code_Add(dst, size,src1).Ins?;

//   requires dst.GV?;
  requires ValidOperand(lvm_s0,dst)
//   
//   ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  // ensures  lvm_get_ok(lvm_sM)
//   ensures ValidOperand(lvm_sM,dst)

//   ensures OperandContents(lvm_sM,dst).Int?;
//   ensures OperandContents(lvm_s0,dst).Int?;

//   ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4
//   ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
  reveal_lvm_simple_challenge1();
  assert lvm_simple_challenge1(dst,t,op1,op2).Block?;
  var getelementins := lvm_simple_challenge1(dst,t,op1,op2).block.hd.ins;

  // Check getelementins validity
  assert getelementins.GETELEMENTPTR?;
  assert ValidState(lvm_s0); 
  assert MemValid(lvm_s0.m);
  assert ValidOperand(lvm_s0,getelementins.dst);
  assert ValidOperand(lvm_s0,getelementins.op1);
  assert ValidOperand(lvm_s0,getelementins.op2);
  assert OperandContents(lvm_s0,getelementins.op1).Ptr?;
  assert OperandContents(lvm_s0,getelementins.op2).Int?;
  assert !OperandContents(lvm_s0,getelementins.op2).itype.signed;
  assert IsValidPtr(lvm_s0.m,OperandContents(lvm_s0,getelementins.op1).bid,OperandContents(lvm_s0,getelementins.op1).offset);
  assert OperandContents(lvm_s0,getelementins.op1).offset 
       + OperandContents(lvm_s0,getelementins.op2).val 
         < |lvm_s0.m.mem[OperandContents(lvm_s0,getelementins.op1).bid]|;
  //
  assert ValidInstruction(lvm_s0,getelementins);

  var lvm_old_s:lvm_state := lvm_s0;
  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  reveal_evalCodeOpaque();
}





}