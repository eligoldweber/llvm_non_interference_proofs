include "../llvm.i.dfy"
include "../control_flow.i.dfy"
include "generalInstructions.i.dfy"

module challenge_problem_1_simplified {
    import opened LLVM_def
    import opened control_flow
    import opened general_instructions

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

    lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(dst,1,op1,index)),
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
  requires OperandContents(lvm_s0,op1).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires ValidOperand(lvm_s0,dst)
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Ptr?;
  ensures  OperandContents(lvm_sM, dst) == evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(2,IntType(8,false)));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
  reveal_lvm_simple_challenge1();
  reveal_lvm_RET();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_lvm_code_GetElementPtr();
  reveal_eval_code();

  assert lvm_simple_challenge1(dst,t,op1,op2).Block?;
  var getelementins := lvm_simple_challenge1(dst,t,op1,op2).block.hd.ins;
  assert lvm_simple_challenge1(dst,t,op1,op2) == lvm_b0.hd;
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
  assert IsValidBid(lvm_s0.m,OperandContents(lvm_s0,getelementins.op1).bid);
  // assert IsValidPtr(lvm_s0.m,OperandContents(lvm_s0,getelementins.op1).bid,OperandContents(lvm_s0,getelementins.op1).offset);
  // assert OperandContents(lvm_s0,getelementins.op1).offset 
      //  + (OperandContents(lvm_s0,getelementins.op2).val * getelementins.t)
        //  < |lvm_s0.m.mem[OperandContents(lvm_s0,getelementins.op1).bid]|;
  //
  assert ValidInstruction(lvm_s0,getelementins);

  var lvm_old_s:lvm_state := lvm_s0;
  var two :=D(Void);
      // var lvm_old_s:lvm_state := lvm_s0;
  // assert evalCode(Ins(getelementins), lvm_s0, lvm_sN,dst);
  assert lvm_s0.ok;
  assert dst == getelementins.dst;
  var getPtr := D(evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)));
  // assert getPtr.Ptr?;
  // assert IsValidPtr(lvm_s0.m,getPtr.bid,getPtr.offset);
  assert ValidData(lvm_sN,evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)));
  assert getPtr.D?;
  assert getPtr.d == evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2));
  // assert  lvm_sN == lvm_s0;
  // assert evalUpdate(lvm_s0, getPtr, evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)),lvm_sN);

  // assert evalIns(getelementins,lvm_s0, lvm_sN,dst);
  assert lvm_s0.ok;
  // assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);
  // assert evalCode(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);
    assert !lvm_b0.CNil?;
  // assert exists r' :: evalCode(lvm_b0.hd, lvm_s0, r',dst);
  // assert lvm_b0.hd.Ins?;
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,dst);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_b1.lvm_CCons?;
  assert lvm_b1.hd.Ins?;
  assert lvm_b1.hd.ins.GETELEMENTPTR?;
  // assert lvm_bM.lvm_CCons?;
  assert lvm_b1.tl.lvm_CCons?;
  assert lvm_b1.tl.hd.Ins?;
  assert lvm_b1.tl.hd.ins.RET?;
  assert lvm_b1.hd == Ins(GETELEMENTPTR(dst,1,op1,D(Int(2,IntType(8,false)))));

  // ghost var lvm_ltmp3, lvm_b2, lvm_s2 := lvm_lemma_block(lvm_b1, lvm_s0, lvm_sM, dst);
  ghost var lvm_b2, lvm_s2 := lvm_lemma_GetElementPtr(lvm_b1, lvm_s0, lvm_sM, dst, s,1,op1,D(Int(2,IntType(8,false))));
  assert OperandContents(lvm_s2, dst) 
        == evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(2,IntType(8,false)));
  // assert lvm_sM.ok;
  assert lvm_b2.hd.Ins?;
  assert lvm_b2.hd.ins.RET?;
  assert lvm_b2.hd.ins == RET(D(Void));
  
  ghost var lvm_b3, lvm_s3 := lvm_lemma_Ret(lvm_b2, lvm_s2, lvm_sM, dst, D(Void));

  lvm_sM := lvm_lemma_empty(lvm_s3,lvm_sM);

  assert ValidState(lvm_sM);
  // lvm_sM := lvm_lemma_empty(lvm_s2,lvm_sM);

  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  reveal_evalCodeOpaque();
}


// ----*****-----


function method{:opaque} lvm_simple_challenge1_cont(dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr):lvm_code
requires op1.D?;
requires op1.d.Ptr?;
requires IsValidBid(s,op1.d.bid) ==> op1.d.offset + ((Int(2,IntType(8,false))).val * 1) < |s.mem[op1.d.bid]|;
// requires exists d:Data :: Load(lvm_s2.m,lvm_sM.m,OperandContents(lvm_s2,dst).bid,OperandContents(lvm_s2,dst).offset,d);

{
    //getelementptr
    reveal_IntFits();
    var void := D(Void);
    var ptrVar:lvm_operand_opr := D(Void);
    var index := D(Int(2,IntType(8,false)));

    lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(dst,1,op1,index)),
              lvm_CCons(Ins(LOAD(dst,s,1,dst)),
              lvm_CCons(Ins(RET(void)),lvm_CNil()))))
    // lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(dst,t,op1,op2)),
    //           lvm_CCons(Ins(RET(void)),lvm_CNil())))

}

lemma lvm_lemma_simple_challenge1_cont(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires op1.D?;
requires op1.d.Ptr?;
requires IsValidBid(lvm_s0.m,op1.d.bid) ==> op1.d.offset + ((Int(2,IntType(8,false))).val * 1) < |lvm_s0.m.mem[op1.d.bid]|;

  requires lvm_require(lvm_b0, lvm_simple_challenge1_cont(dst,lvm_s0.m,t,op1,op2), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,op2);
  requires OperandContents(lvm_s0,op1).Ptr?;
  requires OperandContents(lvm_s0,op1).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires ValidOperand(lvm_s0,dst);
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures !OperandContents(lvm_sM,dst).Ptr?;
  ensures  OperandContents(lvm_sM, dst) == evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(2,IntType(8,false)));
  // ensures  OperandContents(lvm_sM, dst) == 
  // evalLOAD(lvm_sM.m,lvm_sN.m,1,evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(2,IntType(8,false))));

  // ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
  reveal_lvm_simple_challenge1_cont();
  reveal_lvm_RET();
  reveal_lvm_LOAD();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_lvm_code_GetElementPtr();
  reveal_eval_code();

  assert lvm_simple_challenge1_cont(dst,lvm_s0.m,t,op1,op2).Block?;
  var getelementins := lvm_simple_challenge1_cont(dst,lvm_s0.m,t,op1,op2).block.hd.ins;
  assert lvm_simple_challenge1_cont(dst,lvm_s0.m,t,op1,op2) == lvm_b0.hd;
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
  assert IsValidBid(lvm_s0.m,OperandContents(lvm_s0,getelementins.op1).bid);
  // assert IsValidPtr(lvm_s0.m,OperandContents(lvm_s0,getelementins.op1).bid,OperandContents(lvm_s0,getelementins.op1).offset);
  // assert OperandContents(lvm_s0,getelementins.op1).offset 
      //  + (OperandContents(lvm_s0,getelementins.op2).val * getelementins.t)
        //  < |lvm_s0.m.mem[OperandContents(lvm_s0,getelementins.op1).bid]|;
  //
  assert ValidInstruction(lvm_s0,getelementins);

  var lvm_old_s:lvm_state := lvm_s0;
  var two :=D(Void);
      // var lvm_old_s:lvm_state := lvm_s0;
  // assert evalCode(Ins(getelementins), lvm_s0, lvm_sN,dst);
  assert lvm_s0.ok;
  assert dst == getelementins.dst;
  var getPtr := D(evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)));
  // assert getPtr.Ptr?;
  // assert IsValidPtr(lvm_s0.m,getPtr.bid,getPtr.offset);
  assert ValidData(lvm_sN,evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)));
  assert getPtr.D?;
  assert getPtr.d == evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2));
  // assert  lvm_sN == lvm_s0;
  // assert evalUpdate(lvm_s0, getPtr, evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,getelementins.op1),OperandContents(lvm_s0,getelementins.op2)),lvm_sN);

  // assert evalIns(getelementins,lvm_s0, lvm_sN,dst);
  assert lvm_s0.ok;
  // assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);
  // assert evalCode(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);
    assert !lvm_b0.CNil?;
  // assert exists r' :: evalCode(lvm_b0.hd, lvm_s0, r',dst);
  // assert lvm_b0.hd.Ins?;

 assert lvm_b0.hd.Block?;
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,dst);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_b1.lvm_CCons?;
  assert lvm_b1.hd.Ins?;
  assert lvm_b1.hd.ins.GETELEMENTPTR?;
  // assert lvm_bM.lvm_CCons?;
  assert lvm_b1.tl.lvm_CCons?;
  assert lvm_b1.tl.hd.Ins?;
  assert lvm_b1.tl.hd.ins.LOAD?;
  assert lvm_b1.hd == Ins(GETELEMENTPTR(dst,1,op1,D(Int(2,IntType(8,false)))));
  assert lvm_sM == lvm_s0;
  // ghost var lvm_ltmp3, lvm_b2, lvm_s2 := lvm_lemma_block(lvm_b1, lvm_s0, lvm_sM, dst);
  ghost var lvm_b2, lvm_s2 := lvm_lemma_GetElementPtr(lvm_b1, lvm_s0, lvm_sM, dst, s,1,op1,D(Int(2,IntType(8,false))));
  assert OperandContents(lvm_s2, dst) 
        == evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(2,IntType(8,false)));
  // assert lvm_sM.ok;
  assert lvm_b2.hd.Ins?;
  assert lvm_b2.hd.ins.LOAD?;
  assert lvm_b2.hd.ins == LOAD(dst,lvm_s0.m,1,dst);
  assert lvm_s0.m == lvm_s2.m;
  assert IsValidBid(lvm_s2.m,OperandContents(lvm_s2,dst).bid);
  assert IsValidPtr(lvm_s2.m,OperandContents(lvm_s2,dst).bid,OperandContents(lvm_s2,op1).offset);
  assert lvm_s2.m == lvm_sM.m;
  // assert exists d:Data :: Load(lvm_s2.m,lvm_sM.m,OperandContents(lvm_s2,dst).bid,OperandContents(lvm_s2,dst).offset,d);

  ghost var lvm_b3, lvm_s3 := lvm_lemma_Load(lvm_b2, lvm_s2, lvm_sM, dst,1,dst);
  assert !OperandContents(lvm_s3,dst).Ptr?;


  ghost var lvm_b4, lvm_s4 := lvm_lemma_Ret(lvm_b3, lvm_s3, lvm_sM, dst, D(Void));

  lvm_sM := lvm_lemma_empty(lvm_s4,lvm_sM);

  assert ValidState(lvm_sM);
  // lvm_sM := lvm_lemma_empty(lvm_s2,lvm_sM);

  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  reveal_evalCodeOpaque();
}


}