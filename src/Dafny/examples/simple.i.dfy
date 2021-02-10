include "../llvm.i.dfy"
include "../control_flow.i.dfy"

module simple_functions {
    import opened LLVM_def
    import opened control_flow


function method{:opaque} lvm_code_Empty_Test():lvm_code
{   
    lvm_Block(lvm_CNil())
}       

lemma lvm_lemma_Empty_Test(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, src:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Empty_Test(), lvm_s0, lvm_sN,o)
  requires lvm_is_src_opr(src, lvm_s0)
  requires lvm_get_ok(lvm_s0)
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,o)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, lvm_s0)
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
{
  reveal_lvm_code_Empty_Test();
  reveal_eval_code();
  var lvm_old_s:lvm_state := lvm_s0;

  assert lvm_s0.ok;
  assert lvm_code_Empty_Test() == Block(CNil);
  assert lvm_b0.hd == lvm_code_Empty_Test();
  assert !lvm_b0.CNil?;
  assert lvm_code_Empty_Test().block.CNil?;
  assert lvm_b0.hd.Block?;
  assert lvm_get_block(lvm_b0.hd).CNil?;
  assert evalBlock(lvm_get_block(lvm_b0.hd),lvm_s0, lvm_s0,o);
  assert forall r :: r == lvm_s0 ==> eval_code(lvm_b0.hd,lvm_s0,r,o);
  assert evalCode_lax(Block(lvm_b0), lvm_s0, lvm_sN, o);

  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,o) ==> exists r' :: evalCode(lvm_b0.hd, lvm_s0, r',o) && evalBlock(lvm_b0.tl, r', lvm_sN,o);
  assert exists r' :: if evalCode(lvm_b0.hd, lvm_s0, r',o) then true else true;


  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block_lax(lvm_b0, lvm_s0, lvm_sN,o);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert evalCode_lax(lvm_Block(lvm_CNil()), lvm_s0, lvm_sM, o);

  lvm_sM := lvm_lemma_empty(lvm_s0, lvm_sM);
}

////
    // test(src){
    //     src = src + 4;
    // }
///
function method{:opaque} lvm_code_Add_single(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr):lvm_code
{
    reveal_IntFits();
    var val := D(Int(4,IntType(1,false)));
    assert val.d.Int?;
    var void := D(Void);
    lvm_Block(lvm_CCons(Ins(ADD(dst, size,src1,val)),lvm_CNil()))

    // lvm_Block(lvm_CCons(Ins(ADD(dst, size,src1,val)),lvm_CCons(Ins(RET(void)),lvm_CNil())))

}

lemma lvm_lemma_Add_single(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Add_single(dst, size,src1), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires lvm_code_Add_single(dst, size,src1).Ins?;
  requires ValidOperand(lvm_s0,dst)
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)
  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_s0,dst).Int?;
  ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
  reveal_lvm_code_Add_single();
  assert lvm_code_Add_single(dst, size,src1).Ins?;
  var addIns := lvm_code_Add_single(dst, size,src1).ins;
  assert ValidInstruction(lvm_s0,addIns);

  assert  ValidRegOperand(lvm_s0, dst);
  assert ValidState(lvm_s0);
  assert lvm_b0.hd.Ins?;
  var lvm_old_s:lvm_state := lvm_s0;
//   lvm_ins_lemma(Ins(InsAdd(dst, src)), lvm_s0);
  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block_lax(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  assert lvm_b0.tl == lvm_bM;
  assert lvm_bM.CNil?;
//   assert  OperandContents(lvm_sM, dst).Int?;

  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  assert OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4;

  reveal_evalCodeOpaque();
}


///
function method lvm_code_Add_Multiple(lvm_s0:lvm_state,dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr): (out:lvm_code)
    ensures out.Block?;
    ensures out.block.lvm_CCons?;
    ensures out.block.hd.Ins?;
    // ensures out.hd.Ins?;
    // ensures ValidInstruction(lvm_s0,out.block.hd.ins);
{
    reveal_IntFits();
    var val := D(Int(4,IntType(1,false)));
    assert val.d.Int?;
    var void := D(Void);

    var val2 := D(Int(5,IntType(1,false)));
    assert val.d.Int?;

    lvm_Block(lvm_CCons(Ins(ADD(dst,size,src1,val)),
              lvm_CCons(Ins(ADD(dst,size,src1,val2)),lvm_CNil())))

}

lemma lvm_lemma_Add_Multiple(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Add_Multiple(lvm_s0,dst, size,src1).block.hd, lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires ValidOperand(lvm_s0,dst);
  requires ValidInstruction(lvm_s0,lvm_code_Add_Multiple(lvm_s0,dst, size,src1).block.hd.ins);
//   requires lvm_code_Add_Multiple(lvm_s0,dst, size,src1).Ins?; //  ISSUE <<---

  requires ValidOperand(lvm_s0,dst)
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM) 
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_s0,dst).Int?;

  ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 9
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
//   reveal_lvm_code_Add_Multiple();
  assert lvm_code_Add_Multiple(lvm_s0,dst, size,src1).block.hd.Ins?;
  var addIns := lvm_code_Add_Multiple(lvm_s0,dst, size,src1).block.hd.ins;

  assert ValidInstruction(lvm_s0,addIns);
  assert  ValidRegOperand(lvm_s0, dst);
  assert ValidState(lvm_s0);
//   assert lvm_b0.block.hd.Ins?;
  var lvm_old_s:lvm_state := lvm_s0;
//   lvm_ins_lemma(Ins(InsAdd(dst, src)), lvm_s0);
  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  assert lvm_b0.tl == lvm_bM;
//   assert lvm_bM.CNil?;
//   assert  OperandContents(lvm_sM, dst).Int?;

  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  assert OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4;
//   assert ValidInstruction(lvm_s0,lvm_code_Add_Multiple(dst, size,src1,src2).ins) ==> lvm_sM.ok;
//   assert evalUpdate(lvm_s0, o, evalADD(size,OperandContents(lvm_s0,src1),val), lvm_sM);

  reveal_evalCodeOpaque();
}



// function method{:opaque} lvm_code_Add(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr): (out:lvm_code)
//     ensures out.Block?;
//     ensures out.block.lvm_CCons?;
//     ensures out.block.hd.Ins?;
// {
//     reveal_IntFits();
//     var val := D(Int(4,IntType(1,false)));
//     assert val.d.Int?;
//     var void := D(Void);
//     lvm_Block(lvm_CCons(Ins(ADD(dst, size,src1,val)),lvm_CCons(Ins(RET(void)),lvm_CNil())))

// }

// lemma lvm_lemma_Add(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
//             dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr,o:operand)
//   returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
//   requires lvm_require(lvm_b0, lvm_code_Add(dst, size,src1), lvm_s0, lvm_sN,dst)
//   requires lvm_is_dst_opr(dst, lvm_s0)
//   requires lvm_is_src_opr(src1, lvm_s0)
//   requires lvm_get_ok(lvm_s0)

//   requires ValidOperand(lvm_s0,src1);
//   requires OperandContents(lvm_s0,src1).Int?;
//   requires ValidInstruction(lvm_s0,lvm_code_Add(dst, size,src1).block.hd.ins);
// //   requires lvm_code_Add(dst, size,src1).Ins?;

// //   requires dst.GV?;
//   requires ValidOperand(lvm_s0,dst)
// //   
//   ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
//   ensures  lvm_get_ok(lvm_sM)
//   ensures ValidOperand(lvm_sM,dst)

//   ensures OperandContents(lvm_sM,dst).Int?;
//   ensures OperandContents(lvm_s0,dst).Int?;

//   ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4
//   ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
// {
//     // assert dst.g in lvm_s0.gvs;
//   reveal_lvm_code_Add();
//   assert lvm_code_Add(dst, size,src1).Block?;
//   var addIns := lvm_code_Add(dst, size,src1).block.hd.ins;
//   assert ValidInstruction(lvm_s0,addIns);
// //   assert o == dst;
//   assert  ValidRegOperand(lvm_s0, dst);
//   assert ValidOperand(lvm_s0,dst);
//   assert ValidState(lvm_s0);
//   assert lvm_b0.hd.Block?;
//   assert lvm_b0.hd == lvm_code_Add(dst, size,src1);
// //   assert lvm_b0.hd.Ins?;
//   var lvm_old_s:lvm_state := lvm_s0;
// //   lvm_ins_lemma(Ins(InsAdd(dst, src)), lvm_s0);
//   ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block_lax(lvm_b0, lvm_s0, lvm_sN,dst);
//   lvm_sM := lvm_ltmp1;
//   lvm_bM := lvm_ltmp2;
//   assert lvm_b0.tl == lvm_bM;
//   assert lvm_cM == lvm_b0.hd;
// //   assert lvm_bM.CNil?;
// //   assert  OperandContents(lvm_sM, dst).Int?;

//   assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
//   assert lvm_s0.ok;
//   assert lvm_cM.block.hd.Ins?;
//   assert exists r' :: evalCode(lvm_cM.block.hd,lvm_s0,r',dst);
//   assert evalBlock(lvm_cM.block,lvm_s0, lvm_sM,dst);

//   assert OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4;
// //   assert ValidInstruction(lvm_s0,lvm_code_Add(dst, size,src1,src2).ins) ==> lvm_sM.ok;
// //   assert evalUpdate(lvm_s0, o, evalADD(size,OperandContents(lvm_s0,src1),val), lvm_sM);

//   reveal_evalCodeOpaque();
// }


}