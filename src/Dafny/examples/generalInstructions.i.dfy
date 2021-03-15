include "../llvm.i.dfy"
include "../control_flow.i.dfy"

module general_instructions {
    import opened LLVM_def
    import opened control_flow


function method{:opaque}lvm_code_Add(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr):lvm_code

{
   Ins(ADD(dst, size,src1,src2))
}
lemma lvm_lemma_Add(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires lvm_require(lvm_b0, lvm_code_Add(dst, size,src1,src2), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires ValidOperand(lvm_s0,src2);
  requires OperandContents(lvm_s0,src2).Int?;
  requires ValidOperand(lvm_s0,dst);
  requires OperandContents(lvm_s0,dst).Int?;

  requires ValidOperand(lvm_s0,dst);
  requires typesMatch(OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2))
  requires OperandContents(lvm_s0,src2).Int?;
  requires lvm_code_Add(dst, size,src1,src2).Ins?;
  requires ValidOperand(lvm_s0,dst)
// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  ValidOperand(lvm_sM,src1)
  ensures OperandContents(lvm_sM,src1).Int?;
  ensures  ValidOperand(lvm_sM,src2)
  ensures OperandContents(lvm_sM,src2).Int?;
  ensures typesMatch(OperandContents(lvm_sM,src1),OperandContents(lvm_sM,src2))

  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_all(lvm_sM, lvm_s0)))
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, lvm_s0, s2,o) ==> s2.ok
  ensures OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)).val;
  ensures ToTwosComp(OperandContents(lvm_sM, dst)).val == 
          (OperandContents(lvm_s0, src1).val + OperandContents(lvm_s0, src2).val) % Pow256(OperandContents(lvm_s0, src1).itype.size)

{
    reveal_lvm_code_Add();
    reveal_evalCodeOpaque();
    reveal_eval_code();
    assert lvm_code_Add(dst, size,src1,src2).Ins?;
    var addIns := lvm_code_Add(dst, size,src1,src2).ins;
    assert ValidInstruction(lvm_s0,addIns);

    assert  ValidRegOperand(lvm_s0, dst);
    assert ValidState(lvm_s0);
    var lvm_old_s:lvm_state := lvm_s0;
    assert evalCode_lax(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);
    assert lvm_s0.ok;
    assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN,dst);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert lvm_b0.tl == lvm_bM;
    assert ValidState(lvm_s0);
    assert lvm_s0.ok;
    assert ValidState(lvm_sM);
    assert ValidOperand(lvm_sM,dst);
    assert evalIns(lvm_code_Add(dst, size,src1,src2).ins,lvm_s0,lvm_sM,dst);
    assert evalUpdate(lvm_s0, dst, evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)),lvm_sM);
    assert ValidData(lvm_sM,evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)));
    assert OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)).val;
    reveal_evalCodeOpaque();
}

function method{:opaque} lvm_code_GetElementPtr(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr):lvm_code
{
    //getelementptr
    reveal_IntFits();
    Ins(GETELEMENTPTR(dst,t,op1,op2))

}

lemma lvm_lemma_GetElementPtr(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires lvm_require(lvm_b0, lvm_code_GetElementPtr(dst,t,op1,op2), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,op2);
  requires OperandContents(lvm_s0,op1).Ptr?;
  requires OperandContents(lvm_s0,op2).Int?;
  requires !OperandContents(lvm_s0,op2).itype.signed;

  requires OperandContents(lvm_s0,op1).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires ValidOperand(lvm_s0,dst)
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Ptr?;
  ensures  OperandContents(lvm_sM, dst) == evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,op1),OperandContents(lvm_s0,op2));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
{
  reveal_lvm_code_GetElementPtr();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_eval_code();

  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,dst);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
//   var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_sM.ok;
      assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  reveal_evalCodeOpaque();
}


function method{:opaque} lvm_RET(op1:lvm_operand_opr):lvm_code
{
    //getelementptr
    reveal_IntFits();
    Ins(RET(op1))

}

lemma lvm_lemma_Ret(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state,dst:lvm_operand_opr, op1:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires lvm_require(lvm_b0, lvm_RET(op1), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);

//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)

  ensures  lvm_state_eq(lvm_sM,  lvm_s0)
{
  reveal_lvm_RET();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_eval_code();

  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,dst);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
//   var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_sM.ok;
  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  reveal_evalCodeOpaque();
}

function method{:opaque} lvm_LOAD(dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr):lvm_code
{
    //getelementptr
    reveal_IntFits();
    Ins(LOAD(dst,s,t,op1))

}



lemma lvm_lemma_Load(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state,dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
//   requires dst.LV?;
  requires lvm_require(lvm_b0, lvm_LOAD(dst,lvm_s0.m,t,op1), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,dst);
  requires OperandContents(lvm_s0,op1).Ptr?;
  requires MemValid(lvm_s0.m);
  requires IsValidPtr(lvm_s0.m,OperandContents(lvm_s0,op1).bid,OperandContents(lvm_s0,op1).offset);
  requires lvm_s0 == lvm_sN; // this is the issue
  requires exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,op1).bid,OperandContents(lvm_s0,op1).offset,d);

//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)

//   ensures  lvm_state_eq(lvm_sM,  lvm_s0)
{
  reveal_lvm_LOAD();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_eval_code();
  reveal_ValidRegState();
  reveal_ValidData();

  assert evalBlock(lvm_b0, lvm_s0, lvm_sN,dst);
  assert lvm_s0.ok;
  assert ValidInstruction(lvm_s0,lvm_b0.hd.ins);

  assert IsValidPtr(lvm_s0.m, OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset);
  assert exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,d);
  var d := evalLOAD(lvm_s0.m,lvm_sN.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src));
  assert lvm_s0.m == lvm_sN.m;
//   assert exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,d); 

  assert lvm_s0.ok == lvm_sN.ok;
  assert d == evalLOAD(lvm_s0.m,lvm_sN.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src));
  assert D(d).D?;
  assert evalUpdate(lvm_s0, D(d), evalLOAD(lvm_s0.m,lvm_sN.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src)),lvm_sN);

  assert exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,d);
//   assert dst.LV?;
//   assert 
//   assert evalLoad(lvm_s0,dst,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,lvm_sN);
  
//   assert evalIns(lvm_b0.hd.ins,lvm_s0,lvm_sN,dst);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;

  assert lvm_sM.ok;
  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
}

}
