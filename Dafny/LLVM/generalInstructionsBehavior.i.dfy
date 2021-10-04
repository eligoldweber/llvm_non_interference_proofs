include "./llvm.i.dfy"
include "./control_flow.i.dfy"
include "./types.dfy"
include "./memory.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"

module general_instructions_behaviors {
    import opened LLVM_def
    import opened control_flow
    import opened types
    import opened memory
    import opened binary_operations_i
    import opened conversion_operations_i
    import opened bitwise_binary_operations_i
    import opened other_operations_i

function method lvm_code_Add(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr):lvm_code

{
   Ins(ADD(dst, size,src1,src2))
}
lemma lvm_lemma_Add_behavior(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_Add(dst, size,src1,src2), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(src1, bls(b))
  requires lvm_get_ok(bls(b))

  requires ValidOperand(bls(b),src1);
  requires OperandContents(bls(b),src1).Int?;
  requires ValidOperand(bls(b),src2);
  requires OperandContents(bls(b),src2).Int?;
  requires ValidOperand(bls(b),dst);
  // requires OperandContents(bls(b),dst).Int?;

  requires typesMatch(OperandContents(bls(b),src1),OperandContents(bls(b),src2))
  requires size == OperandContents(bls(b),src1).itype.size
  requires lvm_code_Add(dst, size,src1,src2).Ins?;
// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  ValidOperand(lvm_sM,src1)
  ensures OperandContents(lvm_sM,src1).Int?;
  ensures  ValidOperand(lvm_sM,src2)
  ensures OperandContents(lvm_sM,src2).Int?;
  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_sM,dst).itype.size == size;
  ensures !OperandContents(lvm_sM,dst).itype.signed


  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_all(lvm_sM, bls(b))))
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures  forall s2 :: evalCode(lvm_b0.hd, bls(b), s2) ==> s2.ok
    // ensures typesMatch(OperandContents(lvm_sM,src1),OperandContents(lvm_sM,src2))

  // ensures OperandContents(lvm_sM, dst).val == evalADD(OperandContents(bls(b),dst).itype.size,OperandContents(bls(b),src1),OperandContents(bls(b),src2)).val;
  ensures ToTwosComp(OperandContents(lvm_sM, dst)).val == 
          (OperandContents(bls(b), src1).val + OperandContents(bls(b), src2).val) % Pow256(OperandContents(bls(b), src1).itype.size)
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');
{
    var lvm_s0 := bls(b);
    assert lvm_code_Add(dst, size,src1,src2).Ins?;
    var addIns := lvm_code_Add(dst, size,src1,src2).ins;
    assert ValidInstruction(lvm_s0,addIns);

    assert  ValidRegOperand(lvm_s0, dst);
    assert ValidState(lvm_s0);
    var lvm_old_s:lvm_state := lvm_s0;
    assert evalCode_lax(lvm_Block(lvm_b0), lvm_s0, lvm_sN);
    assert lvm_s0.ok;
    assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN);
    assert evalBlock(lvm_Block(lvm_b0).block, lvm_s0, lvm_sN);
    assert exists r' :: (evalCode(lvm_b0.hd, lvm_s0, r'));

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert lvm_b0.tl == lvm_bM;
    assert ValidState(lvm_s0);
    assert lvm_s0.ok;
    assert ValidState(lvm_sM);
    assert ValidOperand(lvm_sM,dst);
    assert evalIns(lvm_code_Add(dst, size,src1,src2).ins,lvm_s0,lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_Add(dst, size,src1,src2).ins));
    assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
    assert StateNext(lvm_s0,lvm_sM);
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_Add(dst, size,src1,src2),[lvm_s0,lvm_sM]);
    // var evalA := evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2));
    // assert evalUpdate(lvm_s0, dst, evalA,lvm_sM);
    assert (forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d));
    // assert ValidData(lvm_sM,evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)));
    assert OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,src1).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)).val;
}

function method lvm_code_GetElementPtr(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr):lvm_code
{
    //getelementptr
    
    Ins(GETELEMENTPTR(dst,t,op1,op2))

}

lemma lvm_lemma_GetElementPtr(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
    requires ValidBehaviorNonTrivial(b);

  requires lvm_require(lvm_b0, lvm_code_GetElementPtr(dst,t,op1,op2), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(op1, bls(b))
  requires lvm_get_ok(bls(b))

  requires ValidOperand(bls(b),op1);
  requires ValidOperand(bls(b),op2);
  requires OperandContents(bls(b),op1).Ptr?;
  requires OperandContents(bls(b),op2).Int?;
  requires !OperandContents(bls(b),op2).itype.signed;
  requires |bls(b).m.mem[OperandContents(bls(b),op1).bid]| == t

  requires OperandContents(bls(b),op1).bid in bls(b).m.mem; //needed for IsValidBid for valid input
  requires ValidOperand(bls(b),dst)
//   
ensures bls(b).m == lvm_sM.m;
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Ptr?;
  ensures  OperandContents(lvm_sM, dst) == evalGETELEMENTPTR(bls(b).m,t,OperandContents(bls(b),op1),OperandContents(bls(b),op2));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');

{ 
  var lvm_s0 := bls(b);
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
//   var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_sM.ok;
  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
  assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_GetElementPtr(dst,t,op1,op2).ins));
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
  b' := b + [lvm_sM];
  assert ValidBehavior(b');
  assert BehaviorEvalsCode(lvm_code_GetElementPtr(dst,t,op1,op2),[lvm_s0,lvm_sM]);

}


function method lvm_code_Ret(op1:lvm_operand_opr):lvm_code
{
    //getelementptr
    
    Ins(RET(op1))

}

lemma lvm_ret_behavior(b:behavior,lvm_b0:lvm_codes,lvm_sN:lvm_state,op1:lvm_operand_opr) 
  returns (b':behavior, lvm_bM:lvm_codes, lvm_sM:lvm_state)
  // requires code.Ins? && code.ins.RET?;
  // requires ValidInstruction(lvm_s0,code.ins);
  requires ValidBehaviorNonTrivial(b);
  requires ValidState(bls(b));
  requires lvm_require(lvm_b0, lvm_code_Ret(op1), bls(b), lvm_sN);
  requires ValidOperand(bls(b),op1);
  // requires lvm_s0 == bls(b);
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  OperandContents(bls(b),op1).Void? ==> bls(b) == lvm_sM
  ensures  lvm_state_eq(lvm_sM,  bls(b))
  ensures lvm_bM == lvm_b0.tl;
  // ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM);
  ensures ValidBehavior(b');

{
  // assert forall
  // assert exists s' :: evalIns(code.ins,lvm_s0,s');
  // var s' :| evalCode(code,lvm_s0,s');
  var lvm_s0 := bls(b);
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;

  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode(lvm_cM, lvm_s0, lvm_sM);
  assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_Ret(op1).ins));
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
  assert StateNext(lvm_s0,lvm_sM);

  b' := b + [lvm_sM];
  assert ValidBehavior(b');
  assert BehaviorEvalsCode(lvm_code_Ret(op1),[lvm_s0,lvm_sM]);
}

lemma lvm_lemma_Ret(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state,dst:lvm_operand_opr, op1:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires lvm_require(lvm_b0, lvm_code_Ret(op1), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);

//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  OperandContents(lvm_s0,op1).Void? ==> lvm_s0 == lvm_sM
  ensures  lvm_state_eq(lvm_sM,  lvm_s0)
  ensures lvm_bM == lvm_b0.tl;
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM);

{
  
  

  assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;

  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode(lvm_cM, lvm_s0, lvm_sM);
  assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_Ret(op1).ins));
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());


}


function method lvm_LOAD(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr):lvm_code
{
    
    Ins(LOAD(dst,t,op1))
}


lemma lvm_lemma_Load(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state,dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_LOAD(dst,t,op1), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(op1, bls(b))
  requires lvm_get_ok(bls(b))

  requires ValidOperand(bls(b),op1);
  requires ValidOperand(bls(b),dst);
  requires OperandContents(bls(b),op1).Ptr?;
  requires MemValid(bls(b).m);
  requires IsValidPtr(bls(b).m,OperandContents(bls(b),op1).bid,OperandContents(bls(b),op1).offset,t);
  // requires bls(b).m == lvm_sN.m;
//   
  ensures  lvm_sM.ok ==> lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_sM.ok ==> lvm_get_ok(lvm_sM)
  ensures  lvm_sM.ok ==> ValidOperand(lvm_sM,dst);
  ensures  lvm_sM.ok ==> !OperandContents(lvm_sM,dst).Ptr?;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int?;

  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Bytes? ==> validBitWidth(|OperandContents(lvm_sM,dst).bytes|)
  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? || OperandContents(lvm_sM,dst).Bytes? || OperandContents(lvm_sM,dst).Void?;
  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? ==> OperandContents(lvm_sM,dst).itype.size == t;
  ensures bls(b).m == lvm_sM.m;
  ensures lvm_sM.ok ==> forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures lvm_sM.ok ==> StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');

{
  
  
  
  var lvm_s0 := bls(b);
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN);
  assert lvm_s0.ok;
  assert ValidInstruction(lvm_s0,lvm_b0.hd.ins);

  assert IsValidPtr(lvm_s0.m, OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,t);
//   assert exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,d);
  // assert lvm_s0.m == lvm_sN.m;
//   assert exists d:Data :: Load(lvm_s0.m,lvm_sN.m,OperandContents(lvm_s0,lvm_b0.hd.ins.src).bid,OperandContents(lvm_s0,lvm_b0.hd.ins.src).offset,d); 
//   assert lvm_s0.ok == lvm_sN.ok;


  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
 
  var d := evalLOAD(lvm_s0.m,lvm_sM.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src));
  assert d == evalLOAD(lvm_s0.m,lvm_sM.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src));
  assert D(d).D?;

  // assert evalLOAD(lvm_s0.m,lvm_sM.m,lvm_b0.hd.ins.t,OperandContents(lvm_s0,lvm_b0.hd.ins.src)).Void? ==> !lvm_sM.ok;
  assert  d.Void? ==> !lvm_sM.ok;
  assert  !d.Void? ==> lvm_sM.ok;
  assert  evalCode(lvm_b0.hd, lvm_s0, lvm_sM);
  assert lvm_b0.hd == lvm_LOAD(dst,t,op1);
  assert lvm_b0.hd.ins.LOAD?;
  assert evalIns(lvm_b0.hd.ins,lvm_s0,lvm_sM);

  assert lvm_b0.tl == lvm_bM;
  assert lvm_sM.ok ==> !OperandContents(lvm_sM,dst).Ptr?;
  assert lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? || OperandContents(lvm_sM,dst).Void?;
  assert lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? ==> OperandContents(lvm_sM,dst).itype.size == t;
  
  assert lvm_sM.ok ==> ValidState(lvm_sM);
  assert lvm_sM.ok ==> evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
  assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_LOAD(dst,t,op1).ins));
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
  b' := b + [lvm_sM];
  assert ValidBehavior(b');
  assert BehaviorEvalsCode(lvm_LOAD(dst,t,op1),[lvm_s0,lvm_sM]);

}



function method lvm_code_ZEXT(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(ZEXT(dst,t,op1,dstSize))
}

lemma lvm_lemma_Zext(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)

   requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_ZEXT(dst,t,op1,dstSize), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(op1, bls(b))
  requires lvm_get_ok(bls(b))

  requires ValidOperand(bls(b),op1);
  requires ValidOperand(bls(b),dst);
  requires OperandContents(bls(b),op1).Int?;
  requires OperandContents(bls(b),op1).itype.size < dstSize;
//   requires !OperandContents(bls(b),dst).itype.signed;

// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures !OperandContents(lvm_sM,dst).itype.signed;
  ensures  OperandContents(lvm_sM,dst).itype.size == dstSize;
  ensures OperandContents(lvm_sM, dst).val == evalZEXT(OperandContents(bls(b),op1),dstSize).val;
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures bls(b).m == lvm_sM.m;
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');

{
    var lvm_s0 := bls(b);   
    assert lvm_code_ZEXT(dst,t,op1,dstSize).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_ZEXT(dst,t,op1,dstSize).ins);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    // assert lvm_b0.tl == lvm_bM;
    assert ValidState(lvm_s0);
    // assert lvm_s0.ok;
    assert ValidState(lvm_sM);
    
  assert lvm_sM.ok;
  assert lvm_b0.tl == lvm_bM;

  assert ValidState(lvm_sM);
  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
  assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_ZEXT(dst,t,op1,dstSize).ins));
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
  b' := b + [lvm_sM];
  assert ValidBehavior(b');
  assert BehaviorEvalsCode(lvm_code_ZEXT(dst,t,op1,dstSize),[lvm_s0,lvm_sM]);
}


function method lvm_code_SEXT(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(SEXT(dst,t,op1,dstSize))
}

lemma lvm_lemma_Sext(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires ValidBehaviorNonTrivial(b);

  requires lvm_require(lvm_b0, lvm_code_SEXT(dst,t,op1,dstSize), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(op1, bls(b))
  requires lvm_get_ok(bls(b))

//   requires ValidInstruction(bls(b), lvm_code_ZEXT(dst,t,op1,dstSize).ins);
  requires ValidOperand(bls(b),op1);
  requires ValidOperand(bls(b),dst);
  requires OperandContents(bls(b),op1).Int?;
  requires OperandContents(bls(b),op1).itype.size < dstSize;
  requires OperandContents(bls(b),dst).Int?;
//   requires !OperandContents(bls(b),dst).itype.signed;

// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_sM,dst).itype.signed;
  ensures  OperandContents(lvm_sM,dst).itype.size == dstSize;
  ensures OperandContents(lvm_sM, dst).val == evalSEXT(OperandContents(bls(b),op1),dstSize).val;
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
    ensures ValidBehavior(b');


{
    var lvm_s0 := bls(b);
    assert lvm_code_SEXT(dst,t,op1,dstSize).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_SEXT(dst,t,op1,dstSize).ins);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    // assert lvm_b0.tl == lvm_bM;
    assert ValidState(lvm_s0);
    // assert lvm_s0.ok;
    assert ValidState(lvm_sM);
   
    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_SEXT(dst,t,op1,dstSize).ins));
    assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_SEXT(dst,t,op1,dstSize),[lvm_s0,lvm_sM]);

}

function method lvm_code_SHL(dst:lvm_operand_opr,src:lvm_operand_opr,shiftAmt:lvm_operand_opr):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(SHL(dst,src,shiftAmt))
}

lemma lvm_lemma_Shl(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, src:lvm_operand_opr,shiftAmt:lvm_operand_opr)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires ValidBehaviorNonTrivial(b);

  requires lvm_require(lvm_b0, lvm_code_SHL(dst,src,shiftAmt), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(src, bls(b))
  requires lvm_get_ok(bls(b))

// is valid ins
  requires ValidOperand(bls(b),src);
  requires ValidOperand(bls(b),dst);
  requires ValidOperand(bls(b),shiftAmt);

  requires OperandContents(bls(b),src).Int?;
  // requires OperandContents(bls(b),dst).Int?;
  requires OperandContents(bls(b),shiftAmt).Int?;
  requires OperandContents(bls(b),src).itype.size*8 > OperandContents(bls(b),shiftAmt).val
  requires OperandContents(bls(b),shiftAmt).val > 0
// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  ValidOperand(lvm_sM,src)

  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  OperandContents(lvm_sM,src).Int?;

  ensures OperandContents(lvm_sM,dst).itype.size == OperandContents(lvm_sM,src).itype.size 
  ensures OperandContents(lvm_sM,dst).itype.signed == OperandContents(lvm_sM,src).itype.signed
  ensures OperandContents(lvm_sM, dst) == evalSHL(OperandContents(bls(b),src),OperandContents(bls(b),shiftAmt));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures bls(b).m == lvm_sM.m;
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
    ensures ValidBehavior(b');


{
    var lvm_s0 := bls(b);
    assert lvm_code_SHL(dst,src,shiftAmt).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_SHL(dst,src,shiftAmt).ins);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert ValidState(lvm_s0);
    assert ValidState(lvm_sM);

    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_SHL(dst,src,shiftAmt).ins));
    assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_SHL(dst,src,shiftAmt),[lvm_s0,lvm_sM]);

}

function method lvm_code_ICMP(dst:lvm_operand_opr,cond:lvm_cond,size:nat,op1:lvm_operand_opr,op2:lvm_operand_opr):(out:lvm_code)
{
    
    Ins(ICMP(dst,cond,size,op1,op2))
}

lemma lvm_lemma_Icmp(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state,
                    dst:lvm_operand_opr,cond:lvm_cond,size:nat,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires ValidBehaviorNonTrivial(b);

  requires lvm_require(lvm_b0, lvm_code_ICMP(dst,cond,size,op1,op2), bls(b), lvm_sN)
  requires lvm_is_dst_opr(dst, bls(b))
  requires lvm_is_src_opr(op1, bls(b))
  requires lvm_get_ok(bls(b))

  requires lvm_code_ICMP(dst,cond,size,op1,op2).Ins?;
  // requires ValidInstruction(bls(b),lvm_code_ICMP(dst,cond,size,op1,op2).ins);
  requires ValidOperand(bls(b),dst) && ValidOperand(bls(b),op1) && ValidOperand(bls(b),op2);
  requires OperandContents(bls(b),op1).Int?;
  requires OperandContents(bls(b),op2).Int?;
  requires typesMatch(OperandContents(bls(b),op1),OperandContents(bls(b),op2));
  requires size == OperandContents(bls(b),op1).itype.size

  ensures lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)
  ensures ValidOperand(lvm_sM,op1)
  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_sM,op1).Int?;
  ensures OperandContents(bls(b),op1).itype == OperandContents(lvm_sM,op1).itype;
  ensures !OperandContents(lvm_sM,dst).itype.signed
  ensures OperandContents(lvm_sM,dst).itype.size == 1 

  ensures OperandContents(lvm_sM, dst) == evalICMP(cond,size,OperandContents(bls(b),op1),OperandContents(bls(b),op2));
  ensures lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, bls(b))))
  ensures forall d :: ValidOperand(bls(b),d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(bls(b),d) == OperandContents(lvm_sM,d)
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');

{
    
    var lvm_s0 := bls(b);

    assert lvm_code_ICMP(dst,cond,size,op1,op2).Ins?;
    assert ValidInstruction(lvm_s0,lvm_code_ICMP(dst,cond,size,op1,op2).ins);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert ValidState(lvm_s0);
    assert ValidState(lvm_sM);
  
    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_ICMP(dst,cond,size,op1,op2).ins));
    assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_ICMP(dst,cond,size,op1,op2),[lvm_s0,lvm_sM]);

}

function method lvm_code_Empty():lvm_code
{   
    lvm_Block(lvm_CNil())
}       

lemma lvm_lemma_Empty(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_Empty(), bls(b), lvm_sN)
  requires lvm_get_ok(bls(b))
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, bls(b))
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, bls(b), s2) ==> s2.ok 
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehavior(b');
 
{
    
    var lvm_s0 := bls(b);

    var lvm_old_s:lvm_state := lvm_s0;

    assert lvm_s0.ok;
    assert lvm_code_Empty() == Block(CNil);
    assert lvm_b0.hd == lvm_code_Empty();
    assert !lvm_b0.CNil?;
    assert lvm_code_Empty().block.CNil?;
    assert lvm_b0.hd.Block?;
    assert lvm_get_block(lvm_b0.hd).CNil?;
    assert evalBlock(lvm_get_block(lvm_b0.hd),lvm_s0, lvm_s0);
    assert forall r :: r == lvm_s0 ==> eval_code(lvm_b0.hd,lvm_s0,r);
    assert evalCode_lax(Block(lvm_b0), lvm_s0, lvm_sN);

    // lvm_sM := lvm_lemma_empty(lvm_s0,lvm_sN);
    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);

    lvm_sM := lvm_lemma_empty(lvm_s0, lvm_sM);
    assert ValidState(lvm_sM);
    assert lvm_s0 == lvm_sM;
    assert NextStep(lvm_s0,lvm_sM,Step.stutterStep());
  assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.stutterStep());
  b' := b + [lvm_sM];
  assert ValidBehavior(b');
  assert BehaviorEvalsCode(lvm_code_Empty(),[lvm_s0,lvm_sM]);
}

function method lvm_code_ALLOCA(dst:lvm_operand_opr,t:bitWidth):(out:lvm_code)
{
    
    Ins(ALLOCA(dst,t))
}


lemma lvm_lemma_Alloca(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state,dst:lvm_operand_opr,t:bitWidth)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_ALLOCA(dst,t), bls(b), lvm_sN)
  requires lvm_get_ok(bls(b))
  requires ValidOperand(bls(b),dst)
  requires MemValid(bls(b).m)
  requires OperandContents(bls(b),dst).Ptr?
  requires validBitWidth(t)
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, bls(b), s2) ==> s2.ok 
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehaviorNonTrivial(b');
  ensures  lvm_state_eq(lvm_sM, bls(b'))



{
    
    var lvm_s0 := bls(b);
    assert lvm_code_ALLOCA(dst,t).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_ALLOCA(dst,t).ins);
    assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

    // assert exists s',b :: (Alloc(lvm_s0.m,s'.m,b,t));
    assert ValidState(lvm_s0) && lvm_s0.ok;
    assert lvm_b0.hd.ins == lvm_code_ALLOCA(dst,t).ins;
    assert lvm_b0.hd.Ins?;
    // var s':MemState := AllocaStep(lvm_s0.m,t);
    // var z:state := State(lvm_s0.lvs,lvm_s0.gvs,s',lvm_s0.ok);

    // // && s'.mem == s.mem[s.nextBlock := UninitBlock(size)]
    // assert ValidState(z); //&& Alloc(lvm_s0.m,s'.m,lvm_s0.m.nextBlock,t);
    // assert Alloc(lvm_s0.m,z.m,lvm_s0.m.nextBlock,t);
    // assert ValidData(z,evalALLOCA(lvm_s0.m,t));
    // assert z == lvm_s0.(m := s'); 
    // assert evalAlloca(lvm_s0, dst, t,z);
    // // assert exists r':state :: evalIns(lvm_b0.hd.ins, lvm_s0, r') <==> evalCode(lvm_b0.hd, lvm_s0, r');
    // assert evalIns(lvm_b0.hd.ins, lvm_s0, z);

    // assert exists r':state :: evalCode(lvm_b0.hd, lvm_s0, r') && evalBlock(lvm_b0.tl, r', lvm_sN);
    //              assert false;

    // var r':state :| evalCode(lvm_b0.hd, lvm_s0, r') && evalBlock(lvm_b0.tl, r', lvm_sN);
    //              assert false;

    // assert lvm_b0.hd == lvm_code_ALLOCA(dst,t);
    // assert evalIns(lvm_b0.hd.ins,lvm_s0,r');
    
    // assert r'.ok;
    //      assert false;

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert ValidState(lvm_s0);
    assert ValidState(lvm_sM);
    //  assert false;

    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_ALLOCA(dst,t).ins));
    assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.allocStep(lvm_s0.m.nextBlock,t));
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_ALLOCA(dst,t),[lvm_s0,lvm_sM]);

}

function method lvm_code_CALL(dst:lvm_operand_opr,fnc:lvm_codes):(out:lvm_code)
{
    
    Ins(CALL(dst,fnc))
}

lemma lvm_lemma_Call(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state,dst:lvm_operand_opr,fnc:lvm_codes)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_CALL(dst,fnc), bls(b), lvm_sN)
  requires lvm_get_ok(bls(b))
  requires ValidOperand(bls(b),dst)
requires !fnc.CNil?;
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, bls(b), s2) ==> s2.ok 
  // ensures StateNext(bls(b),lvm_sM)
  // ensures ValidBehaviorNonTrivial(b');
  // ensures  lvm_state_eq(lvm_sM, bls(b'))



{
    
    var lvm_s0 := bls(b);
    assert lvm_code_CALL(dst,fnc).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_CALL(dst,fnc).ins);
    assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

    // assert exists s',b :: (Alloc(lvm_s0.m,s'.m,b,t));
    assert ValidState(lvm_s0) && lvm_s0.ok;
    assert lvm_b0.hd.ins == lvm_code_CALL(dst,fnc).ins;
    assert lvm_b0.hd.Ins?;
    // var s':MemState := AllocaStep(lvm_s0.m,t);


    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert ValidState(lvm_s0);
    assert ValidState(lvm_sM);
    //  assert false;

    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    // assert StateNext(lvm_s0,lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_CALL(dst,fnc).ins));
    // assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.allocStep(lvm_s0.m.nextBlock,t));
    b' := b + [lvm_sM];
    assert lvm_state_eq(lvm_sM, bls(b'));
    // assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_CALL(dst,fnc),[lvm_s0,lvm_sM]);

}

function method lvm_code_MEMCPY(dst:lvm_operand_opr,src:lvm_operand_opr,len:bitWidth):(out:lvm_code)
{
    
    Ins(LLVM_MEMCPY(dst,src,len,false))
}



lemma lvm_lemma_MemCpy(b:behavior,lvm_b0:lvm_codes, lvm_sN:lvm_state,dst:lvm_operand_opr,src:lvm_operand_opr,len:bitWidth)
  returns (b':behavior,lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires ValidBehaviorNonTrivial(b);
  requires lvm_require(lvm_b0, lvm_code_MEMCPY(dst,src,len), bls(b), lvm_sN)
  requires lvm_get_ok(bls(b))
  requires ValidOperand(bls(b),dst)
  requires ValidOperand(bls(b),src)
  requires MemValid(bls(b).m)
  requires OperandContents(bls(b),dst).Ptr?
  requires OperandContents(bls(b),src).Ptr?
  requires OperandContents(bls(b),dst).size >= OperandContents(bls(b),src).size;
  requires validBitWidth(len)
  ensures  lvm_ensure(lvm_b0, lvm_bM, bls(b), lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, bls(b), s2) ==> s2.ok 
  ensures StateNext(bls(b),lvm_sM)
  ensures ValidBehaviorNonTrivial(b');
  ensures  lvm_state_eq(lvm_sM, bls(b'))



{
    
    var lvm_s0 := bls(b);
    assert lvm_code_MEMCPY(dst,src,len).Ins?;

    assert ValidInstruction(lvm_s0, lvm_code_MEMCPY(dst,src,len).ins);
    assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

    // assert exists s',b :: (Alloc(lvm_s0.m,s'.m,b,t));
    assert ValidState(lvm_s0) && lvm_s0.ok;
    assert lvm_b0.hd.ins == lvm_code_MEMCPY(dst,src,len).ins;
    assert lvm_b0.hd.Ins?;
   

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert ValidState(lvm_s0);
    assert ValidState(lvm_sM);
    //  assert false;

    assert lvm_sM.ok;
    assert lvm_b0.tl == lvm_bM;

    assert ValidState(lvm_sM);
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert NextStep(lvm_s0,lvm_sM,evalInsStep(lvm_code_MEMCPY(dst,src,len).ins));
    // assert MemStateNext(lvm_s0.m,lvm_sM.m,MemStep.allocStep(lvm_s0.m.nextBlock,t));
    b' := b + [lvm_sM];
    assert ValidBehavior(b');
    assert BehaviorEvalsCode(lvm_code_MEMCPY(dst,src,len),[lvm_s0,lvm_sM]);

}

}
