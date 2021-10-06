include "./llvm.i.dfy"
include "./control_flow.i.dfy"
include "./types.dfy"
include "./memory.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"

module general_instructions {
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
lemma lvm_lemma_Add(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires lvm_require(lvm_b0, lvm_code_Add(dst, size,src1,src2), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires ValidOperand(lvm_s0,src2);
  requires OperandContents(lvm_s0,src2).Int?;
  requires ValidOperand(lvm_s0,dst);
  // requires OperandContents(lvm_s0,dst).Int?;

  requires typesMatch(OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2))
  requires size == OperandContents(lvm_s0,src1).itype.size
  requires lvm_code_Add(dst, size,src1,src2).Ins?;
// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
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
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_all(lvm_sM, lvm_s0)))
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, lvm_s0, s2) ==> s2.ok
    // ensures typesMatch(OperandContents(lvm_sM,src1),OperandContents(lvm_sM,src2))

  // ensures OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)).val;
  ensures ToTwosComp(OperandContents(lvm_sM, dst)).val == 
          (OperandContents(lvm_s0, src1).val + OperandContents(lvm_s0, src2).val) % Pow256(OperandContents(lvm_s0, src1).itype.size)
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)
{
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

lemma lvm_lemma_GetElementPtr(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  
  requires lvm_require(lvm_b0, lvm_code_GetElementPtr(dst,t,op1,op2), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,op2);
  requires OperandContents(lvm_s0,op1).Ptr?;
  requires OperandContents(lvm_s0,op2).Int?;
  requires !OperandContents(lvm_s0,op2).itype.signed;
  // requires |lvm_s0.m.mem[OperandContents(lvm_s0,op1).bid]| == t

  requires OperandContents(lvm_s0,op1).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires ValidOperand(lvm_s0,dst)
//   
ensures lvm_s0.m == lvm_sM.m;
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Ptr?;
  ensures  OperandContents(lvm_sM, dst) == evalGETELEMENTPTR(lvm_s0.m,t,OperandContents(lvm_s0,op1),OperandContents(lvm_s0,op2));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)

{
  
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
  requires ValidState(b[|b|-1]);
  requires lvm_require(lvm_b0, lvm_code_Ret(op1), b[|b|-1], lvm_sN);
  requires ValidOperand(b[|b|-1],op1);
  // requires lvm_s0 == b[|b|-1];
  ensures  lvm_ensure(lvm_b0, lvm_bM, b[|b|-1], lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  OperandContents(b[|b|-1],op1).Void? ==> b[|b|-1] == lvm_sM
  ensures  lvm_state_eq(lvm_sM,  b[|b|-1])
  ensures lvm_bM == lvm_b0.tl;
  // ensures forall d :: ValidOperand(b[|b|-1],d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(b[|b|-1],d) == OperandContents(lvm_sM,d)
  ensures StateNext(b[|b|-1],lvm_sM);
  ensures ValidBehavior(b');

{
  // assert forall
  // assert exists s' :: evalIns(code.ins,lvm_s0,s');
  // var s' :| evalCode(code,lvm_s0,s');
  var lvm_s0 := b[|b|-1];
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



lemma lvm_lemma_Load(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state,dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_LOAD(dst,t,op1), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,dst);
  requires OperandContents(lvm_s0,op1).Ptr?;
  requires MemValid(lvm_s0.m);
  requires IsValidPtr(lvm_s0.m,OperandContents(lvm_s0,op1).bid,OperandContents(lvm_s0,op1).offset,t);
  // requires lvm_s0.m == lvm_sN.m;
//   
  ensures  lvm_sM.ok ==> lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_sM.ok ==> lvm_get_ok(lvm_sM)
  ensures  lvm_sM.ok ==> ValidOperand(lvm_sM,dst);
  ensures  lvm_sM.ok ==> !OperandContents(lvm_sM,dst).Ptr?;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int?;

  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Bytes? ==> validBitWidth(|OperandContents(lvm_sM,dst).bytes|)
  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? || OperandContents(lvm_sM,dst).Bytes? || OperandContents(lvm_sM,dst).Void?;
  ensures lvm_sM.ok ==> OperandContents(lvm_sM,dst).Int? ==> OperandContents(lvm_sM,dst).itype.size == t;
  ensures lvm_s0.m == lvm_sM.m;
  ensures lvm_sM.ok ==> forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures lvm_sM.ok ==> StateNext(lvm_s0,lvm_sM)

{
  
  
  

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

}



function method lvm_code_ZEXT(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(ZEXT(dst,t,op1,dstSize))
}

lemma lvm_lemma_Zext(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires lvm_require(lvm_b0, lvm_code_ZEXT(dst,t,op1,dstSize), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,dst);
  requires OperandContents(lvm_s0,op1).Int?;
  requires OperandContents(lvm_s0,op1).itype.size < dstSize;
//   requires !OperandContents(lvm_s0,dst).itype.signed;

// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures !OperandContents(lvm_sM,dst).itype.signed;
  ensures  OperandContents(lvm_sM,dst).itype.size == dstSize;
  ensures OperandContents(lvm_sM, dst).val == evalZEXT(OperandContents(lvm_s0,op1),dstSize).val;
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures lvm_s0.m == lvm_sM.m;
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)

{
    
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
}


function method lvm_code_SEXT(dst:lvm_operand_opr,t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(SEXT(dst,t,op1,dstSize))
}

lemma lvm_lemma_Sext(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, t:bitWidth,op1:lvm_operand_opr,dstSize:bitWidth)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires lvm_require(lvm_b0, lvm_code_SEXT(dst,t,op1,dstSize), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

//   requires ValidInstruction(lvm_s0, lvm_code_ZEXT(dst,t,op1,dstSize).ins);
  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,dst);
  requires OperandContents(lvm_s0,op1).Int?;
  requires OperandContents(lvm_s0,op1).itype.size < dstSize;
  requires OperandContents(lvm_s0,dst).Int?;
//   requires !OperandContents(lvm_s0,dst).itype.signed;

// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_sM,dst).itype.signed;
  ensures  OperandContents(lvm_sM,dst).itype.size == dstSize;
  ensures OperandContents(lvm_sM, dst).val == evalSEXT(OperandContents(lvm_s0,op1),dstSize).val;
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)

{
    
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

}

function method lvm_code_SHL(dst:lvm_operand_opr,src:lvm_operand_opr,shiftAmt:lvm_operand_opr):(out:lvm_code)
    ensures out.Ins?;
{
    
    Ins(SHL(dst,src,shiftAmt))
}

lemma lvm_lemma_Shl(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, src:lvm_operand_opr,shiftAmt:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)

  requires lvm_require(lvm_b0, lvm_code_SHL(dst,src,shiftAmt), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src, lvm_s0)
  requires lvm_get_ok(lvm_s0)

// is valid ins
  requires ValidOperand(lvm_s0,src);
  requires ValidOperand(lvm_s0,dst);
  requires ValidOperand(lvm_s0,shiftAmt);

  requires OperandContents(lvm_s0,src).Int?;
  // requires OperandContents(lvm_s0,dst).Int?;
  requires OperandContents(lvm_s0,shiftAmt).Int?;
  requires OperandContents(lvm_s0,src).itype.size*8 > OperandContents(lvm_s0,shiftAmt).val
  requires OperandContents(lvm_s0,shiftAmt).val > 0
// //   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  ValidOperand(lvm_sM,src)

  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  OperandContents(lvm_sM,src).Int?;

  ensures OperandContents(lvm_sM,dst).itype.size == OperandContents(lvm_sM,src).itype.size 
  ensures OperandContents(lvm_sM,dst).itype.signed == OperandContents(lvm_sM,src).itype.signed
  ensures OperandContents(lvm_sM, dst) == evalSHL(OperandContents(lvm_s0,src),OperandContents(lvm_s0,shiftAmt));
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures lvm_s0.m == lvm_sM.m;
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)

{
    
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

}

function method lvm_code_ICMP(dst:lvm_operand_opr,cond:lvm_cond,size:nat,op1:lvm_operand_opr,op2:lvm_operand_opr):(out:lvm_code)
{
    
    Ins(ICMP(dst,cond,size,op1,op2))
}

lemma lvm_lemma_Icmp(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state,
                    dst:lvm_operand_opr,cond:lvm_cond,size:nat,op1:lvm_operand_opr,op2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_ICMP(dst,cond,size,op1,op2), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires lvm_code_ICMP(dst,cond,size,op1,op2).Ins?;
  // requires ValidInstruction(lvm_s0,lvm_code_ICMP(dst,cond,size,op1,op2).ins);
  requires ValidOperand(lvm_s0,dst) && ValidOperand(lvm_s0,op1) && ValidOperand(lvm_s0,op2);
  requires OperandContents(lvm_s0,op1).Int?;
  requires OperandContents(lvm_s0,op2).Int?;
  requires typesMatch(OperandContents(lvm_s0,op1),OperandContents(lvm_s0,op2));
  requires size == OperandContents(lvm_s0,op1).itype.size

  ensures lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)
  ensures ValidOperand(lvm_sM,op1)
  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_sM,op1).Int?;
  ensures OperandContents(lvm_s0,op1).itype == OperandContents(lvm_sM,op1).itype;
  ensures !OperandContents(lvm_sM,dst).itype.signed
  ensures OperandContents(lvm_sM,dst).itype.size == 1 

  ensures OperandContents(lvm_sM, dst) == evalICMP(cond,size,OperandContents(lvm_s0,op1),OperandContents(lvm_s0,op2));
  ensures lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures forall d :: ValidOperand(lvm_s0,d) && d != dst ==> ValidOperand(lvm_sM,d) && OperandContents(lvm_s0,d) == OperandContents(lvm_sM,d)
  ensures StateNext(lvm_s0,lvm_sM)

{
    

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


}

function method lvm_code_Empty():lvm_code
{   
    lvm_Block(lvm_CNil())
}       

lemma lvm_lemma_Empty(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Empty(), lvm_s0, lvm_sN)
  requires lvm_get_ok(lvm_s0)
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) // ValidState(sM)
  ensures  lvm_state_eq(lvm_sM, lvm_s0)
  ensures  lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
  ensures  forall s2 :: evalCode(lvm_b0.hd, lvm_s0, s2) ==> s2.ok 
    ensures StateNext(lvm_s0,lvm_sM)

{
    

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
}


}
