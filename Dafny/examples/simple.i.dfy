include "../LLVM/llvm.i.dfy"
include "../LLVM/control_flow.i.dfy"
include "../LLVM/generalInstructions.i.dfy"
include "../LLVM/types.dfy"
include "../LLVM/memory.i.dfy"
include "../LLVM/Operations/binaryOperations.i.dfy"


module simple_functions {
    import opened LLVM_def
    import opened control_flow
    import opened general_instructions
    import opened types
    import opened memory
    import opened binary_operations_i





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
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state,lvm_sMs:seq<lvm_state>)
  requires lvm_require(lvm_b0, lvm_code_Add_single(dst, size,src1), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires ValidState(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires ValidOperand(lvm_s0,src2);
  requires OperandContents(lvm_s0,src2).Int?;
  requires ValidOperand(lvm_s0,dst);
  requires typesMatch(OperandContents(lvm_s0,src1),Int(4,IntType(1,false)));
  requires size == OperandContents(lvm_s0,src1).itype.size
  // requires lvm_code_Add(dst, size,src1,src2).Ins?;
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM)
  ensures  ValidOperand(lvm_sM,dst)
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  OperandContents(lvm_sM,dst).Int?;
  ensures  OperandContents(lvm_sM, dst).val == 
  evalADD(OperandContents(lvm_s0,src1).itype.size,OperandContents(lvm_s0,src1),D(Int(4,IntType(1,false))).d).val;
  // ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, src1).val + 4
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
    ensures lvm_sM.ok ==> ValidStateSeq(lvm_sMs);

{
    reveal_lvm_code_Add_single();
    reveal_ValidData();
    reveal_evalCodeOpaque();
    reveal_eval_code();
    reveal_lvm_code_Add();
    lvm_sMs := [lvm_s0];
    assert lvm_code_Add_single(dst,size,src1).block.hd.Ins?;
    assert ValidState(lvm_s0);
    assert lvm_code_Add_single(dst, size,src1).block.hd.ins == ADD(dst, size,src1,D(Int(4,IntType(1,false))));
    assert ValidInstruction(lvm_s0,lvm_code_Add_single(dst,size,src1).block.hd.ins);
    assert lvm_b0.hd.Block?;
    assert lvm_b0.hd.block.hd.ins == ADD(dst, size,src1,D(Int(4,IntType(1,false))));
    assert lvm_b0.hd.block == lvm_code_Add_single(dst,size,src1).block;

    assert evalBlock(lvm_b0,lvm_s0, lvm_sN);
    // assert  ValidRegOperand(lvm_s0, dst);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
    assert lvm_b0.tl == lvm_bM;
    ghost var lvm_b2, lvm_s2 := lvm_lemma_Add(lvm_b1, lvm_s0, lvm_sM, dst, size,src1,D(Int(4,IntType(1,false))));
    assert StateNext(lvm_s0,lvm_s2);
    lvm_sMs := lvm_sMs + [lvm_s2];


    assert lvm_b2 == (lvm_CNil());
    assert eval_code(lvm_Block(lvm_b2), lvm_s2, lvm_sM);
    lvm_sM := lvm_lemma_empty(lvm_s2,lvm_sM);
    assert ValidState(lvm_sM);
    assert StateNext(lvm_s2,lvm_sM);
    lvm_sMs := lvm_sMs + [lvm_sM];


    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    reveal_evalCodeOpaque();
}


// ////

function method {:opaque} lvm_code_Add_Multiple(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr, src2:lvm_operand_opr): (out:lvm_code)
    requires src1.D?;
    requires src1.d.Int?;
    requires src2.D?;
    requires src2.d.Int?;
    ensures out.Block?;
    ensures out.block.lvm_CCons?;
    ensures out.block.hd.Ins?;

{
      reveal_IntFits();
      var val := D(Int(4,src1.d.itype));
      assert val.d.Int?;
      var void := D(Void);

      var val2 := D(Int(5,src2.d.itype));
      assert val.d.Int?;

      lvm_Block(lvm_CCons(Ins(ADD(src2,size,src1,val)),
                lvm_CCons(Ins(ADD(dst,size,src2,val2)),
                lvm_CCons(Ins(RET(void)),lvm_CNil()))))

}

lemma lvm_lemma_Add_Multiple(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state,lvm_sMs:seq<lvm_state>)
  requires src1.D?;
  requires src1.d.Int?;
  requires src2.D?;
  requires src2.d.Int?;
  requires lvm_require(lvm_b0, lvm_code_Add_Multiple(dst, size,src1,src2), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_dst_opr(src2, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires ValidOperand(lvm_s0,src2);
  requires OperandContents(lvm_s0,src2).Int?;
  requires ValidOperand(lvm_s0,dst);
  requires typesMatch(OperandContents(lvm_s0,src1),Int(4,src1.d.itype));
    requires typesMatch(OperandContents(lvm_s0,src2),Int(5,src2.d.itype));

  requires size == OperandContents(lvm_s0,src1).itype.size && size == OperandContents(lvm_s0,src2).itype.size 
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
  ensures  lvm_get_ok(lvm_sM) 
  ensures ValidOperand(lvm_sM,dst)
  ensures OperandContents(lvm_sM,dst).Int?;

  ensures OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,src1).itype.size,OperandContents(lvm_s0,src2),D(Int(5,src2.d.itype)).d).val
  // ensures ToTwosComp(OperandContents(lvm_sM, dst)).val == 
          // (OperandContents(lvm_s0, src1).val + D(Int(5,src1.d.itype)).d.val + D(Int(4,src1.d.itype)).d.val ) % Pow256(OperandContents(lvm_s0, src1).itype.size)
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
  ensures lvm_sM.ok ==> ValidStateSeq(lvm_sMs);

{
    reveal_lvm_code_Add_Multiple();
    reveal_eval_code();
    reveal_evalCodeOpaque();
    reveal_lvm_code_Add();
    reveal_lvm_code_Ret();
    lvm_sMs := [lvm_s0];

    assert lvm_code_Add_Multiple(dst, size,src1,src2).block.hd.Ins?;

    assert ValidState(lvm_s0);
    var lvm_old_s:lvm_state := lvm_s0;
    assert evalCode(lvm_Block(lvm_b0), lvm_s0, lvm_sN);
    assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
    assert lvm_b1.lvm_CCons?;
    reveal_IntFits();
    var val := D(Int(4,src1.d.itype));
    assert val.d.Int?;
    assert lvm_b1.hd == lvm_code_Add(src2, size,src1,val);
    assert ValidState(lvm_s0);
    // src2 := evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,val));
    assert lvm_code_Add(src2, size,src1,val).ins == (ADD(src2, size,src1,val));
    assert ValidInstruction(lvm_s0,(ADD(src2, size,src1,val)));
    assert ValidData(lvm_sM,evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,val)));
    // assert src2.D?;
    // assert src2.d == evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,val));
    // assert lvm_s0 == lvm_sM;
      //  assert evalCode_lax(lvm_Block(lvm_b1), lvm_s0, lvm_sM,src2);
      assert lvm_b1.hd.Ins?;
      assert lvm_b1.hd.ins.dst == src2;
      assert lvm_Block(lvm_b1).block.hd == Ins(ADD(src2, size,src1,val));
      // assert  exists r' ::  evalCode(lvm_b1.hd, lvm_s0, r',src2);
        assert evalCode(lvm_Block(lvm_b1), lvm_s0, lvm_sM);

      assert evalBlock(lvm_b1,lvm_s0, lvm_sM);
      assert evalCode(lvm_Block(lvm_b1), lvm_s0, lvm_sM);
      assert  exists r' ::  evalCode(lvm_b1.hd, lvm_s0, r');
      assert  exists r' ::  evalIns(lvm_b1.hd.ins, lvm_s0, r'); // ???  

    var val2 := D(Int(5,src2.d.itype));
    var step1 := evalADD(OperandContents(lvm_s0,src2).itype.size,OperandContents(lvm_s0,src1),val.d);

    ghost var lvm_b2, lvm_s2 := lvm_lemma_Add(lvm_b1, lvm_s0, lvm_sM, src2, size,src1,val);
    assert StateNext(lvm_s0,lvm_s2);
    lvm_sMs := lvm_sMs + [lvm_s2];

    assert OperandContents(lvm_s2, src2).val == step1.val;
    assert OperandContents(lvm_s2,src2).val == evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,val)).val;
    assert OperandContents(lvm_s0, src1) == OperandContents(lvm_s2, src1); 

    assert  lvm_require(lvm_b2, lvm_code_Add(dst, size,src2,val2), lvm_s2, lvm_sM);
    // assert ValidOperand(lvm_s2,dst);
    // assert OperandContents(lvm_s2,dst).Int?;
    // var step2 := evalADD(OperandContents(lvm_s2,dst).itype.size,OperandContents(lvm_s2,src2),val2.d);

    ghost var lvm_b3, lvm_s3 := lvm_lemma_Add(lvm_b2, lvm_s2, lvm_sM, dst, size,src2,val2);
    assert StateNext(lvm_s2,lvm_s3);
    lvm_sMs := lvm_sMs + [lvm_s3];
    assert OperandContents(lvm_s3, dst).val 
        == evalADD(OperandContents(lvm_s2,src2).itype.size,OperandContents(lvm_s2,src2),val2.d).val;
  
    // assert OperandContents(lvm_s3, dst).val  == step2.val;

    assert lvm_b3.hd.ins == RET(D(Void));

    
    ghost var lvm_b4, lvm_s4 := lvm_lemma_Ret(lvm_b3, lvm_s3, lvm_sM, dst, D(Void));
    assert StateNext(lvm_s3,lvm_s4);
    lvm_sMs := lvm_sMs + [lvm_s4];
    assert lvm_b4.CNil?;

    lvm_sM := lvm_lemma_empty(lvm_s4,lvm_sM);
    assert StateNext(lvm_s4,lvm_sM);
    lvm_sMs := lvm_sMs + [lvm_sM];
    // assert OperandContents(lvm_sM, dst).val  == step2.val;
    assert  OperandContents(lvm_s4, dst).val 
        == evalADD(OperandContents(lvm_s2,src2).itype.size,OperandContents(lvm_s2,src2),val2.d).val;
    assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
    assert OperandContents(lvm_s0, src1) == OperandContents(lvm_sM, src1); 
    assert  OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,src1).itype.size,OperandContents(lvm_s0,src2),val2.d).val;
    assert ValidState(lvm_sM);

    reveal_evalCodeOpaque();
}
// Old example // 

// function method {:opaque} lvm_code_Add_Multiple(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr): (out:lvm_code)
//     requires src1.D?;
//     requires src1.d.Int?;
//     ensures out.Block?;
//     ensures out.block.lvm_CCons?;
//     ensures out.block.hd.Ins?;

// {
//       reveal_IntFits();
//       var val := D(Int(4,src1.d.itype));
//       assert val.d.Int?;
//       var void := D(Void);

//       var val2 := D(Int(5,src1.d.itype));
//       assert val.d.Int?;

//           lvm_Block(lvm_CCons(Ins(ADD(dst,size,src1,val)),
//                 lvm_CCons(Ins(ADD(dst,size,src1,val2)),
//                 lvm_CCons(Ins(RET(void)),lvm_CNil()))))

// }

// lemma lvm_lemma_Add_Multiple(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
//             dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr)
//   returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
//   requires src1.D?;
//   requires src1.d.Int?;
//   requires lvm_require(lvm_b0, lvm_code_Add_Multiple(dst, size,src1), lvm_s0, lvm_sN)
//   requires lvm_is_dst_opr(dst, lvm_s0)
//   requires lvm_is_src_opr(src1, lvm_s0)
//   requires lvm_get_ok(lvm_s0)

//   requires ValidOperand(lvm_s0,src1);
//   requires OperandContents(lvm_s0,src1).Int?;
//   requires ValidOperand(lvm_s0,dst);
//   requires ValidOperand(lvm_s0,dst);
//   requires OperandContents(lvm_s0,dst).Int?;

//   requires ValidOperand(lvm_s0,dst)
// //   
//   ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)
//   ensures  lvm_get_ok(lvm_sM) 
//   ensures ValidOperand(lvm_sM,dst)
//   ensures OperandContents(lvm_sM,dst).Int?;
//   ensures OperandContents(lvm_s0,dst).Int?;

//   ensures  OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),D(Int(5,src1.d.itype)).d).val;
//   ensures ToTwosComp(OperandContents(lvm_sM, dst)).val == 
//           (OperandContents(lvm_s0, src1).val + D(Int(5,src1.d.itype)).d.val) % Pow256(OperandContents(lvm_s0, src1).itype.size)
//   ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_all( lvm_sM, lvm_s0)))
// {
//     reveal_lvm_code_Add_Multiple();
//     reveal_eval_code();
//     reveal_evalCodeOpaque();
//     reveal_lvm_code_Add();
//     reveal_lvm_code_Ret();

//     assert lvm_code_Add_Multiple(dst, size,src1).block.hd.Ins?;

//     assert ValidState(lvm_s0);
//     var lvm_old_s:lvm_state := lvm_s0;
//     assert evalCode(lvm_Block(lvm_b0), lvm_s0, lvm_sN);
//     assert eval_code(lvm_Block(lvm_b0), lvm_s0, lvm_sN);

//     ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
//     lvm_sM := lvm_ltmp1;
//     lvm_bM := lvm_ltmp2;
//     var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
//     assert lvm_b1.lvm_CCons?;
//     reveal_IntFits();
//     var val := D(Int(4,src1.d.itype));
//     assert val.d.Int?;
//     assert lvm_b1.hd == lvm_code_Add(dst, size,src1,val);
//     assert ValidState(lvm_s0);
//     assert evalCode_lax(lvm_Block(lvm_b1), lvm_s0, lvm_sM);
//     assert OperandContents(lvm_s0,dst).Int?;

//     // assert evalUpdate(lvm_s0, dst, evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,val)),lvm_sM);
//     assert evalCode(lvm_Block(lvm_b1), lvm_s0, lvm_sM);
//     assert evalBlock(lvm_Block(lvm_b1).block, lvm_s0, lvm_sM);
//     assert lvm_Block(lvm_b1).block.hd == Ins(ADD(dst, size,src1,val));
//     assert  exists r' ::  evalCode(lvm_b1.hd, lvm_s0, r');
//     assert  exists r' ::  evalIns(lvm_b1.hd.ins, lvm_s0, r');

//     var val2 := D(Int(5,src1.d.itype));
//     var step1 := evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),val.d);


//     ghost var lvm_b2, lvm_s2 := lvm_lemma_Add(lvm_b1, lvm_s0, lvm_sM, dst, size,src1,val);


//     assert OperandContents(lvm_s2, dst).val == step1.val;
//     assert OperandContents(lvm_s0, src1) == OperandContents(lvm_s2, src1); 

//     assert  lvm_require(lvm_b2, lvm_code_Add(dst, size,src1,val2), lvm_s2, lvm_sM);
//     var step2 := evalADD(OperandContents(lvm_s2,dst).itype.size,OperandContents(lvm_s2,src1),val2.d);

//     ghost var lvm_b3, lvm_s3 := lvm_lemma_Add(lvm_b2, lvm_s2, lvm_sM, dst, size,src1,val2);
//     assert OperandContents(lvm_s3, dst).val 
//         == evalADD(OperandContents(lvm_s2,dst).itype.size,OperandContents(lvm_s2,src1),val2.d).val;
  
//     assert OperandContents(lvm_s3, dst).val  == step2.val;
//     // assert lvm_b3.CNil?;
//     assert lvm_b3.hd.ins == RET(D(Void));

    
//     ghost var lvm_b4, lvm_s4 := lvm_lemma_Ret(lvm_b3, lvm_s3, lvm_sM, dst, D(Void));
//     assert lvm_b4.CNil?;
//     assert eval_code(lvm_Block(lvm_b4), lvm_s4, lvm_sM);
//     lvm_sM := lvm_lemma_empty(lvm_s4,lvm_sM);
//     assert   OperandContents(lvm_sM, dst).val  == step2.val;

//     assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM);
//     assert OperandContents(lvm_s0, src1) == OperandContents(lvm_sM, src1); 

//     assert OperandContents(lvm_sM, dst).val == step2.val;
//     assert  OperandContents(lvm_sM, dst).val == evalADD(OperandContents(lvm_s0,dst).itype.size,OperandContents(lvm_s0,src1),val2.d).val;
//     assert ValidState(lvm_sM);
//     reveal_evalCodeOpaque();
// }
}