include "../llvm.i.dfy"
include "../control_flow.i.dfy"
include "generalInstructions.i.dfy"
include "../types.dfy"
include "../memory.dfy"

module demo_challenge_prob_1 {
    import opened LLVM_def
    import opened control_flow
    import opened general_instructions
    import opened types
    import opened memory

//####################################################################
//
//   Simplified Source Patched Challenge Problem 1 [rx_message_routine]
//
//####################################################################

/*
void rx_message_routine(unsigned char buf[]){
  // buf[3] is the integer value, 0-255km, buff[2] is the decimal
  uint16_t speed_value = (buf[3] << 8) + buf[2];  // <-------- Vulnerability here
  uint8_t brake_switch = (buf[4] & 0b00001100) >> 2;
  serial_print("%s", " Speed = ");
  serial_print("%d", speed_value/256); serial_print("%s", ", brake =");
  serial_print("%d", brake_switch);
  serial_println("%s", "]");
  if (brake_switch){
    brake_state = true;
    brake_on();
    if (speed_value > 0 && previous_brake_state != brake_state){  // speed > 0 and brakes were off last
      need_to_flash = true;
      serial_println("%s", "Flashing=true");
    } }
  else{
    brake_state = false;
    need_to_flash = false;
    brake_off();
  }
  previous_brake_state = brake_state;
}
*/ 

//####################################################################
//
//   Simplified LLVM Patched Challenge Problem 1 [ rx_message_routine Source -> LLVM ]
//   (Cleaned up, ie. remove fncs like printf)
//
//####################################################################

/*
; Function Attrs: nofree nounwind ssp uwtable
define void @rx_message_routine(i8* nocapture readonly %0) local_unnamed_addr #0 {

  %5 = getelementptr inbounds i8, i8* %0, i64 3
  %6 = load i8, i8* %5, align 1, !tbaa !4
  %7 = zext i8 %6 to i32
  %8 = shl i32 %7, 8
  %10 = getelementptr inbounds i8, i8* %0, i64 2
  %11 = load i8, i8* %10, align 1
  %12 = zext i8 %11 to i32
  %13 = add nsw i32 %8, %12
  %14 = trunc i32 %13 to i16
  %16 = zext i16 %14 to i32
  %17 = icmp sgt i32 %16, 0
  br i1 %17, label %18, label %23

18:                                               ; preds = %1
  store i8 1, i8* @need_to_flash, align 1
  br label %19

19:                                               ; preds = %18
  %20 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i64 0, i64 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.3, i64 0, i64 0))
  %21 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.1, i64 0, i64 0))
  br label %22

22:                                               ; preds = %19
  br label %23

23:                                               ; preds = %22, %1
  %24 = load i8, i8* @brake_state, align 1
  %25 = trunc i8 %24 to i1
  %26 = zext i1 %25 to i8
  store i8 %26, i8* @previous_brake_state, align 1
  ret void
}
*/

function {:opaque} demo_challenge_prob_1_code(dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr,
                                              var_5:lvm_operand_opr,var_index2:lvm_operand_opr,comp:lvm_operand_opr):lvm_code
{
    reveal_IntFits();
    var void := D(Void);
    var index3 := D(Int(3,IntType(8,false)));
    var index2 := D(Int(2,IntType(8,false)));
    var shl_amount := D(Int(8,IntType(1,false)));

    // var var_5:lvm_operand_opr :| var_5 == dst;
    var var_6:lvm_operand_opr :| var_6 == dst;
    var var_7:lvm_operand_opr :| var_7 == dst;
    var var_8:lvm_operand_opr :| var_8 == dst;
    // var var_9:lvm_operand_opr :| var_9 == dst;

    // var var_index2:lvm_operand_opr :| var_index2 == dst;

    lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(var_5,1,op1,index3)),                  // %5 = getelementptr inbounds i8, i8* %0, i64 3
              lvm_CCons(Ins(LOAD(var_6,s,1,var_5)),                              // %6 = load i8, i8* %2, align 1, !tbaa !4
              lvm_CCons(Ins(ZEXT(var_7,t,var_6,4)),                              // %7 = zext i8 %3 to i32
              lvm_CCons(Ins(SHL(var_8,var_7,shl_amount)),                        // %8 = shl i32 %7, 8
              lvm_CCons(Ins(GETELEMENTPTR(var_index2,1,op2,index2)),             // %10 = getelementptr inbounds i8, i8* %0, i64 2
              lvm_CCons(Ins(LOAD(var_index2,s,1,var_index2)),                    // %11 = load i8, i8* %10, align 1
              lvm_CCons(Ins(ZEXT(var_index2,t,var_index2,4)),                    // %12 = zext i8 %11 to i32
              lvm_CCons(Ins(ADD(dst,4,var_8,var_index2)),                        // %13 = add nsw i32 %8, %12
              lvm_CCons(Ins(ICMP(comp,sgt,4,var_8,D(Int(0,IntType(4,false))))),  // %17 = icmp sgt i32 %16, 0 
              lvm_CCons(Ins(RET(void)),lvm_CNil())))))))))))                     // ret void

}

lemma lvm_demo_challenge_prob_1(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr,s:MemState,t:bitWidth,op1:lvm_operand_opr,op2:lvm_operand_opr,
            var_5:lvm_operand_opr,var_index2:lvm_operand_opr,comp:lvm_operand_opr)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires op1.D?;
  requires op2.D?;
  requires lvm_require(lvm_b0, demo_challenge_prob_1_code(dst,lvm_s0.m,t,op1,op2,var_5,var_index2,comp), lvm_s0, lvm_sN)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(op1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,op1);
  requires ValidOperand(lvm_s0,op2);
  requires ValidOperand(lvm_s0,dst);
  requires ValidOperand(lvm_s0,var_5);
  requires ValidOperand(lvm_s0,var_index2);
  requires ValidOperand(lvm_s0,comp);
  requires operandsUnique(lvm_s0,[dst,var_index2,var_5,comp]);
  // requires dst != var_index2 != var_5 != comp;

  requires OperandContents(lvm_s0,op1).Ptr?;
  requires OperandContents(lvm_s0,op2).Ptr?;
  requires OperandContents(lvm_s0,op1).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires OperandContents(lvm_s0,op2).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires IsValidBid(lvm_s0.m,op1.d.bid) ==> op1.d.offset + ((Int(3,IntType(8,false))).val * 1) < |lvm_s0.m.mem[op1.d.bid]|;
  requires IsValidBid(lvm_s0.m,op2.d.bid) ==> op2.d.offset + ((Int(2,IntType(8,false))).val * 1) < |lvm_s0.m.mem[op2.d.bid]|;

//   

  ensures ValidOperand(lvm_sM,dst)
  ensures ValidOperand(lvm_sM, var_index2)

  ensures  lvm_get_ok(lvm_sM)

  ensures  !OperandContents(lvm_sM, dst).Void? ==> OperandContents(lvm_sM, dst).Int?;
  ensures  !OperandContents(lvm_sM, dst).Void? ==> OperandContents(lvm_sM, dst).itype.size == 4;
  ensures  !OperandContents(lvm_sM, dst).Void? ==> OperandContents(lvm_sM, dst).val < 0x1_0000_0000;
  ensures  !OperandContents(lvm_sM, dst).Void? ==> OperandContents(lvm_sM, dst).val >= 0;

  ensures  (!OperandContents(lvm_sM, dst).Void? && !OperandContents(lvm_sM, var_index2).Void?) ==> lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
  ensures  (!OperandContents(lvm_sM, dst).Void? && !OperandContents(lvm_sM, var_index2).Void?) ==> lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN)

{
  reveal_demo_challenge_prob_1_code();
  reveal_lvm_code_Ret();
  reveal_lvm_LOAD();
  reveal_lvm_code_Add();
  reveal_lvm_code_ZEXT();
  reveal_lvm_code_SHL();
  reveal_lvm_code_ICMP();
  reveal_lvm_code_Empty();
  reveal_lvm_code_GetElementPtr();
  reveal_ValidData();
  reveal_evalCodeOpaque();
  reveal_eval_code();

  var var_7:lvm_operand_opr :| var_7 == dst;
  var var_8:lvm_operand_opr :| var_8 == dst;

  assert demo_challenge_prob_1_code(dst,lvm_s0.m,t,op1,op2,var_5,var_index2,comp).Block?;
  assert lvm_b0.hd.Block?;
  assert evalBlock(lvm_b0, lvm_s0, lvm_sN);

  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, lvm_sN);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert lvm_b1.lvm_CCons?;
  assert lvm_b1.hd.Ins?;
  assert lvm_b1.hd.ins.GETELEMENTPTR?;
  assert lvm_b1.tl.lvm_CCons?;
  assert lvm_b1.tl.hd.Ins?;
  assert lvm_b1.tl.hd.ins.LOAD?;

  // var var_5:lvm_operand_opr :| lvm_require(lvm_b1, lvm_code_GetElementPtr(var_5,1,op1,D(Int(2,IntType(8,false)))),lvm_s0, lvm_sM,var_5);
  // var var_5:lvm_operand_opr :| lvm_require(lvm_b1, lvm_code_GetElementPtr(var_5,1,op1,D(Int(3,IntType(8,false)))),lvm_s0, lvm_sM);
  assert lvm_b1.hd == Ins(GETELEMENTPTR(var_5,1,op1,D(Int(3,IntType(8,false)))));
  assert lvm_sM == lvm_s0;
  ghost var lvm_b2, lvm_s2 := lvm_lemma_GetElementPtr(lvm_b1, lvm_s0, lvm_sM, var_5, lvm_s0.m,1,op1,D(Int(3,IntType(8,false))));
  assert OperandContents(lvm_s2, var_5) 
        == evalGETELEMENTPTR(lvm_s0.m,1,OperandContents(lvm_s0,op1),Int(3,IntType(8,false)));
  assert lvm_s0.m == lvm_s2.m;

  assert lvm_b2.hd.Ins?;
  assert lvm_b2.hd.ins.LOAD?;

  assert lvm_s0.m == lvm_s2.m;
  assert IsValidBid(lvm_s2.m,OperandContents(lvm_s2,var_5).bid);
  assert IsValidPtr(lvm_s2.m,OperandContents(lvm_s2,var_5).bid,OperandContents(lvm_s2,op1).offset);
  assert lvm_s2.m == lvm_sM.m;

  // var var_6:lvm_operand_opr :| lvm_require(lvm_b2, lvm_LOAD(var_6,lvm_s2.m,1,var_5), lvm_s2, lvm_sM,var_6);
    assert ValidOperand(lvm_s2,dst);

  ghost var lvm_b3, lvm_s3 := lvm_lemma_Load(lvm_b2, lvm_s2, lvm_sM, dst,1,var_5);
  assert lvm_s3.m == lvm_s2.m;
  assert !OperandContents(lvm_s3,dst).Ptr?;
  if (OperandContents(lvm_s3,dst).Void?) { // LOAD ins failed
    lvm_sM := lvm_s3;
    assert OperandContents(lvm_sM, dst).Void?;
    return;
  }
    assert OperandContents(lvm_s3,dst).Int? || OperandContents(lvm_s3,dst).Bytes?;
    assert lvm_b3.hd.Ins?;
    assert lvm_b3.hd.ins.ZEXT?;
    assert lvm_b3.hd.ins == ZEXT(var_7,t,dst,4);
    assert lvm_b3.tl.lvm_CCons?;
    assert lvm_b3.tl.hd.Ins?;
    assert lvm_b3.tl.hd.ins.SHL?;
    assert OperandContents(lvm_s3,dst).Int?; //   requires OperandContents(lvm_s0,op1).Int?;
   
    // assert t == OperandContents(lvm_s3,dst).itype.size;// requires t == OperandContents(lvm_s0,op1).itype.size;
    assert OperandContents(lvm_s3,dst).itype.size < 4;
  // requires OperandContents(lvm_s0,dst).Int?;
  // assert OperandContents(lvm_s3,dst).itype.signed;

    ghost var lvm_b4, lvm_s4 := lvm_lemma_Zext(lvm_b3, lvm_s3, lvm_sM, var_7, t,dst,4);
    assert OperandContents(lvm_s4, var_7).Int?;
    assert OperandContents(lvm_s4,var_7).val >= 0;
    assert !OperandContents(lvm_s4,var_7).itype.signed;
    assert lvm_s3.m == lvm_s4.m;

    assert lvm_s4.ok;
    assert !lvm_b4.CNil?;
    assert lvm_b4.hd.Ins?;
    assert lvm_b4.hd.ins.SHL?;
    assert lvm_b4.tl.hd.Ins?;// == lvm_Block(lvm_CCons(Ins(RET(D(Void))),lvm_CNil()));

    // assert lvm_b4.hd
//    ghost var lvm_b2, lvm_s2 := lvm_lemma_Add(lvm_b1, lvm_s0, lvm_sM, src2, size,src1,val,o);
    var shl_amount := D(Int(8,IntType(1,false)));
    assert lvm_s4.ok;
    var temp :| temp == OperandContents(lvm_s4,var_7).val;
    ghost var lvm_b5, lvm_s5 := lvm_lemma_Shl(lvm_b4, lvm_s4, lvm_sM, var_8,var_7,shl_amount);
    assert lvm_s4.m == lvm_s5.m;

    assert OperandContents(lvm_s5,var_8).itype.size == 4;
    assert OperandContents(lvm_s5, var_8).val >= 0;
    assert  OperandContents(lvm_s5,var_8).Int?;

    var ex:lvm_operand_opr := copyIntOperand(OperandContents(lvm_s5,var_8));

       assert OperandContents(lvm_s5,ex).itype.size == 4;
    assert OperandContents(lvm_s5, ex).val >= 0;
    assert  OperandContents(lvm_s5,ex).Int?;

    // assert OperandContents(lvm_s5, var_8).val > temp;
     assert OperandContents(lvm_s5,ex).itype.size == 4;
    assert OperandContents(lvm_s5, ex).val >= 0;

    assert lvm_b5.hd.Ins?;
    assert lvm_b5.hd.ins.GETELEMENTPTR?;
    assert lvm_s5.ok;
    assert lvm_b5.lvm_CCons?;
    assert ValidState(lvm_s5);
    assert lvm_b5.tl.hd.ins.LOAD?;
    assert !lvm_b5.tl.tl.CNil?;

    // assert evalCode(lvm_Block(lvm_b5), lvm_s5, lvm_sM,opTest);// lvm_require(lvm_b5, lvm_code_GetElementPtr(var_index2,1,op2,D(Int(2,IntType(8,false)))),lvm_s5, lvm_sM,var_index2);
    // var var_index2:lvm_operand_opr :| lvm_require(lvm_b5, lvm_code_GetElementPtr(var_index2,1,op2,D(Int(2,IntType(8,false)))),lvm_s5, lvm_sM,var_index2);//evalCode_lax(lvm_Block(lvm_b5), lvm_s5, lvm_sM,var_index2);
    // assert lvm_b5.hd == Ins(GETELEMENTPTR(var_index2,1,op2,D(Int(2,IntType(8,false)))));
    assert  OperandContents(lvm_s5,var_8).Int?;

    assert lvm_s4.m.mem == lvm_s5.m.mem;
    ghost var lvm_b6, lvm_s6 := lvm_lemma_GetElementPtr(lvm_b5, lvm_s5, lvm_sM, var_index2, s,1,op2,D(Int(2,IntType(8,false))));
    assert lvm_s5.m.mem == lvm_s6.m.mem;

    // LOAD now
    ghost var lvm_b7, lvm_s7 := lvm_lemma_Load(lvm_b6, lvm_s6, lvm_sM, var_index2,1,var_index2);
    assert lvm_s6.m.mem == lvm_s7.m.mem;
    if (OperandContents(lvm_s7,var_index2).Void?) { // LOAD ins failed
      lvm_sM := lvm_s7;
      assert OperandContents(lvm_sM, var_index2).Void?;
      return;
    }
    assert OperandContents(lvm_s7,var_index2).Int? || OperandContents(lvm_s7,var_index2).Bytes?;
    

    assert lvm_b7.hd.ins.ZEXT?;
    ghost var lvm_b8, lvm_s8 := lvm_lemma_Zext(lvm_b7, lvm_s7, lvm_sM, var_index2, t,var_index2,4);
    assert OperandContents(lvm_s8,var_index2).itype.size == 4;

    assert lvm_b8.hd.ins.ADD?;
    ghost var lvm_b9, lvm_s9 := lvm_lemma_Add(lvm_b8, lvm_s8, lvm_sM, dst,4,dst,var_index2);

    var arr55 :=[dst,var_index2,var_5,comp];
    assert operandsUnique(lvm_s9,arr55);
    assert arr55[0] == dst && arr55[1] == var_index2;
    assert dst != var_index2;
    assert var_8 != var_index2;
    assert  OperandContents(lvm_s9,var_8).Int?;

    ghost var lvm_b10, lvm_s10:= lvm_lemma_Icmp(lvm_b9, lvm_s9, lvm_sM, comp,sgt,4,var_8,D(Int(0,IntType(4,false))));
    

    ghost var lvm_b11, lvm_s11:= lvm_lemma_Ret(lvm_b10, lvm_s10, lvm_sM, dst, D(Void));

    assert lvm_b11 == (lvm_CNil());
    assert eval_code(lvm_Block(lvm_b11), lvm_s10, lvm_sM);
    lvm_sM := lvm_lemma_empty(lvm_s11,lvm_sM);
    assert OperandContents(lvm_sM, dst).Int?;
    assert OperandContents(lvm_sM,dst).itype.size == 4;
    // assert OperandContents(lvm_sM,dst).val <= 4;

    assert ValidState(lvm_sM);
    
    assert evalCode(lvm_cM, lvm_s0, lvm_sM);
    reveal_evalCodeOpaque();
  
}


}