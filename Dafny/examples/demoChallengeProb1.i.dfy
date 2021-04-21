include "../llvm.i.dfy"
include "../control_flow.i.dfy"
include "generalInstructions.i.dfy"
include "../types.dfy"
include "../memory.i.dfy"

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

int main(int argc, const char *argv[]) {
  // default input
  unsigned char buf[8] = { 0, 1, 2, 3, 4, 5, 6, 7};

  // optional input
  for(int i = 1; i < argc && i < sizeof(buf)/sizeof(buf[0]); i++) {
    buf[i] = (unsigned char)atoi(argv[i]);
  }

  rx_message_routine(buf);
  return 0;
}


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
  %17 = icmp eq i32 %13, 0 // ugt
  ret void
}
*/

function {:opaque} demo_challenge_prob_1_code(speed_value:lvm_operand_opr,s:MemState,var_0:lvm_operand_opr,
                                              var_5:lvm_operand_opr,var_10:lvm_operand_opr,var_17:lvm_operand_opr,
                                              var_6:lvm_operand_opr,var_7:lvm_operand_opr,var_8:lvm_operand_opr,var_11:lvm_operand_opr,var_12:lvm_operand_opr):lvm_code
{
    reveal_IntFits();
    var index3 := D(Int(3,IntType(8,false)));
    var index2 := D(Int(2,IntType(8,false)));
    var shl_amount := D(Int(8,IntType(1,false)));


    lvm_Block(lvm_CCons(Ins(GETELEMENTPTR(var_5,1,var_0,index3)),                         // %5 = getelementptr inbounds i8, i8* %0, i64 3
              lvm_CCons(Ins(LOAD(var_6,s,1,var_5)),                                       // %6 = load i8, i8* %2, align 1, !tbaa !4
              lvm_CCons(Ins(ZEXT(var_7,1,var_6,4)),                                       // %7 = zext i8 %3 to i32
              lvm_CCons(Ins(SHL(var_8,var_7,shl_amount)),                                 // %8 = shl i32 %7, 8
              lvm_CCons(Ins(GETELEMENTPTR(var_10,1,var_0,index2)),                        // %10 = getelementptr inbounds i8, i8* %0, i64 2
              lvm_CCons(Ins(LOAD(var_11,s,1,var_10)),                                     // %11 = load i8, i8* %10, align 1
              lvm_CCons(Ins(ZEXT(var_12,1,var_11,4)),                                     // %12 = zext i8 %11 to i32
              lvm_CCons(Ins(ADD(speed_value,4,var_8,var_12)),                             // %13 = add nsw i32 %8, %12
              lvm_CCons(Ins(ICMP(var_17,ugt,4,speed_value,D(Int(0,IntType(4,false))))),   // %17 = icmp ugt i32 %13, 0 
              lvm_CCons(Ins(RET(D(Void))),lvm_CNil())))))))))))                           // ret void

}

lemma lvm_demo_simple_challenge_prob_1(lvm_b0:lvm_codes, lvm_s0:lvm_state,var_0:lvm_operand_opr,var_5:lvm_operand_opr,
                                       var_6:lvm_operand_opr,var_7:lvm_operand_opr,var_8:lvm_operand_opr,var_10:lvm_operand_opr,
                                       var_11:lvm_operand_opr,var_12:lvm_operand_opr,speed_value:lvm_operand_opr, var_17:lvm_operand_opr)
      returns (lvm_bM:lvm_codes, lvm_sM:lvm_state,lvm_sMs:seq<lvm_state>)
// PRE Conditions 
  requires exists sN :: lvm_require(lvm_b0, demo_challenge_prob_1_code(speed_value,lvm_s0.m,var_0,var_5,var_10,var_17,var_6,var_7,var_8,var_11,var_12), lvm_s0, sN)
  requires lvm_b0.tl.CNil?

  requires ValidState(lvm_s0)
  requires ValidOperand(lvm_s0,var_0);
  requires ValidOperand(lvm_s0,var_5);
  requires ValidOperand(lvm_s0,var_6);
  requires ValidOperand(lvm_s0,var_7);
  requires ValidOperand(lvm_s0,var_8);
  requires ValidOperand(lvm_s0,var_11);
  requires ValidOperand(lvm_s0,var_12);
  requires ValidOperand(lvm_s0,speed_value);
  requires ValidOperand(lvm_s0,var_10);
  requires ValidOperand(lvm_s0,var_17);
  requires operandsUnique(lvm_s0,[speed_value,var_10,var_5,var_6,var_7,var_8,var_11,var_12,var_17]);
  
  requires var_0.D? && OperandContents(lvm_s0,var_0).Ptr?;
  requires OperandContents(lvm_s0,var_0).bid in lvm_s0.m.mem; //needed for IsValidBid for valid input
  requires IsValidBid(lvm_s0.m,var_0.d.bid) ==> var_0.d.offset + ((Int(8,IntType(1,false))).val * 1) < |lvm_s0.m.mem[var_0.d.bid]|;

// POST Conditions
  // end state is valid 
  ensures lvm_sM.ok ==> ValidState(lvm_sM)
  // operands are valid in end state
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_0);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_5);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_6);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_7);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_8);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_11);
  ensures lvm_sM.ok ==> ValidOperand(lvm_s0,var_12);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,speed_value);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_10);
  ensures lvm_sM.ok ==> ValidOperand(lvm_sM,var_17);

  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, var_8).Int?;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, speed_value).Int?;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, var_17).Int?;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, speed_value).itype.size == 4;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, speed_value).val < 0x1_0000_0000;
  ensures  lvm_sM.ok ==> OperandContents(lvm_sM, speed_value).val >= 0;
  
  ensures  lvm_sM.ok ==> (OperandContents(lvm_sM,speed_value).val > 0 ==> OperandContents(lvm_sM,var_17).val == 1);

  ensures lvm_sM.ok ==> lvm_ensure(lvm_b0, lvm_CNil(), lvm_s0, lvm_sM, lvm_sM)
  ensures lvm_sM.ok ==> ValidStateSeq(lvm_sMs);
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
    lvm_sMs := [lvm_s0];
    var operands :=[speed_value,var_10,var_5,var_6,var_7,var_8,var_11,var_12,var_17];

    var codeBlock := demo_challenge_prob_1_code(speed_value,lvm_s0.m,var_0,var_5,var_10,var_17,var_6,var_7,var_8,var_11,var_12);
    var sN :|  lvm_require(lvm_b0, codeBlock, lvm_s0, sN);

    ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(lvm_b0, lvm_s0, sN);
    lvm_sM := lvm_ltmp1;
    lvm_bM := lvm_ltmp2;
    assert lvm_bM == lvm_b0.tl;
    assert lvm_bM.CNil?;
    var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);

    assert lvm_b1.hd == Ins(GETELEMENTPTR(var_5,1,var_0,D(Int(3,IntType(8,false)))));
    // assert lvm_sM == lvm_s0;

    ghost var lvm_b2, lvm_s2 := lvm_lemma_GetElementPtr(lvm_b1, lvm_s0, lvm_sM, var_5, lvm_s0.m,1,var_0,D(Int(3,IntType(8,false))));
    assert lvm_s0.m == lvm_s2.m;
    assert StateNext(lvm_s0,lvm_s2);
    lvm_sMs := lvm_sMs + [lvm_s2];

    ghost var lvm_b3, lvm_s3 := lvm_lemma_Load(lvm_b2, lvm_s2, lvm_sM, var_6,1,var_5);
    assert lvm_s3.m == lvm_s2.m;


    if (!lvm_s3.ok) { // LOAD ins failed
      lvm_sM := lvm_s3;
      assert !lvm_sM.ok;
      return;
    }
    assert StateNext(lvm_s2,lvm_s3);
    lvm_sMs := lvm_sMs + [lvm_s3];

    assert OperandContents(lvm_s3,var_6).Int?;
    ghost var lvm_b4, lvm_s4 := lvm_lemma_Zext(lvm_b3, lvm_s3, lvm_sM, var_7, 1,var_6,4);
    assert lvm_s3.m == lvm_s4.m;
    assert StateNext(lvm_s3,lvm_s4);
    lvm_sMs := lvm_sMs + [lvm_s4];

    assert OperandContents(lvm_s4,var_7).Int?;
    assert OperandContents(lvm_s4,var_7).itype.size == 4;


    var shl_amount := D(Int(8,IntType(1,false)));
    ghost var lvm_b5, lvm_s5 := lvm_lemma_Shl(lvm_b4, lvm_s4, lvm_sM, var_8,var_7,shl_amount);
    assert lvm_s4.m == lvm_s5.m;
    assert StateNext(lvm_s4,lvm_s5);
    lvm_sMs := lvm_sMs + [lvm_s5];


    assert OperandContents(lvm_s5,var_8).itype.size == 4;
    assert OperandContents(lvm_s5, var_8).val >= 0;
    assert OperandContents(lvm_s5,var_8).Int?;
    assert !OperandContents(lvm_s5,var_8).itype.signed;

    assert lvm_b5.hd.Ins?;
    assert lvm_b5.hd.ins.GETELEMENTPTR?;

    ghost var lvm_b6, lvm_s6 := lvm_lemma_GetElementPtr(lvm_b5, lvm_s5, lvm_sM, var_10, lvm_s5.m,1,var_0,D(Int(2,IntType(8,false))));
    assert lvm_s5.m == lvm_s6.m;
    assert StateNext(lvm_s5,lvm_s6);
    lvm_sMs := lvm_sMs + [lvm_s6];

      // LOAD now
    assert operandsUnique(lvm_s6,operands);
    assert operands[5] == var_8 && operands[1] == var_10;
    assert OperandContents(lvm_s6,var_8).Int?;
    assert !OperandContents(lvm_s6,var_8).itype.signed;

    ghost var lvm_b7, lvm_s7 := lvm_lemma_Load(lvm_b6, lvm_s6, lvm_sM, var_11,1,var_10);
    assert lvm_s6.m == lvm_s7.m;
    if (!lvm_s7.ok) { // LOAD ins failed
      lvm_sM := lvm_s7;
      assert !lvm_sM.ok;
      return;
    }
    assert StateNext(lvm_s6,lvm_s7);
    lvm_sMs := lvm_sMs + [lvm_s7];

    assert OperandContents(lvm_s7,var_11).Int?;
    assert operandsUnique(lvm_s6,operands);
    assert operands[5] == var_8 && operands[6] == var_11;

    assert lvm_b7.hd.ins.ZEXT?;
    ghost var lvm_b8, lvm_s8 := lvm_lemma_Zext(lvm_b7, lvm_s7, lvm_sM, var_12, 1,var_11,4);
    assert StateNext(lvm_s7,lvm_s8);
    lvm_sMs := lvm_sMs + [lvm_s8];

    assert lvm_b8.hd.ins.ADD?;
    ghost var lvm_b9, lvm_s9 := lvm_lemma_Add(lvm_b8, lvm_s8, lvm_sM, speed_value,4,var_8,var_12);
    assert StateNext(lvm_s8,lvm_s9);
    lvm_sMs := lvm_sMs + [lvm_s9];

    assert operandsUnique(lvm_s9,operands);
    assert operands[0] == speed_value && operands[1] == var_10;
    assert OperandContents(lvm_s9,speed_value).Int?;
    assert OperandContents(lvm_s9,speed_value).itype.size == 4;

    ghost var lvm_b10, lvm_s10:= lvm_lemma_Icmp(lvm_b9, lvm_s9, lvm_sM, var_17,ugt,4,speed_value,D(Int(0,IntType(4,false))));
    assert StateNext(lvm_s9,lvm_s10);
    lvm_sMs := lvm_sMs + [lvm_s10];
    assert OperandContents(lvm_s10,var_17).Int?;
    assert !OperandContents(lvm_s10,var_17).itype.signed;
    assert OperandContents(lvm_s10,var_17).itype.size == 1;
    assert OperandContents(lvm_s9,speed_value).val > 0 ==> OperandContents(lvm_s10,var_17).val == 1;

    ghost var lvm_b11, lvm_s11:= lvm_lemma_Ret(lvm_b10, lvm_s10, lvm_sM, speed_value, D(Void));
    assert StateNext(lvm_s10,lvm_s11);
    lvm_sMs := lvm_sMs + [lvm_s11];

    assert lvm_b11 == (lvm_CNil());
    assert eval_code(lvm_Block(lvm_b11), lvm_s10, lvm_sM);
    lvm_sM := lvm_lemma_empty(lvm_s11,lvm_sM);
    assert ValidState(lvm_sM);
    assert StateNext(lvm_s11,lvm_sM);
    lvm_sMs := lvm_sMs + [lvm_sM];
  
  }

}