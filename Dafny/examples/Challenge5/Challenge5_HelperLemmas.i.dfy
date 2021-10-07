include "../../LLVM/llvm.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "./Challenge5Code.s.dfy"
include "../../LLVM/memory.i.dfy"
include "../../LLVM/generalInstructionsBehavior.i.dfy"


module challenge5_helpful_lemmas{
    import opened challenge5Code
    import opened control_flow
    import opened LLVM_def
    import opened types
    import opened memory
    import opened general_instructions_behaviors


lemma {:axiom} challengeStateAssumptions(s:state)
    ensures exists cipherText:operand :: ValidOperand(s,cipherText) && ValidState(s)
    ensures exists bytes_written:operand :: ValidOperand(s,bytes_written) && ValidState(s) && bytes_written.D? && D(Ptr(0,0,0,1)) == bytes_written

predicate challengeStateAssumptionsPred(s:state)
    {
        challengeStateAssumptions(s);
        && (exists cipherText:operand :: ValidOperand(s,cipherText) && ValidState(s))
        && (exists bytes_written:operand :: ValidOperand(s,bytes_written) && ValidState(s)&& bytes_written.D?&& D(Ptr(0,0,0,1)) == bytes_written)
    }

lemma malloc_(b:behavior,codes:lvm_codes, ptr:operand,size:Data ,sN:lvm_state) 
        returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
        requires ValidBehaviorNonTrivial(b);
        requires lvm_require(codes, Ins(CALL(ptr,malloc(size))), bls(b), sN)
        requires ValidState(bls(b));
        requires ValidOperand(bls(b),ptr);
        requires challengeStateAssumptionsPred(bls(b));

        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];
    {
        var s := bls(b);
        assert malloc(size) == ForeignFunction;
        assert codes.hd == Ins(CALL(ptr,malloc(size)));
        assert ValidOperand(s,ptr);
        assert !codes.hd.ins.fnc.CNil?;
        assert ValidInstruction(s, codes.hd.ins);

        assert forall s' :: evalIns(codes.hd.ins,bls(b),s') ==> bls(b) == s';
        s' := s;
        lvm_bM := codes.tl;

        ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
        var lvm_sM := lvm_ltmp1;
        var lvm_bMs := lvm_ltmp2;
        assert ValidState(s);
        assert ValidState(lvm_sM);
        assert lvm_sM == s;
        assert codes.tl == lvm_bMs;

        assert evalIns(codes.hd.ins,bls(b),s');
        assert NextStep(s,s',Step.stutterStep());
        assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
        assert StateNext(s,s');
        b' := b + [s'];
        assert ValidBehaviorNonTrivial(b');
    }


    lemma encryptEmpty_(b:behavior,codes:lvm_codes, ptr:operand ,sN:lvm_state) 
        returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
        requires ValidBehaviorNonTrivial(b);
        requires lvm_require(codes, Ins(CALL(ptr,encryptEmpty())), bls(b), sN)
        requires ValidState(bls(b));
        requires ValidOperand(bls(b),ptr);
        requires challengeStateAssumptionsPred(bls(b));

        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];
    {
        var s := bls(b);
        assert encryptEmpty() == ForeignFunction;
        assert codes.hd == Ins(CALL(ptr,encryptEmpty()));
        assert ValidOperand(s,ptr);
        assert !codes.hd.ins.fnc.CNil?;
        assert ValidInstruction(s, codes.hd.ins);

        assert forall s' :: evalIns(codes.hd.ins,bls(b),s') ==> bls(b) == s';
        s' := s;
        lvm_bM := codes.tl;

        ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
        var lvm_sM := lvm_ltmp1;
        var lvm_bMs := lvm_ltmp2;
        assert ValidState(s);
        assert ValidState(lvm_sM);
        assert lvm_sM == s;
        assert codes.tl == lvm_bMs;
        assert evalIns(codes.hd.ins,bls(b),s');

        assert NextStep(s,s',Step.stutterStep());
        assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
        assert StateNext(s,s');
        b' := b + [s'];
        assert ValidBehaviorNonTrivial(b');
    }

    lemma fwrite_(b:behavior,codes:lvm_codes, dst:operand, ptr:operand, size:nat, cnt:nat, file:operand ,sN:lvm_state) 
        returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
        requires ValidBehaviorNonTrivial(b);
        requires lvm_require(codes, Ins(CALL(dst,fwrite(ptr,size,cnt,file))), bls(b), sN)
        requires ValidState(bls(b));
        requires ValidOperand(bls(b),dst);
        requires challengeStateAssumptionsPred(bls(b));

        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

    {
        var s := bls(b);
        assert encryptEmpty() == ForeignFunction;
        assert codes.hd == Ins(CALL(dst,fwrite(ptr,size,cnt,file)));
        assert ValidOperand(s,dst);
        assert !codes.hd.ins.fnc.CNil?;
        assert ValidInstruction(s, codes.hd.ins);

        assert forall s' :: evalIns(codes.hd.ins,bls(b),s') ==> bls(b) == s';
        s' := s;
        lvm_bM := codes.tl;

        ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
        var lvm_sM := lvm_ltmp1;
        var lvm_bMs := lvm_ltmp2;
        assert ValidState(s);
        assert ValidState(lvm_sM);
        assert lvm_sM == s;
        assert codes.tl == lvm_bMs;
        assert evalIns(codes.hd.ins,bls(b),s');

        assert NextStep(s,s',Step.stutterStep());
        assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
        assert StateNext(s,s');
        b' := b + [s'];
        assert ValidBehaviorNonTrivial(b');
    }


lemma encrypt_(b:behavior,codes:lvm_codes, ptr:operand ,plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand,sN:lvm_state) 
        returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
        requires ValidBehaviorNonTrivial(b);
        requires lvm_require(codes, Ins(CALL(ptr,encrypt(plainText,size,KEY,IV,cipherText))), bls(b), sN)
        requires ValidState(bls(b));
        requires ValidOperand(bls(b),ptr);
        requires challengeStateAssumptionsPred(bls(b));

        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

    {
        var s := bls(b);
        assert encrypt(plainText,size,KEY,IV,cipherText) == ForeignFunction;
        assert codes.hd == Ins(CALL(ptr,encrypt(plainText,size,KEY,IV,cipherText)));
        assert ValidOperand(s,ptr);
        assert !codes.hd.ins.fnc.CNil?;
        assert ValidInstruction(s, codes.hd.ins);

        assert forall s' :: evalIns(codes.hd.ins,bls(b),s') ==> bls(b) == s';
        s' := s;
        lvm_bM := codes.tl;

        ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
        var lvm_sM := lvm_ltmp1;
        var lvm_bMs := lvm_ltmp2;
        assert ValidState(s);
        assert ValidState(lvm_sM);
        assert lvm_sM == s;
        assert codes.tl == lvm_bMs;
        assert evalIns(codes.hd.ins,bls(b),s');

        assert NextStep(s,s',Step.stutterStep());
        assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
        assert StateNext(s,s');
        b' := b + [s'];
        assert ValidBehaviorNonTrivial(b');
    }

    lemma encryptSideEffect_(b:behavior,codes:lvm_codes, ptr:operand ,plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand,sN:lvm_state) 
        returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
        requires ValidBehaviorNonTrivial(b);
        requires lvm_require(codes, Ins(CALL(ptr,encrypt_side_effects(plainText,size,KEY,IV,cipherText))), bls(b), sN)
        requires ValidState(bls(b));
        requires ValidOperand(bls(b),ptr);
        requires challengeStateAssumptionsPred(bls(b));


        requires ValidOperand(bls(b),plainText)
        requires ValidOperand(bls(b),cipherText)
        requires MemValid(bls(b).m)
        requires OperandContents(bls(b),plainText).Ptr?
        requires OperandContents(bls(b),cipherText).Ptr?
        requires OperandContents(bls(b),plainText).size >= OperandContents(bls(b),cipherText).size;
        requires validBitWidth(size)

        ensures ValidBehaviorNonTrivial(b');
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 3;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];
    {
        var s := bls(b);
        assert codes.hd == Ins(CALL(ptr,encrypt_side_effects(plainText,size,KEY,IV,cipherText)));
        assert ValidOperand(s,ptr);
        assert !codes.hd.ins.fnc.CNil?;
        assert ValidInstruction(s, codes.hd.ins);
        assert codes.hd.ins.fnc == lvm_Codes(Ins(LLVM_MEMCPY(plainText,cipherText,1,false)),encrypt(plainText,size,KEY,IV,cipherText));   
                  
        assert evalIns(codes.hd.ins,s,sN) ==> evalBlock(codes.hd.ins.fnc,s,sN);
        assert evalCode_lax(lvm_Block(codes), s, sN);
    
        lvm_bM := codes.tl;

        ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
        var lvm_sM := lvm_ltmp1;
        var lvm_bMs := lvm_ltmp2;
        assert ValidState(s);
        assert ValidState(lvm_sM);

        assert codes.tl == lvm_bMs;
        assert evalIns(Ins(CALL(ptr,encrypt_side_effects(plainText,size,KEY,IV,cipherText))).ins,s,lvm_sM);
        assert evalBlock(codes.hd.ins.fnc,s,lvm_sM);
        var sidesB := encrypt_side_effects_behavior(codes.hd.ins.fnc,s,plainText,size,KEY,IV,cipherText,lvm_sM);
        assert bls(b) == sidesB[0];

        b' := b + sidesB;
        assert NextStep(bls(b),sidesB[0],Step.stutterStep());
        assert MemStateNext(bls(b).m,sidesB[0].m,MemStep.stutterStep());
        assert StateNext(bls(b),sidesB[0]);
        assert ValidBehaviorNonTrivial(b');
        assert lvm_sM == bls(b');
        s' := lvm_sM;

    }




lemma encrypt_side_effects_behavior(codes:lvm_codes, s:lvm_state ,plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand,sN:lvm_state) 
        returns (postB:behavior)
        
        requires codes == encrypt_side_effects(plainText,size,KEY,IV,cipherText);
        requires evalBlock(encrypt_side_effects(plainText,size,KEY,IV,cipherText),s,sN);
        requires codes.lvm_Codes?
        requires ValidState(s)
        
        requires ValidOperand(s,plainText)
        requires ValidOperand(s,cipherText)
        requires MemValid(s.m)
        requires OperandContents(s,plainText).Ptr?
        requires OperandContents(s,cipherText).Ptr?
        requires OperandContents(s,plainText).size >= OperandContents(s,cipherText).size;
        requires validBitWidth(size)

        ensures ValidBehaviorNonTrivial(postB);
        ensures BehaviorEvalsCode(codes.hd,postB);
        ensures |postB| == 3;
        ensures postB[0] == s;
        ensures bls(postB) == sN;


    {
        postB := [s];
        var fullCode := encrypt_side_effects(plainText,size,KEY,IV,cipherText);
                   
        var s' := sN;
        assert s.ok;
        assert evalBlock(codes, s, s');
        var codeBlock:lvm_codes := codes;
        var r:state :| evalCode(codes.hd, s, r) && evalBlock(codes.tl, r, s') ;
        assert r == s';
        assert codeBlock.hd == Ins(LLVM_MEMCPY(plainText,cipherText,1,false));

        var updatedB, unwrapedCode, nextState := lvm_lemma_MemCpy(postB, codeBlock, r, plainText, cipherText,1);
        assert |updatedB| == 2;

        assert StateNext(s,nextState);
        var currState := nextState;
        assert unwrapedCode == encrypt(plainText,size,KEY,IV,cipherText);
        assert ValidBehavior(updatedB); 
        assert forall s'' :: evalBlock(unwrapedCode,currState,s'') ==> currState == s'';
        var s'' := currState;
        updatedB := updatedB + [s''];
        assert NextStep(currState,s'',Step.stutterStep());
        assert MemStateNext(currState.m,s''.m,MemStep.stutterStep());
        assert StateNext(currState,s'');
        assert ValidBehavior(updatedB); 
        assert BehaviorEvalsCode(codes.hd,updatedB);
        assert bls(updatedB) == r;
        postB := updatedB;
        assert |updatedB| == 3;
    }

}