include "../../LLVM/llvm.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "./Challenge5Code.s.dfy"
include "../../LLVM/memory.i.dfy"


module challenge5_helpful_lemmas{
    import opened challenge5Code
    import opened control_flow
    import opened LLVM_def
    import opened types
    import opened memory



    predicate stateFraming(s:state,s':state,op:operand)
    {
        ValidState(s)
        && ValidState(s')
        && ValidOperand(s,op)
        && ValidOperand(s',op)
        && s.ok == s'.ok
        && op.LV? ==> (forall lv :: (lv in s.lvs && lv != op.l) ==> (lv in s'.lvs && s.lvs[lv] == s'.lvs[lv]))//(lv in s'.lv && s.lv[op] == s'.lv[op])
        && op.GV? ==> (forall gv :: (gv in s.gvs && gv != op.g) ==> (gv in s'.gvs && s.gvs[gv] == s'.gvs[gv]))//(lv in s'.lv && s.lv[op] == s'.lv[op])
        && s.m == s'.m
    }


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

        // requires codes == malloc(ptr);
        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

        // requires exists s' :: lvm_require(codes,malloc(ptr),s,s');
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
        // lvm_bM := codes.tl;
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

        // requires codes == malloc(ptr);
        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

        // requires exists s' :: lvm_require(codes,malloc(ptr),s,s');
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
        // lvm_bM := codes.tl;
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

        // requires codes == malloc(ptr);
        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

        // requires exists s' :: lvm_require(codes,malloc(ptr),s,s');
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
        // lvm_bM := codes.tl;
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

        // requires codes == malloc(ptr);
        ensures ValidBehaviorNonTrivial(b');
        ensures StateNext(bls(b),s')
        ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
        ensures |b'| == |b| + 1;
        ensures bls(b') == s';
        ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

        // requires exists s' :: lvm_require(codes,malloc(ptr),s,s');
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
        // lvm_bM := codes.tl;
        assert evalIns(codes.hd.ins,bls(b),s');

        assert NextStep(s,s',Step.stutterStep());
        assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
        assert StateNext(s,s');
        b' := b + [s'];
        assert ValidBehaviorNonTrivial(b');
    }


    // lemma encrypt_side_effects_(b:behavior,codes:lvm_codes, ptr:operand ,plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand,sN:lvm_state) 
    //     returns (b':behavior,lvm_bM:lvm_codes, s':lvm_state)
        
    //     requires ValidBehaviorNonTrivial(b);
    //     requires lvm_require(codes, Ins(CALL(ptr,encrypt_side_effects(plainText,size,KEY,IV,cipherText))), bls(b), sN)
    //     requires ValidState(bls(b));
    //     requires ValidOperand(bls(b),ptr);
    //     requires challengeStateAssumptionsPred(bls(b));

    //     // requires codes == malloc(ptr);
    //     ensures ValidBehaviorNonTrivial(b');
    //     ensures StateNext(bls(b),s')
    //     ensures  lvm_ensure(codes, lvm_bM, bls(b), s', sN);
    //     ensures |b'| == |b| + 1;
    //     ensures bls(b') == s';
    //     ensures forall i :: i >=0 && i < |b| ==> b[i] == b'[i];

    //     // requires exists s' :: lvm_require(codes,malloc(ptr),s,s');
    // {
    //     var s := bls(b);
    //     assert encrypt_side_effects(plainText,size,KEY,IV,cipherText) == lvm_Codes(Ins(RET(D(Void))),lvm_CNil())  ;
    //     assert codes.hd == Ins(CALL(ptr,encrypt_side_effects(plainText,size,KEY,IV,cipherText)));
    //     assert ValidOperand(s,ptr);
    //     assert !codes.hd.ins.fnc.CNil?;
    //     assert ValidInstruction(s, codes.hd.ins);

    //     // assert forall s' :: evalIns(codes.hd.ins,bls(b),s') ==> bls(b) == s';
    //     s' :| evalIns(codes.hd.ins,bls(b),s');
    //     lvm_bM := codes.tl;

    //     ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block(codes, s, sN);
    //     var lvm_sM := lvm_ltmp1;
    //     var lvm_bMs := lvm_ltmp2;
    //     assert ValidState(s);
    //     assert ValidState(lvm_sM);
    //     assert lvm_sM == s;
    //     assert codes.tl == lvm_bMs;
    //     // lvm_bM := codes.tl;
    //     assert evalIns(codes.hd.ins,bls(b),s');

    //     assert NextStep(s,s',Step.stutterStep());
    //     assert MemStateNext(s.m,s'.m,MemStep.stutterStep());
    //     assert StateNext(s,s');
    //     b' := b + [s'];
    //     assert ValidBehaviorNonTrivial(b');
    // }



}