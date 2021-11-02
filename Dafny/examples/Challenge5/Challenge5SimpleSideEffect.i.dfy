include "../../LLVM/llvm.i.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/generalInstructionsBehavior.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/memory.i.dfy"
include "../../LLVM/Operations/otherOperations.i.dfy"
include "../../AbstractNonInterferenceProof.s.dfy"
include "./Challenge5Code.s.dfy"
include "./Challenge5_HelperLemmas.i.dfy"
include "../../LLVM/control_flow.i.dfy"

module challenge5SideEffects{ 
    import opened LLVM_def
    import opened control_flow
    import opened challenge5Code
    import opened challenge5_helpful_lemmas
    import opened general_instructions_behaviors
    import opened types
    import opened memory
    import opened other_operations_i


     predicate preConds(codes:lvm_codes, s:lvm_state, s':lvm_state){
        
        && lvm_require(codes,challenge_prob_5_code_write_encrypted_simple_side_effect(),s,s')
        && codes.lvm_Codes?
        && codes.tl.CNil?
        && ValidState(s)
        && challengeStateAssumptionsPred(s)
    }

    lemma challengeProb5PatchBehavior(codes:lvm_codes, s:lvm_state) 
        returns (postB:behavior)
        requires exists s' :: preConds(codes,s,s');

        ensures ValidBehaviorNonTrivial(postB);
        
        // By ensuring !RemovedBehaviors(b), this lemma shows that postB does not contain any 'bad' behavior; ie(encrypt has additonal side effects )
        ensures !RemovedBehaviors(postB); // This proof should fail - this post condition is not maintained

    {
        postB := [s];
        
        var fullCode := challenge_prob_5_code_write_encrypted_simple_side_effect();
        var s' :|  lvm_require(codes, fullCode, s, s');
        
        assert s.ok;
        assert codes.hd.Block?;
        assert evalBlock(codes, s, s');
        var r:state :| evalCode(codes.hd, s, r) && evalBlock(codes.tl, r, s') ;
        var tail := codes.tl;
 
        var codeBlock:lvm_codes := lvm_get_block(codes.hd);
        var call := D(Ptr(0,0,0,1));

        var bytes_written :| ValidOperand(s,bytes_written) && ValidState(s) && bytes_written.D? && D(Ptr(0,0,0,1)) == bytes_written;
        assert codeBlock.hd == Ins(CALL(call,malloc(Int(0,IntType(8,false)))));
        assert codeBlock.tl.lvm_Codes?;


        var updatedB:behavior, unwrapedCode:lvm_codes, nextState:state := malloc_(postB, codeBlock, call, Int(0,IntType(8,false)), s');
        assert updatedB[0] == s;

        // assert AllocaStep(s.m,4) == nextState.m;
        assert StateNext(s,nextState);
        assert unwrapedCode == codeBlock.tl;
        assert nextState == bls(updatedB);
        var currState := nextState;

        var mblock := D(Ptr(0,0,0,1));
        assert unwrapedCode.hd == Ins(LLVM_MEMCPY(call,mblock,1,false));
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 2;

        updatedB, unwrapedCode, nextState := lvm_lemma_MemCpy(updatedB, unwrapedCode, r, call, mblock,1);

         var call1 := D(Ptr(0,0,0,1));
        assert StateNext(currState,nextState);
        currState := nextState;
        assert unwrapedCode.hd == Ins(CALL(call1,malloc(call1.d)));
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 3;

        updatedB, unwrapedCode, nextState := malloc_(updatedB, unwrapedCode, call1, Int(0,IntType(8,false)), s');
        var IV_SIZE := D(Int(16,IntType(4,false)));
        var KEY := D(Int(16,IntType(4,false)));
        var cipherText := D(Ptr(0,0,0,1));
        var call2 := D(Int(0,IntType(1,false)));

       assert unwrapedCode.hd == Ins(CALL(call2,encrypt_side_effects(call,4,KEY,IV_SIZE,cipherText)));

        currState := nextState;
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 4;
        var oldCode := unwrapedCode;
        updatedB, unwrapedCode, nextState := encryptSideEffect_(updatedB, unwrapedCode, call2,call,4,KEY,IV_SIZE,cipherText, s');

        assert unwrapedCode.hd == Ins(STORE(call2,bytes_written));
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 7;
        assert ValidState(bls(updatedB));
        assert (nextState.ok ==> evalCode_lax(oldCode.hd, currState, nextState));
        assert  lvm_ensure(oldCode, unwrapedCode, currState, nextState, s');

        assert evalCode_lax(lvm_Block(unwrapedCode), nextState, s');

        // assert evalCode(lvm_Block(unwrapedCode), (bls(updatedB)), s');
        updatedB, unwrapedCode, nextState := lvm_lemma_Store(updatedB, unwrapedCode, r, call2, bytes_written);
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 8;
        
        var call3 := D(Int(1,IntType(4,false)));
        assert unwrapedCode.hd == Ins(CALL(call3,fwrite(bytes_written,4,1,D(Ptr(0,0,0,1)))));
        
        updatedB, unwrapedCode, nextState := fwrite_(updatedB, unwrapedCode, call3, bytes_written,4,1,D(Ptr(0,0,0,1)),s');
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 9;
        var cmp := D(Int(0,IntType(1,false)));

        assert unwrapedCode.hd == Ins(ICMP(cmp,eq,4,call3,D(Int(0,IntType(4,false)))));
        updatedB, unwrapedCode, nextState := lvm_lemma_Icmp(updatedB, unwrapedCode, s', cmp, eq,4,call3,D(Int(0,IntType(4,false))));
        assert ValidBehavior(updatedB); 
        assert |updatedB| == 10;
        
        assert nextState == s';
        assert unwrapedCode == lvm_CNil(); 
        assert updatedB[0] == s;
        assert updatedB[|updatedB|-1] == s';
        assert BehaviorEvalsCode(codes.hd,updatedB);
        // assert !RemovedBehaviors(updatedB);
        
        postB := updatedB;
    }

    // Describes/Excludes 'bad' behaviors in the Unpatched Code (ie preBehaviors)
        predicate RemovedBehaviors(b:behavior)
    {
        exists i,j :: && i in b
                      && j in b 
                      && (forall plainText:operand,size:nat,KEY:operand,IV:operand,cipherText:operand :: evalBlock(encrypt_side_effects(plainText,size,KEY,IV,cipherText),i,j)) 
                      && !stateFramingMultiValue(i,j)
    }

    
       predicate stateFramingMultiValue(s:state,s':state)
    {

        challengeStateAssumptions(s);
        var cipherText :| ValidOperand(s,cipherText) && ValidState(s);
        var bytes_written :| ValidOperand(s,bytes_written) && ValidState(s);
        var ops := {OperandContents(s,cipherText),OperandContents(s,bytes_written)};


        ValidState(s)
        && ValidState(s')
        && forall op :: op in ops ==> 
            (&& ValidData(s,op)
            && ValidData(s',op)
            && s.ok == s'.ok
            && (forall lv :: (lv in s.lvs && !(s.lvs[lv] in ops)) ==> (lv in s'.lvs && s.lvs[lv] == s'.lvs[lv]))//(lv in s'.lv && s.lv[op] == s'.lv[op])
            && (forall gv :: (gv in s.gvs && !(s.gvs[gv] in ops)) ==> (gv in s'.gvs && s.gvs[gv] == s'.gvs[gv]))
            && (forall o:operand :: (o.D? && ValidOperand(s,o) && ValidOperand(s',o) && !(OperandContents(s,o) in ops) ) ==> (OperandContents(s,o) == OperandContents(s',o)))
            && s.m == s'.m)
    }




}
