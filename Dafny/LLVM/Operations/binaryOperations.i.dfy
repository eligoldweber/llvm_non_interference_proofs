include "../ops.dfy"
include "../types.dfy"
include "binaryOperationsHelper.i.dfy"

// Contains the following conversion operations: ADD, SUB

module binary_operations_i {
    import opened ops
    import opened types
    import opened binary_operations_helper_i

    function evalADD(size:nat,v0:Data,v1:Data):  (out:Data) // doesnt support nsw/nuw
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == size
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures out.itype.size == size
        ensures !out.itype.signed
        ensures typesMatch(v0,v1)
        ensures ToTwosComp(out).val == (v0.val + v1.val) % Pow256(v0.itype.size)
    { 
        if (v0.itype.size == 1) then evalADD8(size,v0,v1) else
        if (v0.itype.size == 2) then evalADD16(size,v0,v1) else
        if (v0.itype.size == 4) then evalADD32(size,v0,v1) else
                                     assert v0.itype.size == 8; 
                                     evalADD64(size,v0,v1)
    }


 // SUB // 
    function evalSUB(size:nat,v0:Data,v1:Data):  (out:Data) // doesnt support nsw/nuw
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == size
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures out.itype.size == size
        ensures ToTwosComp(out).val == (v0.val - v1.val) % Pow256(v0.itype.size)

    { 
        
        if (v0.itype.size == 1) then evalSUB8(size,v0,v1) else
        if (v0.itype.size == 2) then evalSUB16(size,v0,v1) else
        if (v0.itype.size == 4) then evalSUB32(size,v0,v1) else
                                     assert v0.itype.size == 8; 
                                     evalSUB64(size,v0,v1)

    }

    


// //-----------------------------------------------------------------------------
// // INSTRUCTION VALIDITY
// //-----------------------------------------------------------------------------

//-- ADD -- // 
    lemma evalADD8check_unsigned()
    {
        reveal_BitwiseAdd8();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, false) 
                                    ==> evalADD(1,d0,d1).val == (d0.val+d1.val) % Pow256(1);   
    }    
    lemma evalADD16check_unsigned()
    {
        reveal_BitwiseAdd16();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, false) 
                                    ==> evalADD(2,d0,d1).val == (d0.val+d1.val) % Pow256(2);
    }
    lemma evalADD32check_unsigned()
    {
        reveal_BitwiseAdd32();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, false) 
                                    ==> evalADD(4,d0,d1).val == (d0.val+d1.val) % Pow256(4);
    }

        lemma evalADD64check_unsigned()
    {
        reveal_BitwiseAdd64(); 
            
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, false) 
                                    ==> evalADD(8,d0,d1).val == (d0.val+d1.val) % Pow256(8);
    }

    lemma evalADD8check_signed()
    {
        reveal_BitwiseAdd8();
        
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, true) 
                                    ==> ToTwosComp(evalADD(1,d0,d1)).val == (d0.val+d1.val) % Pow256(1);   
    }
    lemma evalADD16check_signed()
    {
        reveal_BitwiseAdd16();
        
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, true) 
                                    ==> ToTwosComp(evalADD(2,d0,d1)).val == (d0.val+d1.val) % Pow256(2);    
    }
    lemma evalADD32check_signed()
    {
        reveal_BitwiseAdd32();
        
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, true) 
                                    ==> ToTwosComp(evalADD(4,d0,d1)).val == (d0.val+d1.val) % Pow256(4);    
    } 
    lemma evalADD64check_signed()
    {
        reveal_BitwiseAdd64();
        
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, true) 
                                    ==> ToTwosComp(evalADD(8,d0,d1)).val == (d0.val+d1.val) % Pow256(8);   
    } 

// // -- SUB -- //
lemma evalSUB8check_unsigned()
    {
        reveal_BitwiseSub8();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, false) 
                                    ==> evalSUB(1,d0,d1).val == (d0.val-d1.val) % Pow256(1);   
    }
lemma evalSUB16check_unsigned()
    {
        reveal_BitwiseSub16();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, false) 
                                    ==> evalSUB(2,d0,d1).val == (d0.val-d1.val) % Pow256(2);   
    }
lemma evalSUB32check_unsigned()
    {
        reveal_BitwiseSub32();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, false) 
                                    ==> evalSUB(4,d0,d1).val == (d0.val-d1.val) % Pow256(4);   
    }
lemma evalSUB64check_unsigned()
    {
        reveal_BitwiseSub64();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, false) 
                                    ==> evalSUB(8,d0,d1).val == (d0.val-d1.val) % Pow256(8);   
    }

lemma evalSUB8check_signed()
    {
        reveal_BitwiseSub8();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, false) 
                                    ==> ToTwosComp(evalSUB(1,d0,d1)).val == (d0.val-d1.val) % Pow256(1);   
    }
lemma evalSUB16check_signed()
    {
        reveal_BitwiseSub16();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, false) 
                                    ==> ToTwosComp(evalSUB(2,d0,d1)).val == (d0.val-d1.val) % Pow256(2);   
    }
lemma evalSUB32check_signed()
    {
        reveal_BitwiseSub32();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, false) 
                                    ==> ToTwosComp(evalSUB(4,d0,d1)).val == (d0.val-d1.val) % Pow256(4);   
    }
lemma evalSUB64check_signed()
    {
        reveal_BitwiseSub64();
        
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, false) 
                                    ==> ToTwosComp(evalSUB(8,d0,d1)).val == (d0.val-d1.val) % Pow256(8);   
    }
 
}