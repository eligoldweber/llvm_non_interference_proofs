include "../ops.dfy"
include "../types.dfy"

// Contains the following conversion operations: ADD, SUB

module binary_operations_i {
    import opened ops
    import opened types

    function evalADD(size:nat,v0:Data,v1:Data):  (out:Data) // doesnt support nsw/nuw
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        // ensures out.itype.size == size
    { 
        reveal_ToTwosComp();
        reveal_FromTwosComp();
        if (v0.itype.size == 1 && !v0.itype.signed) then UInt8(BitwiseAdd8(DataToUInt8(ToTwosComp(v0)),DataToUInt8(ToTwosComp(v1)))) else 
        if (v0.itype.size == 1 && v0.itype.signed) then FromTwosComp(UInt8(BitwiseAdd8(DataToUInt8(ToTwosComp(v1)),DataToUInt8(ToTwosComp(v0))))) else 
        if (v0.itype.size == 2 && !v0.itype.signed) then UInt16(BitwiseAdd16(DataToUInt16(ToTwosComp(v0)),DataToUInt16(ToTwosComp(v1)))) else 
        if (v0.itype.size == 2 && v0.itype.signed) then FromTwosComp(UInt16(BitwiseAdd16(DataToUInt16(ToTwosComp(v1)),DataToUInt16(ToTwosComp(v0))))) else 
        if (v0.itype.size == 4 && !v0.itype.signed) then UInt32(BitwiseAdd32(DataToUInt32(ToTwosComp(v0)),DataToUInt32(ToTwosComp(v1)))) else 
        if (v0.itype.size == 4 && v0.itype.signed) then FromTwosComp(UInt32(BitwiseAdd32(DataToUInt32(ToTwosComp(v1)),DataToUInt32(ToTwosComp(v0))))) else 
        if (v0.itype.size == 8 && !v0.itype.signed) then UInt64(BitwiseAdd64(DataToUInt64(ToTwosComp(v0)),DataToUInt64(ToTwosComp(v1)))) else 
        if (v0.itype.size == 8 && v0.itype.signed) then FromTwosComp(UInt64(BitwiseAdd64(DataToUInt64(ToTwosComp(v1)),DataToUInt64(ToTwosComp(v0))))) else v0

    }


    function evalSUB(size:nat,v0:Data,v1:Data):  (out:Data) // doesnt support nsw/nuw
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        // ensures out.itype.size == size
        ensures (v0.itype.size == 1 && v0.itype.signed) ==> evalSUB(size,v0,v1)== FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(v1)),DataToUInt8(ToTwosComp(v0)))))
    { 
        reveal_ToTwosComp();
        reveal_FromTwosComp();
        if (v0.itype.size == 1 && !v0.itype.signed) then UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(v0)),DataToUInt8(ToTwosComp(v1)))) else 
        if (v0.itype.size == 1 && v0.itype.signed) then FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(v1)),DataToUInt8(ToTwosComp(v0))))) else 
        if (v0.itype.size == 2 && !v0.itype.signed) then UInt16(BitwiseSub16(DataToUInt16(ToTwosComp(v0)),DataToUInt16(ToTwosComp(v1)))) else 
        if (v0.itype.size == 2 && v0.itype.signed) then FromTwosComp(UInt16(BitwiseSub16(DataToUInt16(ToTwosComp(v1)),DataToUInt16(ToTwosComp(v0))))) else 
        if (v0.itype.size == 4 && !v0.itype.signed) then UInt32(BitwiseSub32(DataToUInt32(ToTwosComp(v0)),DataToUInt32(ToTwosComp(v1)))) else 
        if (v0.itype.size == 4 && v0.itype.signed) then FromTwosComp(UInt32(BitwiseSub32(DataToUInt32(ToTwosComp(v1)),DataToUInt32(ToTwosComp(v0))))) else 
        if (v0.itype.size == 8 && !v0.itype.signed) then UInt64(BitwiseSub64(DataToUInt64(ToTwosComp(v0)),DataToUInt64(ToTwosComp(v1)))) else 
        if (v0.itype.size == 8 && v0.itype.signed) then FromTwosComp(UInt64(BitwiseSub64(DataToUInt64(ToTwosComp(v1)),DataToUInt64(ToTwosComp(v0))))) else v0

    }

//-----------------------------------------------------------------------------
// INSTRICTION VALIDITY
//-----------------------------------------------------------------------------

//-- ADD -- // 
    lemma evalADD8check_unsigned()
    {
        reveal_BitwiseAdd8();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, false) 
                                    ==> evalADD(1,d0,d1).val == (d0.val+d1.val) % Pow256(1);   
    }    
    lemma evalADD16check_unsigned()
    {
        reveal_BitwiseAdd16();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, false) 
                                    ==> evalADD(2,d0,d1).val == (d0.val+d1.val) % Pow256(2);
    }
    lemma evalADD32check_unsigned()
    {
        reveal_BitwiseAdd32();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, false) 
                                    ==> evalADD(4,d0,d1).val == (d0.val+d1.val) % Pow256(4);
    }

        lemma evalADD64check_unsigned()
    {
        reveal_BitwiseAdd64(); 
        reveal_ToTwosComp();    
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, false) 
                                    ==> evalADD(8,d0,d1).val == (d0.val+d1.val) % Pow256(8);
    }

    lemma evalADD8check_signed()
    {
        reveal_BitwiseAdd8();
        reveal_ToTwosComp();
        reveal_FromTwosComp();
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, true) 
                                    ==> evalADD(1,d0,d1).val == FromTwosComp(evalADD(1,ToTwosComp(d0),ToTwosComp(d1))).val;   
    }
    lemma evalADD16check_signed()
    {
        reveal_BitwiseAdd16();
        reveal_ToTwosComp();
        reveal_FromTwosComp();
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, true) 
                                    ==> evalADD(2,d0,d1).val == FromTwosComp(evalADD(2,ToTwosComp(d0),ToTwosComp(d1))).val;   
    }
    lemma evalADD32check_signed()
    {
        reveal_BitwiseAdd32();
        reveal_ToTwosComp();
        reveal_FromTwosComp();
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, true) 
                                    ==> evalADD(4,d0,d1).val == FromTwosComp(evalADD(4,ToTwosComp(d0),ToTwosComp(d1))).val;   
    } 
    lemma evalADD64check_signed()
    {
        reveal_BitwiseAdd64();
        reveal_ToTwosComp();
        reveal_FromTwosComp();
      
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, true) 
                                    ==> evalADD(8,d0,d1).val == FromTwosComp(evalADD(8,ToTwosComp(d0),ToTwosComp(d1))).val;   
    } 

// -- SUB -- //
lemma evalSUB8check_unsigned()
    {
        reveal_BitwiseSub8();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, false) 
                                    ==> evalSUB(1,d0,d1).val == (d0.val-d1.val) % Pow256(1);   
    }
lemma evalSUB16check_unsigned()
    {
        reveal_BitwiseSub16();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(2, false) 
                                    ==> evalSUB(2,d0,d1).val == (d0.val-d1.val) % Pow256(2);   
    }
lemma evalSUB32check_unsigned()
    {
        reveal_BitwiseSub32();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(4, false) 
                                    ==> evalSUB(4,d0,d1).val == (d0.val-d1.val) % Pow256(4);   
    }
lemma evalSUB64check_unsigned()
    {
        reveal_BitwiseSub64();
        reveal_ToTwosComp();
        assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(8, false) 
                                    ==> evalSUB(8,d0,d1).val == (d0.val-d1.val) % Pow256(8);   
    }
lemma evalSUB8check_signed()
    {
        reveal_BitwiseSub8();
        reveal_ToTwosComp();
        reveal_FromTwosComp();
      
        var v2:sint8 := 2;
        var v3:sint8 := -50;
        assert SInt8(v2).itype.size == 1 && SInt8(v2).itype.signed;
        assert FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))).val == 52;
        assert evalSUB(1,SInt8(v2),SInt8(v3)).val == -52;
        
        assert -evalSUB(1,SInt8(v2),SInt8(v3)).val == FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))).val;
        // assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, true) 
                                    // ==> evalSUB(1,d0,d1).val == FromTwosComp(evalSUB(1,ToTwosComp(d0),ToTwosComp(d1))).val;   
    }   
}