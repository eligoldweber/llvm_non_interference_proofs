include "llvm.i.dfy"

module insCheck {
    import opened LLVM_def

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
// lemma evalSUB8check_signed()
//     {
//         reveal_BitwiseSub8();
//         reveal_ToTwosComp();
//         reveal_FromTwosComp();
      
//         var v2:sint8 := 2;
//         var v3:sint8 := -50;
//         assert SInt8(v2).itype.size == 1 && SInt8(v2).itype.signed;
//         assert FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))).itype.signed;
//         assert FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))).itype.size == 1;
//         assert FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))).val == 52;
//         // assert FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3)))))) == evalSUB(1,SInt8(v2),SInt8(v3));
//         assert (UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v3))),DataToUInt8(ToTwosComp(SInt8(v2)))))).val == 204;
//         assert UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v2))),DataToUInt8(ToTwosComp(SInt8(v3))))).val == 52;
//         var t:uint8 := 204;
//         assert FromTwosComp(UInt8(t)).val == -52;
//         // assert SInt8(v3).itype.size == 1 && SInt8(v3).itype.signed && evalSUB(1,SInt8(v3),SInt8(v2)) == FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(SInt8(v3))),DataToUInt8(ToTwosComp(SInt8(v2))))));
//         // assert forall d0,d1:Data :: isInt(d0) && isInt(d1) && typesMatch(d0,d1) && d0.itype == IntType(1, true) 
//                                     // ==> evalSUB(1,d0,d1).val == FromTwosComp(evalSUB(1,ToTwosComp(d0),ToTwosComp(d1))).val;   
//     }    


// -- ICMP -- // 
    lemma evalICMPcheck()
    {
        reveal_ToTwosComp();
        reveal_FromTwosComp();
        //<result> = icmp eq i32 4, 5          ; yields: result=false
        var v0:sint32 := 4;
        var v1:sint32 := 5;
        assert evalICMP(eq,4,SInt32(v0),SInt32(v1)).val == 0;
        // <result> = icmp ult i16  4, 5        ; yields: result=true
        var v2:uint16 := 4;
        var v3:uint16 := 5;
        assert evalICMP(ult,2,SInt16(v2),SInt16(v3)).val == 1;
        // <result> = icmp sgt i16  4, 5        ; yields: result=false
        var v4:sint16 := 4;
        var v5:sint16 := 5;
        assert evalICMP(sgt,2,SInt16(v4),SInt16(v5)).val == 0;
        // <result> = icmp ule i16 -4, 5        ; yields: result=false
        var v6:sint16 := -4;
        var v7:sint16 := 5;
        assert evalICMP(ule,2,SInt16(v6),SInt16(v7)).val == 0;
        assert  evalICMP(sle,2,SInt16(v6),SInt16(v7)).val == 1;
        // <result> = icmp sge i16  4, 5        ; yields: result=false
        var v8:sint16 := 4;
        var v9:sint16 := 5;
        assert evalICMP(sge,2,SInt16(v8),SInt16(v9)).val == 0;
        
    }    

}

// var v0:sint8 := -4;
//         var v1:sint8 := 5;

//         assert evalADD(1,SInt8(v0),SInt8(v1)).val == 1;

//         var v2:sint8 := 127;
//         var v3:sint8 := 2;
//         assert evalADD(1,SInt8(v2),SInt8(v3)).val == (127+2) % Pow128(1);


//         v2 := -50;
//         v3 := 2;
//         var r:uint8 := 208;
//         assert SInt8(v2).val == -50;
//         assert  (v2+v3) == -48;
//         assert ToTwosComp(SInt8(v2)).val +  ToTwosComp(SInt8(v3)).val == 208;
//         assert FromTwosComp(UInt8(r)).val == -48;
//         assert FromTwosComp(evalADD(1,ToTwosComp(SInt8(v2)),ToTwosComp(SInt8(v3)))).val == -48;
//         assert evalADD(1,SInt8(v2),SInt8(v3)).val == -48;