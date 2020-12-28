include "ops.dfy"
include "types.dfy"
include "conversionOperations.i.dfy"

// Contains the following bitwise binary operations: LSHL, AND, OR
module bitwise_binary_operations_i {
    import opened ops
    import opened types
    import opened conversion_operations_i

    // TODO: REWRITE WITH BINOPS
     function evalLSHR(op1:Data,op2:Data): (out:Data) // still wip
        requires isInt(op1) && isInt(op2)
        requires op1.itype.size*8 > op2.val //See note above
        requires op2.val > 0
        ensures out.Int?;
        ensures out.itype.size == op1.itype.size && !out.itype.signed;
     {
        reveal_IntFits();
        reveal_rightShift();
        var initial := if op1.itype.signed then ToTwosComp(op1).val else op1.val;
        var result := rightShift(initial,op2.val);
        ValToData(result,op1.itype.size,false)

     }
    function {:opaque} rightShift(val:int,shift:int) : (result:int)
        requires shift >= 1
        requires val >= 0
        ensures result <= val
        ensures result >= 0
        decreases shift
    {
        var r:real := (val/2) as real;
        if shift == 1 then r.Floor
        else  rightShift(r.Floor,shift-1)
    }

    function evalAND(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
        requires isInt(op1) && isInt(op2)
        requires typesMatch(op1,op2)
        requires dstSize == op1.itype.size
        ensures out.Int?;
        ensures out.itype.size == dstSize && !out.itype.signed;
    {
        reveal_BitAnd();
        reveal_BitsToWord();
        reveal_WordToBits();
        if dstSize == 1 then evalAND8(dstSize,op1,op2) else 
        if dstSize == 2 then evalAND16(dstSize,op1,op2) else 
        if dstSize == 4 then evalAND32(dstSize,op1,op2) else 
        evalAND64(dstSize,op1,op2) 

    }

    function evalOR(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
        requires isInt(op1) && isInt(op2)
        requires typesMatch(op1,op2)
        requires dstSize == op1.itype.size
        ensures out.Int?
        ensures out.itype.size == dstSize && !out.itype.signed
    {
        reveal_BitOr();
        reveal_BitsToWord();
        reveal_WordToBits();
        if dstSize == 1 then evalOR8(dstSize,op1,op2) else 
        if dstSize == 2 then evalOR16(dstSize,op1,op2) else 
        if dstSize == 4 then evalOR32(dstSize,op1,op2) else 
        evalOR64(dstSize,op1,op2) 

    }
/// HELPER FUNCTIONS
    // AND HELPER FUNCTIONS //
function evalAND8(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 1
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseAndBytes(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,1,false)      
     }     

function evalAND16(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 2
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseAndHalfWord(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,2,false)      
     }

function evalAND32(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 4
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseAnd(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,4,false)      
     }

function evalAND64(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 8
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseAnd64(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,8,false)      
     }

    // OR HELPER FUNCTIONS //
function evalOR8(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 1
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseOrBytes(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,1,false)      
     }     

function evalOR16(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 2
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseOrHalfWord(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,2,false)      
     }

function evalOR32(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 4
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseOr(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,4,false)      
     }

function evalOR64(dstSize:bitWidth,op1:Data,op2:Data): (out:Data)
      requires isInt(op1) && isInt(op2)
      requires typesMatch(op1,op2)
      requires op1.itype.size == 8
      requires dstSize == op1.itype.size
      ensures out.Int?;
      ensures out.itype.size == dstSize && !out.itype.signed;
     {
        reveal_ToTwosComp(); 
        reveal_IntFits();
        var result := BitwiseOr64(ToTwosComp(op1).val,ToTwosComp(op2).val);
        ValToData(result,8,false)      
     }
     // --  Lemmas for correctness checking -----
    lemma evalSHLIsValid()
    {
       
    }

    lemma evalLSHRIsValid()
    {
        reveal_IntFits();
        reveal_IntFromBytes();
        reveal_IntToBytes();
        reveal_ExtendZeroBytes();
        reveal_rightShift();
        reveal_WordToBits64();
        reveal_BitsToWord64();
        reveal_ToTwosComp();
        // <result> = lshr i32 4, 1   ; yields i32:result = 2
         var v0:uint32 := 4;
         var v1:uint32 := 1;
         var d0:uint32 := 2;
         var out:Data := evalLSHR(UInt32(v0),UInt32(v1));
         assert out.itype.size == 4;// == UInt64(d0);
         assert out.val == 2;
         assert out.val == UInt32(d0).val;

        // <result> = lshr i32 4, 2   ; yields i32:result = 1
         var v2:uint32 := 4;
         var v3:uint32 := 2;
         var d1:uint32 := 1;
         var out1:Data := evalLSHR(UInt32(v2),UInt32(v3));
         assert out1.itype.size == 4;// == UInt64(d0);
         assert out1.val == 1;
         assert out1.val == UInt32(d1).val;

        // <result> = lshr i8  4, 3   ; yields i8:result = 0
         var v4:uint32 := 4;
         var v5:uint32 := 3;
         var d2:uint32 := 0;
         var out2:Data := evalLSHR(UInt32(v4),UInt32(v5));
         assert out2.itype.size == 4;// == UInt64(d0);
         assert out2.val == 0;
         assert out2.val == UInt32(d2).val;
         
        // <result> = lshr i8 -2, 1   ; yields i8:result = 0x7F
         var v6:sint8 := -2;
         var v7:uint32 := 1;
         var d3:uint8 := 127;
         var out3:Data := evalLSHR(SInt8(v6),UInt32(v7));
         assert out3.itype.size == 1;// == UInt64(d0);
         assert out3.val == 127;
         assert out3.val == UInt8(d3).val;

         // <result> = lshr i8 -2, 1   ; yields i8:result = 0x7F
         var v8:sint8 := -42;
         var v9:uint32 := 2;
         var d4:uint8 := 53;
         var out4:Data := evalLSHR(SInt8(v8),UInt32(v9));
         assert out4.itype.size == 1;// == UInt64(d0);
         assert out4.val == 53;
         assert out4.val == UInt8(d4).val;

        //
       
    }

    lemma evalANDIsValid()
    {
         reveal_BitAnd();
         reveal_BitAnd16();
         reveal_BitAnd8();
         reveal_BitAnd64();
         reveal_BitsToWord();
         reveal_WordToBits();

        //<result> = and i32 15, 40     ; yields i32:result = 8
         var v0:uint32 := 15;
         var v1:uint32 := 40;
         var d0:uint32 := 8;
         var out:Data := evalAND(4,UInt32(v0),UInt32(v1));
         assert out.itype.size == 4;// == UInt64(d0);
         lemma_WordToBitsToWord(v0);
         assert WordToBits(v0) == 15;
         assert WordToBits(v1) == 40;
         assert out.val == 8;
        // <result> = and i32 4, 8      ; yields i32:result = 0
         var v2:uint32 := 4;
         var v3:uint32 := 8;
         var d1:uint32 := 8;
         var out1:Data := evalAND(4,UInt32(v2),UInt32(v3));
         assert out1.itype.size == 4;// == UInt64(d0);
         assert WordToBits(v2) == 4;
         assert WordToBits(v3) == 8;
         assert out1.val == 0;

    }

        lemma evalORIsValid()
    {
         reveal_BitOr();
         reveal_BitOr16();
         reveal_BitOr8();
         reveal_BitOr64();
         reveal_BitsToWord();
         reveal_WordToBits();

        //<result> = and i32 15, 40     ; yields i32:result = 47
         var v0:uint32 := 15;
         var v1:uint32 := 40;
         var out:Data := evalOR(4,UInt32(v0),UInt32(v1));
         assert out.itype.size == 4;// == UInt64(d0);
         lemma_WordToBitsToWord(v0);
         assert WordToBits(v0) == 15;
         assert WordToBits(v1) == 40;
         assert out.val == 47;
        // <result> = and i32 4, 8      ; yields i32:result = 12
         var v2:uint32 := 4;
         var v3:uint32 := 8;
         var out1:Data := evalOR(4,UInt32(v2),UInt32(v3));
         assert out1.itype.size == 4;// == UInt64(d0);
         assert WordToBits(v2) == 4;
         assert WordToBits(v3) == 8;
         assert out1.val == 12;

    }


}