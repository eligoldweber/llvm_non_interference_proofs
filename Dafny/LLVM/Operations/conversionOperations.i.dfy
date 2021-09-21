include "../ops.dfy"
include "../types.dfy"

// Contains the following conversion operations: TRUNC, ZEXT, SEXT
// TODO: BITCAST
module conversion_operations_i {
    import opened ops
    import opened types

    function evalTRUNC(src:Data,dstSize:bitWidth): (out:Data)
        requires isInt(src)
        requires src.itype.size >= dstSize;
        ensures out.Int?;
        ensures out.itype.size == dstSize;
    {
        
        var bytes := IntToBytes(src);
        var slice:seq<Byte> := TruncateBytes(bytes,dstSize);
        IntFromBytes(slice,IntType(dstSize, false))

    }

    function evalZEXT(src:Data,dstSize:bitWidth): (out:Data)
        requires isInt(src)
        requires src.itype.size < dstSize;
        ensures out.Int?;
        ensures out.itype.size == dstSize && !out.itype.signed;
    {
        

        var bytes := IntToBytes(src);
        var extendedBytes := ExtendZeroBytes(bytes,dstSize);
        assert |extendedBytes| == |bytes| + (dstSize - |bytes|);
        IntFromBytes(extendedBytes,IntType(dstSize, false))

    }
   
    function evalSEXT(src:Data,dstSize:bitWidth): (out:Data)
        requires isInt(src)
        requires src.itype.size < dstSize;
        ensures out.Int?;
        ensures out.itype.size == dstSize && out.itype.signed;
    {
        
        var bytes := IntToBytes(src);
        var extendedBytes := ExtendSignedBytes(bytes,dstSize);
        assert |extendedBytes| == |bytes| + (dstSize - |bytes|);
        IntFromBytes(extendedBytes,IntType(dstSize, true))

    }
    // function evalPTRTOINT(src:Data,dstSize:bitWidth): (out:Data)
    //     requires src.Ptr?
    //     ensures out.Int?
    //     ensures out.itype.size == dstSize
    // {
    // }

    // function evalINTTOPTR(src:Data,dstSize:bitWidth): (out:Data)
    //     requires src.Int?
    //     ensures out.Ptr?
    //     ensures out.itype.size == dstSize
    // {
    // }
    function evalBITCAST(src:Data,castType:Data): (out:Data)
        // requires validBitWidth(dstSize)
        requires (src.Int? && castType.Int?) || (src.Ptr? && castType.Ptr?);
        ensures (src.Int? && out.Int?) || (src.Ptr? && out.Ptr?);
    {
        if src.Ptr? then    
            var o:Data := Ptr(src.block, src.bid, src.offset, castType.size);
            o
        else
            if src.itype.size <= castType.itype.size then 
                assert IntFits(src.val, IntType(castType.itype.size,src.itype.signed)); 
                var o:Data := Int(src.val,IntType(castType.itype.size,src.itype.signed)); 
                o
            else 
                var o:Data := evalTRUNC(src,castType.itype.size); 
                o

    }

// --  Lemmas for correctness checking -----
    lemma evalTRUNCIsValid()
    {
        
        
        // %X = trunc i32 257 to i8                        ; yields i8:1
        var v0:sint32 := 257;
        var d0:sint8 := 1;
        var out:Data := evalTRUNC(SInt32(v0),1);
        assert out.itype.size == 1;// == UInt64(d0);
        // assert out.val == SInt8(d0).val;
        // assert out.val == 1;
       
        // %Y = trunc i32 123 to i1                        ; yields i1:true
        var v1:uint32 := 123;
        var d1:uint8 := 1;
        var out1:Data := evalTRUNC(UInt32(v1),1);
        assert out1.itype.size == 1;// == UInt64(d0);
        // assert out1.val == UInt8(d1).val;
        // assert out1.val == 1;

        // %Z = trunc i32 122 to i1                        ; yields i1:false
        var v2:uint32 := 122;
        var d2:uint8 := 0;
        var out2:Data := evalTRUNC(UInt32(v2),1);
        assert out2.itype.size == 1;// == UInt64(d0);
        // assert out2.val == UInt8(d2).val;
        // assert out2.val == 0;
    }


    lemma evalZEXTIsValid()
    {
        var v0:uint16 := 42;
        var d0:uint32 := 42;
        var out:Data := evalZEXT(UInt16(v0),4);
        assert out.itype.size == 4;// == UInt64(d0);\
        // assert out.val == UInt32(d0).val;
        // assert out.val == 42;
        // assert out.val == UInt16(d0).val;
        var v1:bool := true;
        var d1:uint32 := 1;
        var out1:Data := evalZEXT(boolToData(v1),4);
        assert out1.itype.size == 4;
        // assert out1.val == UInt32(d1).val;

        // %X = zext i32 257 to i64

        var v2:uint32 := 257;
        var d2:uint64 := 257;
        var out2:Data := evalZEXT(UInt32(v2),8);
        assert out2.itype.size == 8;
        // assert out2.val == UInt64(d2).val;
    }


    lemma evalSEXTIsValid()
    {
        
        
        var v0:sint8 := -1;
        var d0:sint16 := -1;
        var out:Data := evalSEXT(SInt8(v0),2);
        assert out.itype.size == 2;// == UInt64(d0);
        // assert out.val == SInt16(d0).val;
        // assert out.val == -1;
        // %Y = sext i1 true to i32             ; yields i32:-1
        var v1:bool := true;
        var d1:sint32 := -1;
        var out1:Data := evalSEXT(boolToData(v1),4);
        // assert out1.itype.size == 4;
        // assert out1.val == SInt32(d1).val;
    }


    // function evalZEXT(src:Data,dstSize:bitWidth): (out:Data)
    //     requires isInt(src)
    //     requires src.itype.size < dstSize;
    //     requires !src.itype.signed // Is this always the case?? 
    //     ensures out.Int?;
    //     ensures out.itype.size == dstSize && !out.itype.signed;
    // {
    //     reveal_IntFits();
    //     assert IntFits(src.val, IntType(dstSize, false));
    //     ValToData(src.val,dstSize,false)
    // }

    // function evalSEXT(src:Data,dstSize:bitWidth): (out:Data)
    //     requires isInt(src)
    //     requires src.itype.size < dstSize;
    //     ensures out.Int?;
    //     ensures out.itype.size == dstSize && out.itype.signed;
    // {
    //     reveal_IntFits();
    //     assert IntFits(src.val, IntType(dstSize, true));
    //     ValToData(src.val,dstSize,true)
    // }


//     function evalZEXT8Helper(src:Value) : Value
//     {
//        src
//     }

//     function evalZEXT16Helper(src:Value) : Value
//     {
//         if src.Val8? then Val16(Bitwise8CastTo16(src.v8)) else src
//     }

//     function evalZEXT32Helper(src:Value) : Value
//     {
//         if src.Val8? then Val32(Bitwise8CastTo32(src.v8)) else 
//         if src.Val16? then Val32(Bitwise16CastTo32(src.v16)) else src 
//     }

//     function evalZEXT64Helper(src:Value) : Value
//     {
//         if src.Val8? then Val64(Bitwise8CastTo64(src.v8)) else 
//         if src.Val16? then Val64(Bitwise16CastTo64(src.v16)) else
//         if src.Val32? then Val64(Bitwise32CastTo64(src.v32)) else src
//     }

    
//     function evalSEXT8Helper(src:Value) : Value
//     {
//        src
//     }

//     function evalSEXT16Helper(src:Value) : Value
//     {
//         if src.SVal8? then SVal16(SignedBitwise8CastTo16(src.sv8)) else src
//     }

//     function evalSEXT32Helper(src:Value) : Value
//     {
//         if src.SVal8? then SVal32(SignedBitwise8CastTo32(src.sv8)) else 
//         if src.SVal16? then SVal32(SignedBitwise16CastTo32(src.sv16)) else src 
//     }

//     function evalSEXT64Helper(src:Value) : Value
//     {
//         if src.SVal8? then SVal64(SignedBitwise8CastTo64(src.sv8)) else 
//         if src.SVal16? then SVal64(SignedBitwise16CastTo64(src.sv16)) else
//         if src.SVal32? then SVal64(SignedBitwise32CastTo64(src.sv32)) else src
//     }


// ///// Cast functions /////

// ////----UNSIGNED----////

// //
// function {:opaque} Bitwise8CastTo16(x:uint8):uint16
// {
//     x  % 0x1000
// }
// //
// function {:opaque} Bitwise8CastTo32(x:uint8):uint32
// {
//     x  % 0x1_0000_0000
// }
// function {:opaque} Bitwise16CastTo32(x:uint16):uint32
// {
//     x  % 0x1_0000_0000
// }
// //
// function {:opaque} Bitwise8CastTo64(x:uint8):uint64
// {
//     x  % 0x1_0000_0000_0000_0000
// }
// function {:opaque} Bitwise16CastTo64(x:uint16):uint64
// {
//     x  % 0x1_0000_0000_0000_0000
// }
// function {:opaque} Bitwise32CastTo64(x:uint32):uint64
// {
//     x  % 0x1_0000_0000_0000_0000
// }

// ////----SIGNED----////

// function {:opaque} SignedBitwise8CastTo16(x:sint8):sint16
// {
//     x  % 0x8000
// }
// function {:opaque} SignedBitwise8CastTo32(x:sint8):sint32
// {
//     x  % 0x80000000
// }
// function {:opaque} SignedBitwise16CastTo32(x:sint16):sint32
// {
//     x  % 0x80000000
// }
// function {:opaque} SignedBitwise8CastTo64(x:sint8):sint64
// {
//     x  % 0x8000000000000000
// }
// function {:opaque} SignedBitwise16CastTo64(x:sint16):sint64
// {
//     x  % 0x8000000000000000
// }
// function {:opaque} SignedBitwise32CastTo64(x:sint32):sint64
// {
//     x  % 0x8000000000000000
// }


}
