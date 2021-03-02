include "../ops.dfy"
include "../types.dfy"


module binary_operations_helper_i {
    import opened ops
    import opened types

    function evalADD8(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 1
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures (!v0.itype.signed) ==> out.val == (v0.val + v1.val) % 0x100
        ensures (v0.itype.signed) ==> ToTwosComp(out).val == (v0.val + v1.val) % 0x100
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt8(BitwiseAdd8(DataToUInt8(ToTwosComp(v0)),DataToUInt8(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt8(BitwiseAdd8(DataToUInt8(ToTwosComp(v1)),DataToUInt8(ToTwosComp(v0)))))  
        }
        
    function evalADD16(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 2
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures (!v0.itype.signed) ==> out.val == (v0.val + v1.val) % 0x10000
        ensures (v0.itype.signed) ==> ToTwosComp(out).val == (v0.val + v1.val) % 0x10000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt16(BitwiseAdd16(DataToUInt16(ToTwosComp(v0)),DataToUInt16(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt16(BitwiseAdd16(DataToUInt16(ToTwosComp(v1)),DataToUInt16(ToTwosComp(v0)))))
        }

    function evalADD32(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 4
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures (!v0.itype.signed) ==> out.val == (v0.val + v1.val) % 0x1_0000_0000
        ensures (v0.itype.signed) ==> ToTwosComp(out).val == (v0.val + v1.val) % 0x1_0000_0000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt32(BitwiseAdd32(DataToUInt32(ToTwosComp(v0)),DataToUInt32(ToTwosComp(v1)))) else  
                                       FromTwosComp(UInt32(BitwiseAdd32(DataToUInt32(ToTwosComp(v1)),DataToUInt32(ToTwosComp(v0)))))
        }

    function evalADD64(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 8
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures (!v0.itype.signed) ==> out.val == (v0.val + v1.val) % 0x1_0000_0000_0000_0000
        ensures (v0.itype.signed) ==> ToTwosComp(out).val == (v0.val + v1.val) % 0x1_0000_0000_0000_0000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt64(BitwiseAdd64(DataToUInt64(ToTwosComp(v0)),DataToUInt64(ToTwosComp(v1)))) else  
                                       FromTwosComp(UInt64(BitwiseAdd64(DataToUInt64(ToTwosComp(v1)),DataToUInt64(ToTwosComp(v0)))))
        }

    // SUB //
    function evalSUB8(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 1
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures  ToTwosComp(out).val == (v0.val - v1.val) % 0x100
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(v0)),DataToUInt8(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt8(BitwiseSub8(DataToUInt8(ToTwosComp(v0)),DataToUInt8(ToTwosComp(v1)))))  
        }

    function evalSUB16(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 2
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures  ToTwosComp(out).val == (v0.val - v1.val) % 0x10000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt16(BitwiseSub16(DataToUInt16(ToTwosComp(v0)),DataToUInt16(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt16(BitwiseSub16(DataToUInt16(ToTwosComp(v0)),DataToUInt16(ToTwosComp(v1)))))  
        }
    
    function evalSUB32(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 4
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures  ToTwosComp(out).val == (v0.val - v1.val) % 0x1_0000_0000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt32(BitwiseSub32(DataToUInt32(ToTwosComp(v0)),DataToUInt32(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt32(BitwiseSub32(DataToUInt32(ToTwosComp(v0)),DataToUInt32(ToTwosComp(v1)))))   
        }
    
    function evalSUB64(size:nat,v0:Data,v1:Data):  (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        requires validBitWidth(v0.itype.size)
        requires v0.itype.size == 8
        ensures out.Int?
        ensures validBitWidth(out.itype.size)
        ensures  ToTwosComp(out).val == (v0.val - v1.val) % 0x1_0000_0000_0000_0000
        
        {
            reveal_ToTwosComp();
            reveal_FromTwosComp();
            if (!v0.itype.signed) then UInt64(BitwiseSub64(DataToUInt64(ToTwosComp(v0)),DataToUInt64(ToTwosComp(v1)))) else 
                                       FromTwosComp(UInt64(BitwiseSub64(DataToUInt64(ToTwosComp(v0)),DataToUInt64(ToTwosComp(v1)))))   
        }
}