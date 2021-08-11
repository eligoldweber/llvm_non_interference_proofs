include "../ops.dfy"
include "../types.dfy"

// Contains the following conversion operations: ICMP
// TODO: FCMP, PHI, CALL 

module other_operations_i {
    import opened ops
    import opened types

     // eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

    function evalICMP(c:condition,size:nat,v0:Data,v1:Data): (out:Data)
        requires isInt(v0)
        requires isInt(v1)
        requires typesMatch(v0,v1)
        ensures out.Int? && !out.itype.signed
        ensures out.itype.size == 1 
        ensures out.val == 0 || out.val == 1
    {
        match c
            case eq => boolToData(v0.val == v1.val)
            case ne => boolToData(v0.val != v1.val)
            case ugt => boolToData(ToTwosComp(v0).val > ToTwosComp(v1).val)
            case uge => boolToData(ToTwosComp(v0).val >= ToTwosComp(v1).val) 
            case ult => boolToData(ToTwosComp(v0).val < ToTwosComp(v1).val)
            case ule => boolToData(ToTwosComp(v0).val <= ToTwosComp(v1).val) 
            case sgt => boolToData(FromTwosComp(v0).val > FromTwosComp(v1).val)             
            case sge => boolToData(FromTwosComp(v0).val >= FromTwosComp(v1).val) 
            case slt => boolToData(FromTwosComp(v0).val < FromTwosComp(v1).val)             
            case sle => boolToData(FromTwosComp(v0).val <= FromTwosComp(v1).val)
    }

//-----------------------------------------------------------------------------
// Instruction VALIDITY
//-----------------------------------------------------------------------------

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

        var v10:uint16 := 65000;
        var v11:uint16 := 0;
        assert !(FromTwosComp(UInt16(v10)).val >= FromTwosComp(UInt16(v11)).val);
        assert evalICMP(sge,2,UInt16(v10),UInt16(v11)).val == 0;
        
    } 

}