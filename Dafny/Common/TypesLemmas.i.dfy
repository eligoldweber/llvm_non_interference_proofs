include "Types.s.dfy"

module TypesLemmas refines Types_s{
    // import opened Types_s

    function UInt8(val:uint8) : Data {  Int(val, IntType(1, false)) }
    function UInt16(val:uint16) : Data {  Int(val, IntType(2, false)) }
    function UInt32(val:uint32) : Data {  Int(val, IntType(4, false)) }
    function UInt64(val:uint64) : Data {  Int(val, IntType(8, false)) }
    function SInt8(val:sint8) : Data {  Int(val, IntType(1, true)) }
    function SInt16(val:sint16) : Data {  Int(val, IntType(2, true)) }
    function SInt32(val:sint32) : Data {  Int(val, IntType(4, true)) }
    function SInt64(val:sint64) : Data {  Int(val, IntType(8, true)) }

    function DataToUInt8(data:Data) : (out:uint8) 
        {data.val % 0x100}
    function DataToUInt16(data:Data) : (out:uint16) 
        {data.val % 0x10000}
    function DataToUInt32(data:Data) : (out:uint32) 
        {data.val % 0x1_0000_0000}
    function DataToUInt64(data:Data) : (out:uint64) 
        {data.val % 0x1_0000_0000_0000_0000}


    function DataToSInt8(data:Data) : (out:sint8) 
        {data.val % 0x80}
    function DataToSInt16(data:Data) : (out:sint16) 
        {data.val % 0x8000}
    function DataToSInt32(data:Data) : (out:sint32) 
        {data.val % 0x8000_0000}
    function DataToSInt64(data:Data) : (out:sint64) 
        {data.val % 0x8000_0000_0000_0000}   

    function boolToData(b:bool) : (out:Data)
        ensures out.Int? && !out.itype.signed 
        ensures out.itype.size == 1
    {
    
        var val:int := (if b then 1 else 0);
        var size:bitWidth := 1;
        Int(val, IntType(size, false))
    }

    function dataToBool(b:Data) : (out:bool)
        requires b.Int? && !b.itype.signed 
        requires b.itype.size == 1
    {
        
        var val:int := b.val;
        if val == 1 then true else false
    }

    function ValToData(val:int, size:bitWidth, sign:bool ) : (out:Data)
        requires IntFits(val, IntType(size, sign))
        ensures isInt(out)
        ensures out.itype.signed == sign
        ensures out.itype.size == size
    {
        
        var iType:IntType := IntType(size, sign);
        Int(val, iType) 
    }

    ////////////////////////////////////////////////////////////////
    // Primitive data operations
    ////////////////////////////////////////////////////////////////

    // Converts a signed integer to its unsigned representation in two's complement so it
    // can be converted into bytes and stored in memory
    function ToTwosComp(data:Data) : (out:Data)
        requires data.Int?
        ensures out.Int? && !out.itype.signed
        ensures out.itype.size == data.itype.size
    {
        
        var newval := (if data.val >= 0 then data.val else data.val + Pow256(data.itype.size));
        Int(newval, IntType(data.itype.size, false))
    }

    lemma UnsignedToTwosComp(data:Data)
        requires data.Int?
        requires !data.itype.signed
        ensures data == ToTwosComp(data)
    {
        assert data == ToTwosComp(data);
    }
    // Converts an unsigned two's complement number back to its signed representation for
    // returning from a sequence of bytes back to a normal integer
    function FromTwosComp(data:Data) : (out:Data)
        requires data.Int? 
        ensures out.Int? && out.itype.signed
        ensures out.itype.size == data.itype.size
    {
        
        var bound := Pow256(data.itype.size);
        var newval := (if data.val < bound/2 then data.val else data.val - bound);
        Int(newval, IntType(data.itype.size, true))
    }

    // Makes sure that sending numbers through two's complement and back doesn't change them
    lemma TwosCompIdentity(data:Data)
        requires data.Int? && data.itype.signed
        ensures FromTwosComp(ToTwosComp(data)) == data
    {
    }

    //Unsigned Byte extension to size dst
    function ExtendZeroBytes(src:Bytes,dst:nat) : (bytes:Bytes)
        requires dst >= |src|
        ensures |bytes| == dst
        ensures bytes ==  src + zeroArray(dst - |src|) 
        decreases dst
    {
        src + zeroArray(dst - |src|) 
    }

    // outputs Byte seq of length s with all values eqaul to 0
    function zeroArray(s:nat) : (bytes:seq<Byte>)
        requires s >= 0
        ensures |bytes| == s
        ensures forall b :: b in bytes ==> b == 0;
        decreases s
    {
        if s == 0 then []
        else  [0] + zeroArray(s-1) 
    }


    // Signed Byte extension to size dst
    function ExtendSignedBytes(src:Bytes,dst:nat) : (bytes:Bytes)
        requires dst >= |src|
        ensures |bytes| == dst
        ensures bytes ==  src + oneArray(dst - |src|) 
        decreases dst
    {
        src + oneArray(dst - |src|) 
    }

    // outputs Byte seq of length s with all values eqaul to 1
    function oneArray(s:nat) : (bytes:seq<Byte>)
        requires s >= 0
        ensures |bytes| == s
        ensures forall b :: b in bytes ==> b == 1;
        decreases s
    {
        if s == 0 then []
        else  [1] + oneArray(s-1) 
    }

    // Truncates Bytes seq to size s
    function TruncateBytes(b:Bytes,s:nat) : (bytes:seq<Byte>)
        requires s >= 0
        requires |b| > 0
        ensures |bytes| == s
        decreases s
    {
        if s == 0 then []
        else  
            var start:Bytes := [b[0]]; 
            start + TruncateBytes(b,s-1)
    }

    // Transforms data that is in some arbitrary int form into a sequence of bytes
    function IntToBytes(data:Data) : (bytes:Bytes)
    {
        var val := if data.itype.signed then ToTwosComp(data).val else data.val;
        RecurseIntToBytes(val, data.itype.size)
    }

    // Helper function for IntToBytes() that performs the operation on specifically unsigned
    // integers recursively
    function RecurseIntToBytes(val:nat, size:nat) : (bytes:Bytes)
        requires size > 0
        requires val < Pow256(size)
        ensures |bytes| == size
        decreases size
    {
        if size == 1 then [val]
        else [val % 0x100] + RecurseIntToBytes(val / 0x100, size - 1)
    }

    // Transforms a list of bytes back into the given integer format
    function IntFromBytes(bytes:Bytes, itype:IntType) : (data:Data)
        requires |bytes| == itype.size
        ensures data.Int?
        ensures data.itype == itype
    {
        
        var udata := Int(RecurseIntFromBytes(bytes), IntType(itype.size, false));
        if itype.signed then FromTwosComp(udata)
        else udata
    }

    // Helper function for IntFromBytes that performs the operation for specifically unsigned
    // integers recursively
    function RecurseIntFromBytes(bytes:Bytes) : (val:nat)
        ensures val < Pow256(|bytes|)
        decreases bytes
    {
        if |bytes| == 1 then bytes[0]
        else (bytes[0] as nat) + (0x100 * RecurseIntFromBytes(bytes[1..]))
    }

    // Starting small, we'll do the recursive identity
    lemma {:induction val, size} RecursiveIdentity(val:nat, size:nat)
        requires size > 0
        requires val < Pow256(size)
        ensures RecurseIntFromBytes(RecurseIntToBytes(val, size)) == val
    {
    }

    // Now, we make sure that converting data to/from bytes doesn't change it
    lemma IntBytesIdentity(data:Data)
        requires data.Int?
        ensures IntFromBytes(IntToBytes(data), data.itype) == data
    {
        
        if (data.itype.signed) {
            var udata := ToTwosComp(data);
            TwosCompIdentity(data);
            RecursiveIdentity(udata.val, udata.itype.size);
        } else {
            RecursiveIdentity(data.val, data.itype.size);
        }
    }

    function bits_to_byte(bits:BitsOfByte) : uint8
    {
        64 * (bits.hi as uint8) + 16 * (bits.mid_hi as uint8) + 4 * (bits.mid_lo as uint8) + (bits.lo as uint8)
    }

    function byte_to_bits(b:uint8) : BitsOfByte
    {
        BitsOfByte((b % 4) as twobits, ((b / 4) % 4) as twobits, ((b / 16) % 4) as twobits, ((b / 64) % 4) as twobits)
    }

    /////////////////
    // Bit vectors
    /////////////////
    function method BitsToByte(b:bv8) : uint8 { b as uint8 }
    function method ByteToBits(w:uint8) : bv8 { w as bv8 }

    lemma {:axiom} lemma_BitsToByteToByte(b:bv8)
        ensures ByteToBits(BitsToByte(b)) == b;

    lemma {:axiom} lemma_ByteToBitsToByte(w:uint8)
        ensures BitsToByte(ByteToBits(w)) == w;


    function method BitsToHalfWord(b:bv16) : uint16 { b as uint16 }
    function method HalfWordToBits(w:uint16) : bv16 { w as bv16 }

    lemma {:axiom} lemma_BitsToWordToHalfBits(b:bv16)
        ensures HalfWordToBits(BitsToHalfWord(b)) == b;

    lemma {:axiom} lemma_HalfWordToBitsToHalfWord(w:uint16)
        ensures BitsToHalfWord(HalfWordToBits(w)) == w;

    function method BitsToWord(b:bv32) : uint32 { b as uint32 }
    function method WordToBits(w:uint32) : bv32 { w as bv32 }

    lemma {:axiom} lemma_BitsToWordToBits(b:bv32)
        ensures WordToBits(BitsToWord(b)) == b;

    lemma {:axiom} lemma_WordToBitsToWord(w:uint32)
        ensures BitsToWord(WordToBits(w)) == w;

    function method BitsToWord64(b:bv64) : uint64 { b as uint64 }
    function method WordToBits64(w:uint64) : bv64 { w as bv64 }

    lemma {:axiom} lemma_BitsToWordToBits64(b:bv64)
        ensures WordToBits64(BitsToWord64(b)) == b;

    lemma {:axiom} lemma_WordToBitsToWord64(w:uint64)
        ensures BitsToWord64(WordToBits64(w)) == w;
}