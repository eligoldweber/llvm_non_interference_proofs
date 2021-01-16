module types {

datatype condition = eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle

/////////////////
// Native types
/////////////////
// newtype{:nativeType "bit"} bit = i:int | 0 <= i < 1
newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "uint"} uint = i:int | 0 <= i < 0x1_0000_0000
newtype{:nativeType "ulong"} ulong = i:int | 0 <= i < 0x1_0000_0000_0000_0000


////////////////////////////////////////////////////////////////
// Primitive data types
////////////////////////////////////////////////////////////////

// The integer types as normally defined
type uint8   = i:int | 0 <= i < 0x100
type uint16  = i:int | 0 <= i < 0x10000
type uint32  = i:int | 0 <= i < 0x1_0000_0000
type uint64  = i:int | 0 <= i < 0x1_0000_0000_0000_0000
type sint8   = i:int | -0x80 <= i < 0x80 
type sint16  = i:int | -0x8000 <= i < 0x8000
type sint32  = i:int | -0x8000_0000 <= i < 0x8000_0000
type sint64  = i:int | -0x8000_0000_0000_0000 <= i < 0x8000_0000_0000_0000

//ADD MATH FROM IRONFLEET? IE redo this
type bitWidth = s:nat | (s == 1 || s == 2 || s == 4 || s == 8) ghost witness 1
// Our integers have a type associated with them that stores their size and whether
// they're signed/unsigned
datatype IntType_ = IntType(size:bitWidth, signed:bool)
type IntType = t:IntType_ | t.size > 0 ghost witness IntType(1, false)

// Bytes is just that; a list of bytes
type Byte = b:int | 0 <= b < 0x100
type Bytes = b:seq<Byte> | |b| > 0 ghost witness [0]

// A point of data is a primitive in our program. It could either be a sequence of bytes,
// a pointer (in block/index form), or an integer. The validity of these is built into
// the "Data" type
datatype Data_ = Bytes(bytes:Bytes) |
                 Ptr(block:nat, bid:nat, offset:nat) |
                 Int(val:int, itype:IntType) | Void
type Data = d:Data_ | (d.Int? ==> IntFits(d.val, d.itype)) ghost witness Bytes([0])

// Specifies whether the given integer value fits in the given IntType; used for the
// validity specification of Data
predicate {:opaque} IntFits(val:int, itype:IntType) {
    var bound := Pow256(itype.size);
    if itype.signed then (-bound/2 <= val < bound/2)
    else (0 <= val < bound)
}

// For aiding in converting between the size of a number in bytes and its bounds
function Pow256(n:nat) : int
    decreases n
{
    if n == 0 then 1
    else 0x100 * Pow256(n-1)
}

function Pow128(n:nat) : int
    decreases n
{
    if n == 0 then 1
    else 0x80 * Pow128(n-1)
}

function  power2(exp: nat) : int
    ensures power2(exp) > 0;
{
    if (exp==0) then
        1
    else
        2*power2(exp-1)
}

// Functions to return a Data of the given integer type given the appropriate integer
// value
function UInt8(val:uint8) : Data { reveal_IntFits(); Int(val, IntType(1, false)) }
function UInt16(val:uint16) : Data { reveal_IntFits(); Int(val, IntType(2, false)) }
function UInt32(val:uint32) : Data { reveal_IntFits(); Int(val, IntType(4, false)) }
function UInt64(val:uint64) : Data { reveal_IntFits(); Int(val, IntType(8, false)) }
function SInt8(val:sint8) : Data { reveal_IntFits(); Int(val, IntType(1, true)) }
function SInt16(val:sint16) : Data { reveal_IntFits(); Int(val, IntType(2, true)) }
function SInt32(val:sint32) : Data { reveal_IntFits(); Int(val, IntType(4, true)) }
function SInt64(val:sint64) : Data { reveal_IntFits(); Int(val, IntType(8, true)) }


predicate isInt(data:Data)
{
    data.Int?
}

function DataToUInt8(data:Data) : uint8 
    requires isInt(data)
    requires data.itype.size == 1 && !data.itype.signed  
    {data.val % 0x100}
function DataToUInt16(data:Data) : uint16 
    requires isInt(data)
    requires data.itype.size == 2 && !data.itype.signed  
    {data.val % 0x10000}
function DataToUInt32(data:Data) : uint32 
    requires isInt(data)
    requires data.itype.size == 4 && !data.itype.signed  
    {data.val % 0x1_0000_0000}
function DataToUInt64(data:Data) : uint64 
    requires isInt(data)
    requires data.itype.size == 8 && !data.itype.signed  
    {data.val % 0x1_0000_0000_0000_0000}


 function DataToSInt8(data:Data) : sint8 
    requires isInt(data)
    requires data.itype.size == 1 && data.itype.signed  
    {data.val % 0x80}
function DataToSInt16(data:Data) : sint16 
    requires isInt(data)
    requires data.itype.size == 2 && data.itype.signed  
    {data.val % 0x8000}
function DataToSInt32(data:Data) : sint32 
    requires isInt(data)
    requires data.itype.size == 4 && data.itype.signed  
    {data.val % 0x8000_0000}
function DataToSInt64(data:Data) : sint64 
    requires isInt(data)
    requires data.itype.size == 8 && data.itype.signed  
    {data.val % 0x8000_0000_0000_0000}   



predicate typesMatch(x:Data, y:Data)
    requires isInt(x)
    requires isInt(y)
{
    x.itype.size == y.itype.size && x.itype.signed == y.itype.signed
}

function boolToData(b:bool) : (out:Data)
    ensures out.Int? && !out.itype.signed 
    ensures out.itype.size == 1
{
    reveal_IntFits();
    var val:int := (if b then 1 else 0);
    var size:bitWidth := 1;
    Int(val, IntType(size, false))
}

function dataToBool(b:Data) : (out:bool)
    requires b.Int? && !b.itype.signed 
    requires b.itype.size == 1
{
    reveal_IntFits();
    var val:int := b.val;
    if val == 1 then true else false
}

function ValToData(val:int, size:bitWidth, sign:bool ) : (out:Data)
    requires IntFits(val, IntType(size, sign))
    ensures isInt(out)
    ensures out.itype.signed == sign
    ensures out.itype.size == size
{
    reveal_IntFits();
    var iType:IntType := IntType(size, sign);
    Int(val, iType) 
}

////////////////////////////////////////////////////////////////
// Primitive data operations
////////////////////////////////////////////////////////////////

// Converts a signed integer to its unsigned representation in two's complement so it
// can be converted into bytes and stored in memory
function {:opaque} ToTwosComp(data:Data) : (out:Data)
    requires data.Int?
    ensures out.Int? && !out.itype.signed
    ensures out.itype.size == data.itype.size
{
    reveal_IntFits();
    var newval := (if data.val >= 0 then data.val else data.val + Pow256(data.itype.size));
    Int(newval, IntType(data.itype.size, false))
}

// Converts an unsigned two's complement number back to its signed representation for
// returning from a sequence of bytes back to a normal integer
function {:opaque} FromTwosComp(data:Data) : (out:Data)
    requires data.Int? 
    ensures out.Int? && out.itype.signed
    ensures out.itype.size == data.itype.size
{
    reveal_IntFits();
    var bound := Pow256(data.itype.size);
    var newval := (if data.val < bound/2 then data.val else data.val - bound);
    Int(newval, IntType(data.itype.size, true))
}

// Makes sure that sending numbers through two's complement and back doesn't change them
lemma {:opaque} TwosCompIdentity(data:Data)
    requires data.Int? && data.itype.signed
    ensures FromTwosComp(ToTwosComp(data)) == data
{
    reveal_ToTwosComp();
    reveal_FromTwosComp();
}

//Unsigned Byte extension to size dst
function {:opaque} ExtendZeroBytes(src:Bytes,dst:nat) : (bytes:Bytes)
    requires dst >= |src|
    ensures |bytes| == dst
    ensures bytes ==  src + zeroArray(dst - |src|) 
    decreases dst
{
    src + zeroArray(dst - |src|) 
}

// outputs Byte seq of length s with all values eqaul to 0
function {:opaque} zeroArray(s:nat) : (bytes:Bytes)
    requires s >= 0
    ensures |bytes| == s
    ensures forall b :: b in bytes ==> b == 0;
    decreases s
{
    if s == 0 then []
    else  [0] + zeroArray(s-1) 
}

// Signed Byte extension to size dst
function {:opaque} ExtendSignedBytes(src:Bytes,dst:nat) : (bytes:Bytes)
    requires dst >= |src|
    ensures |bytes| == dst
    ensures bytes ==  src + oneArray(dst - |src|) 
    decreases dst
{
    src + oneArray(dst - |src|) 
}

// outputs Byte seq of length s with all values eqaul to 1
function {:opaque} oneArray(s:nat) : (bytes:Bytes)
    requires s >= 0
    ensures |bytes| == s
    ensures forall b :: b in bytes ==> b == 1;
    decreases s
{
    if s == 0 then []
    else  [1] + oneArray(s-1) 
}

// Truncates Bytes seq to size s
function {:opaque} TruncateBytes(b:Bytes,s:nat) : (bytes:Bytes)
    requires s >= 0
    ensures |bytes| == s
    decreases s
{
    if s == 0 then []
    else  
        var start:Bytes := [b[0]]; 
        start + TruncateBytes(b,s-1)
}

// Transforms data that is in some arbitrary int form into a sequence of bytes
function {:opaque} IntToBytes(data:Data) : (bytes:Bytes)
    requires data.Int?
    ensures |bytes| == data.itype.size
{
    reveal_IntFits();
    var val := if data.itype.signed then ToTwosComp(data).val else data.val;
    RecurseIntToBytes(val, data.itype.size)
}

// Helper function for IntToBytes() that performs the operation on specifically unsigned
// integers recursively
function {:opaque} RecurseIntToBytes(val:nat, size:nat) : (bytes:Bytes)
    requires size > 0
    requires val < Pow256(size)
    ensures |bytes| == size
    decreases size
{
    if size == 1 then [val]
    else [val % 0x100] + RecurseIntToBytes(val / 0x100, size - 1)
}

// Transforms a list of bytes back into the given integer format
function {:opaque} IntFromBytes(bytes:Bytes, itype:IntType) : (data:Data)
    requires |bytes| == itype.size
    ensures data.Int?
    ensures data.itype == itype
{
    reveal_IntFits();
    var udata := Int(RecurseIntFromBytes(bytes), IntType(itype.size, false));
    if itype.signed then FromTwosComp(udata)
    else udata
}

// Helper function for IntFromBytes that performs the operation for specifically unsigned
// integers recursively
function {:opaque} RecurseIntFromBytes(bytes:Bytes) : (val:nat)
    ensures val < Pow256(|bytes|)
    decreases bytes
{
    if |bytes| == 1 then bytes[0]
    else (bytes[0] as nat) + (0x100 * RecurseIntFromBytes(bytes[1..]))
}

// Starting small, we'll do the recursive identity
lemma {:opaque} {:induction val, size} RecursiveIdentity(val:nat, size:nat)
    requires size > 0
    requires val < Pow256(size)
    ensures RecurseIntFromBytes(RecurseIntToBytes(val, size)) == val
{
    reveal_IntToBytes();
    reveal_IntFromBytes();
    reveal_RecurseIntToBytes();
    reveal_RecurseIntFromBytes();
}

// Now, we make sure that converting data to/from bytes doesn't change it
lemma {:opaque} IntBytesIdentity(data:Data)
    requires data.Int?
    ensures IntFromBytes(IntToBytes(data), data.itype) == data
{
    reveal_IntFits();
    reveal_IntToBytes();
    reveal_IntFromBytes();
    reveal_RecurseIntToBytes();
    reveal_RecurseIntFromBytes();
    if (data.itype.signed) {
        var udata := ToTwosComp(data);
        TwosCompIdentity(data);
        RecursiveIdentity(udata.val, udata.itype.size);
    } else {
        RecursiveIdentity(data.val, data.itype.size);
    }
}

/////////////////
// Quadword
/////////////////

datatype Quadword = Quadword(lo:uint32, mid_lo:uint32, mid_hi:uint32, hi:uint32)

/////////////////
// BitsOfByte
/////////////////

newtype{:nativeType "byte"} twobits = i:int | 0 <= i < 4
datatype BitsOfByte = BitsOfByte(lo:twobits,
                                 mid_lo:twobits,
                                 mid_hi:twobits,
                                 hi:twobits)

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
function method {:opaque} BitsToByte(b:bv8) : uint8 { b as uint8 }
function method {:opaque} ByteToBits(w:uint8) : bv8 { w as bv8 }

lemma {:axiom} lemma_BitsToByteToByte(b:bv8)
    ensures ByteToBits(BitsToByte(b)) == b;

lemma {:axiom} lemma_ByteToBitsToByte(w:uint8)
    ensures BitsToByte(ByteToBits(w)) == w;


function method {:opaque} BitsToHalfWord(b:bv16) : uint16 { b as uint16 }
function method {:opaque} HalfWordToBits(w:uint16) : bv16 { w as bv16 }

lemma {:axiom} lemma_BitsToWordToHalfBits(b:bv16)
    ensures HalfWordToBits(BitsToHalfWord(b)) == b;

lemma {:axiom} lemma_HalfWordToBitsToHalfWord(w:uint16)
    ensures BitsToHalfWord(HalfWordToBits(w)) == w;

function method {:opaque} BitsToWord(b:bv32) : uint32 { b as uint32 }
function method {:opaque} WordToBits(w:uint32) : bv32 { w as bv32 }

lemma {:axiom} lemma_BitsToWordToBits(b:bv32)
    ensures WordToBits(BitsToWord(b)) == b;

lemma {:axiom} lemma_WordToBitsToWord(w:uint32)
    ensures BitsToWord(WordToBits(w)) == w;

function method {:opaque} BitsToWord64(b:bv64) : uint64 { b as uint64 }
function method {:opaque} WordToBits64(w:uint64) : bv64 { w as bv64 }

lemma {:axiom} lemma_BitsToWordToBits64(b:bv64)
    ensures WordToBits64(BitsToWord64(b)) == b;

lemma {:axiom} lemma_WordToBitsToWord64(w:uint64)
    ensures BitsToWord64(WordToBits64(w)) == w;

    // predicate typesMatch(v0:Value,v1:Value)
    // {
    //     (v0.Val8? ==> v1.Val8? )
    //     && (v0.Val16? ==> v1.Val16?)
    //     && (v0.Val32? ==> v1.Val32? )
    //     && (v0.Val64? ==> v1.Val64? )
    //     && (v0.ValBool? ==> !v1.ValBool? )
    // }

} // end module types
