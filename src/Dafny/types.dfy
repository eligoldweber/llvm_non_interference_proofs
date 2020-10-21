module types {

/////////////////
// Native types
/////////////////
// newtype{:nativeType "bit"} bit = i:int | 0 <= i < 1
newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "uint"} uint = i:int | 0 <= i < 0x1_0000_0000
newtype{:nativeType "ulong"} ulong = i:int | 0 <= i < 0x1_0000_0000_0000_0000

/////////////////
// Subset types
/////////////////

// The integer types as normally defined
type uint8   = i:int | 0 <= i < 0x100
type uint16  = i:int | 0 <= i < 0x10000
type uint32  = i:int | 0 <= i < 0x1_0000_0000
type uint64  = i:int | 0 <= i < 0x1_0000_0000_0000_0000
type int8    = i:int | -0x80 <= i < 0x80
type int16   = i:int | -0x8000 <= i < 0x8000
type int32   = i:int | -0x8000_0000 <= i < 0x8000_0000
type int64   = i:int | -0x8000_0000_0000_0000 <= i < 0x8000_0000_0000_0000
type sint8   = i:int | -0x80 <= i < 0x80 
type sint16  = i:int | -0x8000 <= i < 0x8000
type sint32  = i:int | -0x80000000 <= i < 0x80000000
type sint64  = i:int | -0x8000000000000000 <= i < 0x8000000000000000

// A pointer is a block/index, not an absolute value, based on our specification
// Each Data holds a piece of information that can be loaded/stored from/to memory
datatype Data = Bytes(bytes:seq<uint8>) |
                Ptr(block:nat, offset:nat) |
                Int(val:int, size:nat, signed:bool)

// For aiding in converting between the size of a number in bytes and its bounds
function Pow256(n:nat) : (ret:nat)
    ensures ret > 0
    decreases n
{
    if n == 0 then 1
    else 0x100 * Pow256(n-1)
}

// In order to be valid, integer types need to be within the bounds of their size
// Also, cannot have bytes that are empty
predicate {:opaque} ValidData(data:Data) {
    match data
        case Bytes(bytes) => |bytes| > 0
        case Ptr(block, offset) => true
        case Int(val, size, signed) =>
            var bound := Pow256(size) as int;
            if size == 0 then false
            else if signed then (-bound/2 <= val < bound/2)
            else (0 <= val < bound)
}

// Getters for the common integer types
function UInt8(val:uint8) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 1, false)
}

function UInt16(val:uint16) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 2, false)
}

function UInt32(val:uint32) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 4, false)
}

function UInt64(val:uint64) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 8, false)
}

function Int8(val:int8) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 1, true)
}

function Int16(val:int16) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 2, true)
}

function Int32(val:int32) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 4, true)
}

function Int64(val:int64) : (data:Data)
    ensures ValidData(data)
{
    reveal_ValidData();
    Int(val, 8, true)
}

// Converts a signed integer to its unsigned representation in two's complement
function {:opaque} ToTwosComp(data:Data) : (out:Data)
    requires data.Int? && data.signed && ValidData(data)
    ensures out.Int? && !out.signed && ValidData(out)
    ensures out.size == data.size
{
    reveal_ValidData();
    var newval := (if data.val >= 0 then data.val else data.val + Pow256(data.size));
    Int(newval, data.size, false)
}

// Converts an unsigned two's complement back to its signed integer counterpart
function {:opaque} FromTwosComp(data:Data) : (out:Data)
    requires data.Int? && !data.signed && ValidData(data)
    ensures out.Int? && out.signed && ValidData(out)
    ensures out.size == data.size
{
    reveal_ValidData();
    var bound := Pow256(data.size) as int;
    var newval := (if data.val < bound/2 then data.val else data.val - bound);
    Int(newval, data.size, true)
}

// // Makes sure that sending numbers through two's complement and back doesn't change them
lemma {:opaque} TwosCompIdentity(data:Data)
    requires data.Int? && data.signed && ValidData(data)
    ensures FromTwosComp(ToTwosComp(data)) == data
{
    reveal_ToTwosComp();
    reveal_FromTwosComp();
}

// Transforms data that is in some arbitrary form into byte form
function ToBytes(data:Data) : (bytes:seq<uint8>)
    requires !data.Ptr?
    requires ValidData(data)
    ensures data.Int? ==> |bytes| == data.size
{
    reveal_ValidData();
    if data.Bytes? then data.bytes
    else
        var val := if data.signed then ToTwosComp(data).val else data.val;
        UIntToBytes(val, data.size)
}

// Recursive helper function for ToBytes() for handling the integer case
function UIntToBytes(val:nat, size:nat) : (bytes:seq<uint8>)
    requires val < Pow256(size)
    ensures |bytes| == size
    decreases size
{
    if size == 0 then []
    else [val % 0x100] + UIntToBytes(val / 0x100, size - 1)
}

// Going the other way, we transform data that is in byte form back into some
// other format
function FromBytes(bytes:seq<uint8>, form:Data) : (data:Data)
    requires |bytes| > 0
    requires !form.Ptr?
    requires form.Int? ==> form.size == |bytes|
    ensures form.Bytes? ==> data.Bytes?
    ensures form.Int? ==> data.Int?
    ensures form.Int? ==> data.size == form.size
    ensures form.Int? ==> data.signed == form.signed
    ensures ValidData(data)
{
    reveal_ValidData();
    if form.Bytes? then Bytes(bytes)
    else
        var val := UIntFromBytes(bytes);
        var udata := Int(val, form.size, false);
        if form.signed then FromTwosComp(udata)
        else udata
}

// Recursive helper function for FromBytes() for handling the integer case
function UIntFromBytes(bytes:seq<uint8>) : (val:nat)
    ensures val < Pow256(|bytes|)
    decreases bytes
{
    if |bytes| == 0 then 0
    else bytes[0] + (0x100 * UIntFromBytes(bytes[1..]))
}

// First, let's just make sure that the uint conversions preserve information
lemma {:opaque} {:induction val, size} UIntBytesIdentity(val:nat, size:nat)
    requires val < Pow256(size)
    ensures UIntFromBytes(UIntToBytes(val, size)) == val
{
}

// Finally, need to verify that converting data to bytes and back again doesn't change
// it whatsoever
// lemma {:opaque} ToBytesIdentity(data:Data)
//     requires !data.Ptr?
//     requires ValidData(data)
//     ensures FromBytes(ToBytes(data), data) == data
// {
//     if (data.Bytes?) {
//         assert FromBytes(ToBytes(data), data) == data;
//     } else {
//         assert data.Int?;
//         if (data.signed) {
//             if (data.size == 1) {
//                 assert FromBytes(ToBytes(data), data) == data;
//             } else {
//                 assert FromBytes(ToBytes(data), data) == data;
//             }
//         } else {
//             if (data.size == 1) {
//                 assert FromBytes(ToBytes(data), data) == data;
//             } else {
//                 assert FromBytes(ToBytes(data), data) == data;
//             }
//         }
//     }
// }

datatype Value = Val8(v8:uint8) | Val16(v16:uint16) | Val32(v32:uint32) | Val64(v64:uint64) | ValBool(vBool:bool)
                | SVal8(sv8:sint8) | SVal16(sv16:sint16) | SVal32(sv32:sint32) | SVal64(sv64:sint64) 


predicate unsignedVal(v:Value)
{
    v.Val8? || v.Val16? || v.Val32? || v.Val64?
}
predicate signedVal(v:Value)
{
    v.SVal8? || v.SVal16? || v.SVal32? || v.SVal64? 
}
predicate boolVal(v:Value)
{
    v.ValBool? 
}

predicate unsignedValLT(v0:Value,v1:Value)
    requires unsignedVal(v0)
    requires unsignedVal(v1)
{
    &&(v0.Val8?   ==>  v1.Val8? || v1.Val16? || v1.Val32? || v1.Val64?)
    &&(v0.Val16?  ==> v1.Val16? || v1.Val32? || v1.Val64?)
    &&(v0.Val32?  ==> v1.Val32? || v1.Val64?)
    &&(v0.Val64?  ==> v1.Val64?)
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

    predicate typesMatch(v0:Value,v1:Value)
    {
        (v0.Val8? ==> v1.Val8? )
        && (v0.Val16? ==> v1.Val16?)
        && (v0.Val32? ==> v1.Val32? )
        && (v0.Val64? ==> v1.Val64? )
        && (v0.ValBool? ==> !v1.ValBool? )
    }

} // end module types
