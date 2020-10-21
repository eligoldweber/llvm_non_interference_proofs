include "ops.dfy"
include "types.dfy"

module type_conversion {
    import opened ops



    function evalZEXT(t0:Value,src:Value,t1:Value): Value
        requires typesMatch(t0,src)
        requires unsignedVal(src)
        requires unsignedVal(t1)
        requires unsignedValLT(src,t1)
    {
        if t1.Val8? then evalZEXT8Helper(src) else 
        if t1.Val16? then evalZEXT16Helper(src) else 
        if t1.Val32? then evalZEXT32Helper(src) else 
        if t1.Val64? then evalZEXT64Helper(src) else 
        if t1.Val128? then evalZEXT128Helper(src) else 
        src
    }

    function evalZEXT8Helper(src:Value) : Value
    {
       src
    }

    function evalZEXT16Helper(src:Value) : Value
    {
        if src.Val8? then Val16(Bitwise8CastTo16(src.v8)) else src
    }

    function evalZEXT32Helper(src:Value) : Value
    {
        if src.Val8? then Val32(Bitwise8CastTo32(src.v8)) else 
        if src.Val16? then Val32(Bitwise16CastTo32(src.v16)) else src 
    }

    function evalZEXT64Helper(src:Value) : Value
    {
        if src.Val8? then Val64(Bitwise8CastTo64(src.v8)) else 
        if src.Val16? then Val64(Bitwise16CastTo64(src.v16)) else
        if src.Val32? then Val64(Bitwise32CastTo64(src.v32)) else src
    }

    function evalZEXT128Helper(src:Value) : Value
    {
        if src.Val8? then Val128(Bitwise8CastTo128(src.v8)) else 
        if src.Val16? then Val128(Bitwise16CastTo128(src.v16)) else
        if src.Val32? then Val128(Bitwise32CastTo128(src.v32)) else
        if src.Val64? then Val128(Bitwise64CastTo128(src.v64)) else src
    }


///// Cast functions /////

////----UNSIGNED----////

//
function {:opaque} Bitwise8CastTo16(x:uint8):uint16
{
    x  % 0x1000
}
//
function {:opaque} Bitwise8CastTo32(x:uint8):uint32
{
    x  % 0x1_0000_0000
}
function {:opaque} Bitwise16CastTo32(x:uint16):uint32
{
    x  % 0x1_0000_0000
}
//
function {:opaque} Bitwise8CastTo64(x:uint8):uint64
{
    x  % 0x1_0000_0000_0000_0000
}
function {:opaque} Bitwise16CastTo64(x:uint16):uint64
{
    x  % 0x1_0000_0000_0000_0000
}
function {:opaque} Bitwise32CastTo64(x:uint32):uint64
{
    x  % 0x1_0000_0000_0000_0000
}
//
function {:opaque} Bitwise8CastTo128(x:uint8):uint128
{
    x  % 0x1_00000000_00000000_00000000_00000000
}
function {:opaque} Bitwise16CastTo128(x:uint16):uint128
{
    x  % 0x1_00000000_00000000_00000000_00000000
}
function {:opaque} Bitwise32CastTo128(x:uint32):uint128
{
    x  % 0x1_00000000_00000000_00000000_00000000
}
function {:opaque} Bitwise64CastTo128(x:uint64):uint128
{
    x  % 0x1_00000000_00000000_00000000_00000000
}

////----SIGNED----////

function {:opaque} SignedBitwise8CastTo16(x:sint8):sint16
{
    x  % 0x8000
}



}