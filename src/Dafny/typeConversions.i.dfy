include "ops.dfy"
include "types.dfy"

module type_conversion {
    import opened ops
    import opened types



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
        src
    }

    function evalSEXT(t0:Value,src:Value,t1:Value): Value
        requires typesMatch(t0,src)
        requires signedVal(src)
        requires signedVal(t1)
        requires signedValLT(src,t1)
    {
        if t1.SVal8? then evalSEXT8Helper(src) else 
        if t1.SVal16? then evalSEXT16Helper(src) else 
        if t1.SVal32? then evalSEXT32Helper(src) else 
        if t1.SVal64? then evalSEXT64Helper(src) else src
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
    
    function evalSEXT8Helper(src:Value) : Value
    {
       src
    }

    function evalSEXT16Helper(src:Value) : Value
    {
        if src.SVal8? then SVal16(SignedBitwise8CastTo16(src.sv8)) else src
    }

    function evalSEXT32Helper(src:Value) : Value
    {
        if src.SVal8? then SVal32(SignedBitwise8CastTo32(src.sv8)) else 
        if src.SVal16? then SVal32(SignedBitwise16CastTo32(src.sv16)) else src 
    }

    function evalSEXT64Helper(src:Value) : Value
    {
        if src.SVal8? then SVal64(SignedBitwise8CastTo64(src.sv8)) else 
        if src.SVal16? then SVal64(SignedBitwise16CastTo64(src.sv16)) else
        if src.SVal32? then SVal64(SignedBitwise32CastTo64(src.sv32)) else src
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

////----SIGNED----////

function {:opaque} SignedBitwise8CastTo16(x:sint8):sint16
{
    x  % 0x8000
}
function {:opaque} SignedBitwise8CastTo32(x:sint8):sint32
{
    x  % 0x80000000
}
function {:opaque} SignedBitwise16CastTo32(x:sint16):sint32
{
    x  % 0x80000000
}
function {:opaque} SignedBitwise8CastTo64(x:sint8):sint64
{
    x  % 0x8000000000000000
}
function {:opaque} SignedBitwise16CastTo64(x:sint16):sint64
{
    x  % 0x8000000000000000
}
function {:opaque} SignedBitwise32CastTo64(x:sint32):sint64
{
    x  % 0x8000000000000000
}


}
