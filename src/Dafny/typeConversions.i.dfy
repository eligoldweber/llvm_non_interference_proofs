include "ops.dfy"
include "types.dfy"

module type_conversion {
    import opened ops



    function evalSEXT(t0:Value,src:Value,t1:Value): Value
        requires typesMatch(t0,src)
    {
        
        if t1.Val8? then evalSEXT8Helper(src) else 
        if t1.Val16? then evalSEXT16Helper(src) else 
        if t1.Val32? then evalSEXT32Helper(src) else 
        if t1.Val64? then evalSEXT64Helper(src) else 
        if t1.Val128? then evalSEXT128Helper(src) else 
        src
    }

    function evalSEXT8Helper(src:Value) : Value
    {
        if src.Val8? then src else 
        if src.Val16? then Val8(Bitwise16CastTo8(src.v16)) else
        if src.Val32? then Val8(Bitwise32CastTo8(src.v32)) else
        if src.Val64? then Val8(Bitwise64CastTo8(src.v64)) else
        if src.Val64? then Val8(Bitwise128CastTo8(src.v128)) else 
                            src
    }

    function evalSEXT16Helper(src:Value) : Value
    {
        if src.Val8? then Val16(Bitwise8CastTo16(src.v8)) else 
        if src.Val16? then src else
        if src.Val32? then Val16(Bitwise32CastTo16(src.v32)) else
        if src.Val64? then Val16(Bitwise64CastTo16(src.v64)) else
        if src.Val64? then Val16(Bitwise128CastTo16(src.v128)) else 
                            src
    }

    function evalSEXT32Helper(src:Value) : Value
    {
        if src.Val8? then Val32(Bitwise8CastTo32(src.v8)) else 
        if src.Val16? then Val32(Bitwise16CastTo32(src.v16)) else
        if src.Val32? then src else
        if src.Val64? then Val32(Bitwise64CastTo32(src.v64)) else
        if src.Val64? then Val32(Bitwise128CastTo32(src.v128)) else 
                            src
    }

    function evalSEXT64Helper(src:Value) : Value
    {
        if src.Val8? then Val64(Bitwise8CastTo64(src.v8)) else 
        if src.Val16? then Val64(Bitwise16CastTo64(src.v16)) else
        if src.Val32? then Val64(Bitwise32CastTo64(src.v32)) else
        if src.Val64? then src else
        if src.Val128? then Val64(Bitwise128CastTo64(src.v128)) else 
                            src
    }

    function evalSEXT128Helper(src:Value) : Value
    {
        if src.Val8? then Val128(Bitwise8CastTo128(src.v8)) else 
        if src.Val16? then Val128(Bitwise16CastTo128(src.v16)) else
        if src.Val32? then Val128(Bitwise32CastTo128(src.v32)) else
        if src.Val64? then Val128(Bitwise64CastTo128(src.v64)) else 
                            src
    }
}