include "ops.dfy"
include "types.dfy"
include "Maps.i.dfy"

module simple_memory {
    import opened ops
    import opened Collections__Maps_i

    type ptr = uint32
    datatype addr = ptr | NULL

    datatype mb = Mb(sz:int, b:byte)
    datatype mptr = Mptr(blk:string,ofs:int,idx:int)
    datatype munit = addr
    datatype memoryCell = mb | mptr | munit

    type memmap = map<addr, memoryCell>
    
    function{:axiom} TheValidAddresses(): set<addr>
    predicate{:opaque} ValidMemState(s:memmap)
    {
        // regular mem
        (forall m:addr :: m in TheValidAddresses() <==> m in s)    
    }
    
    // predicate alloca(m:memmap,m':memmap)
    // {

    // }
    
    // predicate load(m:memmap,m':memmap)
    // {

    // }
    
    predicate store(m:memmap, adr:addr, mc:memoryCell ,m':memmap)
    {
        adr !in m ==> |m| + 1 == |m'|
        && adr in m ==> |m| == |m'|
        && m' == m[adr := mc]
    }
}