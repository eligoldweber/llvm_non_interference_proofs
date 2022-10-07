include "ops.dfy"
include "types.s.dfy"
include "Maps.i.dfy"

module simple_memory {
    import opened ops
    import opened Collections__Maps_i
    import opened types

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
    
    predicate alloca(m:memmap,m':memmap)
    {
        |m| + 1 == |m'|
        && forall adr:addr :: adr in m ==> adr in m'
    }
    

    predicate load(m:memmap,m':memmap)
    {
        m == m'
    }

    method loadMem(m:memmap,adr:addr) returns (mc:memoryCell)
        requires adr in m;
    {
        mc := m[adr];
    }

    
    predicate store(m:memmap, adr:addr, mc:memoryCell ,m':memmap)
    {
        adr !in m ==> |m| + 1 == |m'|
        && adr in m ==> |m| == |m'|
        && m' == m[adr := mc]
    }
}
