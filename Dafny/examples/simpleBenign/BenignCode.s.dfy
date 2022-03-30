include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"

module challenge6Code{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory


    function challenge_7_transport_handler_code():codeRe
    {



var var_z := LV(" var_z ");
var var_cmp := LV(" var_cmp ");
var var_x := LV(" var_x ");
var var_cmp1 := LV(" var_cmp1 ");
var var_add := LV(" var_add ");
var var_cmp2 := LV(" var_cmp2 ");
var var_0 := LV(" var_0 ");

var return_ := Block([Ins(RET(D(Void)))]);

var if_end4 := Block([Ins(UNCONDBR(return_))]);

var if_then3 := Block([Ins(UNCONDBR(if_end4))]);

var if_end := Block([Ins(ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false))))),
Ins(STORE(var_add,var_z)),
Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
Ins(BR(var_0,if_then3,if_end4))]);

var if_then := Block([Ins(UNCONDBR(return_))]);

var lor_lhs_false := Block([Ins(ICMP(var_cmp1,sgt,4,var_x,D(Int(2,IntType(4,false))))),
Ins(BR(var_x,if_then,if_end))]);

var entry := Block([Ins(ALLOCA(var_z,4)),
Ins(ICMP(var_cmp,slt,4,var_x,D(Int(0,IntType(4,false))))),
Ins(BR(var_x,if_then,lor_lhs_false))]);

entry
    }

}