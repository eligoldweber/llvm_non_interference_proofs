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
var var_if_then := LV(" var_if_then ");
var var_lor_lhs_false := LV(" var_lor_lhs_false ");
var var_cmp1 := LV(" var_cmp1 ");
var var_if_end := LV(" var_if_end ");
var var_add := LV(" var_add ");
var var_0 := LV(" var_0 ");
var var_cmp2 := LV(" var_cmp2 ");
var var_if_then3 := LV(" var_if_then3 ");
var var_if_end4 := LV(" var_if_end4 ");

var entry := Block([Ins(ALLOCA(var_z)),
Ins(ICMP(var_cmp,slt,4,var_x,D(Int(0,IntType(4,false))))),
Ins(BR(var_cmp,var_if_then,var_lor_lhs_false))]);

var lor_lhs_false := Block([Ins(ICMP(var_cmp1,sgt,4,var_x,D(Int(2,IntType(4,false))))),
Ins(BR(var_cmp1,var_if_then,var_if_end))]);




        entry
    }

}