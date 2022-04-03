include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"

module challenge7Code{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory


    function challenge_7_transport_handler_code_vuln():codeRe
    {


var var_20 := LV(" var_20 ");
var var_read_frame_coerce1 := LV(" var_read_frame_coerce1 ");
var var_conv78 := LV(" var_conv78 ");
var var_num_packets88 := LV(" var_num_packets88 ");
var var_23 := LV(" var_23 ");
var var_conv89 := LV(" var_conv89 ");
var var_cmp90 := LV(" var_cmp90 ");

var if_end93 := Block([Ins(RET(D(Void)))]);

var if_end122 := Block([Ins(RET(D(Void)))]);

var if_then92 := Block([Ins(UNCONDBR(if_end122))]);

var entry := Block([Ins(TRUNC(var_20,8,var_read_frame_coerce1,4)),
Ins(AND(var_conv78,var_20,D(Int(255,IntType(4,false))))),
Ins(LOAD(var_23,1,var_num_packets88)),
Ins(ZEXT(var_conv89,4,var_23,4)),
Ins(ICMP(var_cmp90,ugt,4,var_conv78,var_conv89)),
Ins(BR(var_conv78,if_then92,if_end93))]);

entry
    }

       function challenge_7_transport_handler_code_patch():codeRe
    {
        //placeholder
        Block([CNil])
    }

}