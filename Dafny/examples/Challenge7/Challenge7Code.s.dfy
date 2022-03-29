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


var var_read_frame_sroa_4122_8_extract_trunc := LV(" var_read_frame_sroa_4122_8_extract_trunc ");
var var_read_frame_coerce1 := LV(" var_read_frame_coerce1 ");
var var_read_frame_sroa_8_8_extract_shift := LV(" var_read_frame_sroa_8_8_extract_shift ");
var var_read_frame_sroa_8_8_extract_trunc := LV(" var_read_frame_sroa_8_8_extract_trunc ");
var var_read_frame_sroa_10_8_extract_shift := LV(" var_read_frame_sroa_10_8_extract_shift ");
var var_read_frame_sroa_10_8_extract_trunc := LV(" var_read_frame_sroa_10_8_extract_trunc ");
var var_read_frame_sroa_11_8_extract_shift := LV(" var_read_frame_sroa_11_8_extract_shift ");
var var_read_frame_sroa_11_8_extract_trunc := LV(" var_read_frame_sroa_11_8_extract_trunc ");
var var_read_frame_sroa_12_8_extract_shift := LV(" var_read_frame_sroa_12_8_extract_shift ");
var var_read_frame_sroa_12_8_extract_trunc := LV(" var_read_frame_sroa_12_8_extract_trunc ");
var var_conv := LV(" var_conv ");
var var_read_frame_coerce0 := LV(" var_read_frame_coerce0 ");
var var_and2126 := LV(" var_and2126 ");
var var_0 := LV(" var_0 ");
var var_cmp := LV(" var_cmp ");
var var_current_sa := LV(" var_current_sa ");

var entry := Block([Ins(TRUNC(var_read_frame_sroa_4122_8_extract_trunc,8,var_read_frame_coerce1,1)),
Ins(LSHR(var_read_frame_sroa_8_8_extract_shift,var_read_frame_coerce1,D(Int(8,IntType(8,false))))),
Ins(TRUNC(var_read_frame_sroa_8_8_extract_trunc,8,var_read_frame_sroa_8_8_extract_shift,2)),
Ins(LSHR(var_read_frame_sroa_10_8_extract_shift,var_read_frame_coerce1,D(Int(24,IntType(8,false))))),
Ins(TRUNC(var_read_frame_sroa_10_8_extract_trunc,8,var_read_frame_sroa_10_8_extract_shift,1)),
Ins(LSHR(var_read_frame_sroa_11_8_extract_shift,var_read_frame_coerce1,D(Int(32,IntType(8,false))))),
Ins(TRUNC(var_read_frame_sroa_11_8_extract_trunc,8,var_read_frame_sroa_11_8_extract_shift,1)),
Ins(LSHR(var_read_frame_sroa_12_8_extract_shift,var_read_frame_coerce1,D(Int(40,IntType(8,false))))),
Ins(TRUNC(var_read_frame_sroa_12_8_extract_trunc,8,var_read_frame_sroa_12_8_extract_shift,4)),
Ins(TRUNC(var_conv,8,var_read_frame_coerce0,1)),
Ins(LSHR(var_and2126,var_read_frame_coerce0,D(Int(8,IntType(8,false))))),
Ins(TRUNC(var_0,8,var_and2126,1)),
Ins(ICMP(var_cmp,eq,1,var_0,var_current_sa))]);




        entry
    }

}