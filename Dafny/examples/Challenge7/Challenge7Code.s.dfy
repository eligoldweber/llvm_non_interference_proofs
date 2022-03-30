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
        var var_src := LV(" var_src ");
        var var_and2126 := LV(" var_and2126 ");
        var var_0 := LV(" var_0 ");
        var var_cmp := LV(" var_cmp ");
        var var_current_sa := LV(" var_current_sa ");
        var var_read_frame_sroa_0_0_extract_trunc := LV(" var_read_frame_sroa_0_0_extract_trunc ");
        var var_and6 := LV(" var_and6 ");
        var var_Pivot := LV(" var_Pivot ");
        var var_SwitchLeaf2 := LV(" var_SwitchLeaf2 ");
        var var_SwitchLeaf := LV(" var_SwitchLeaf ");
        var var_Pivot9 := LV(" var_Pivot9 ");
        var var_SwitchLeaf7 := LV(" var_SwitchLeaf7 ");
        var var_SwitchLeaf5 := LV(" var_SwitchLeaf5 ");



        var if_end111 := Block([Ins(RET(D(Void)))]);

        var sw_bb54 := Block([Ins(UNCONDBR(if_end111))]);

        var sw_bb45 := Block([Ins(UNCONDBR(if_end111))]);

        var if_else := Block([Ins(UNCONDBR(if_end111))]);

        var NewDefault3 := Block([Ins(UNCONDBR(if_end111))]);

        var NewDefault := Block([Ins(UNCONDBR(if_end111))]);

        var LeafBlock4 := Block([Ins(ICMP(var_SwitchLeaf5,eq,1,var_read_frame_sroa_4122_8_extract_trunc,D(Int(16,IntType(1,false))))),
        Ins(BR(var_read_frame_sroa_4122_8_extract_trunc,if_else,NewDefault3))]);

        var LeafBlock6 := Block([Ins(ICMP(var_SwitchLeaf7,eq,1,var_read_frame_sroa_4122_8_extract_trunc,D(Int(19,IntType(1,false))))),
        Ins(BR(var_read_frame_sroa_4122_8_extract_trunc,sw_bb45,NewDefault3))]);

        var NodeBlock8 := Block([Ins(ICMP(var_Pivot9,slt,1,var_read_frame_sroa_4122_8_extract_trunc,D(Int(19,IntType(1,false))))),
        Ins(BR(var_read_frame_sroa_4122_8_extract_trunc,LeafBlock4,LeafBlock6))]);

        var sw_bb := Block([Ins(UNCONDBR(NodeBlock8))]);

        var LeafBlock := Block([Ins(ICMP(var_SwitchLeaf,eq,4,var_and6,D(Int(15400960,IntType(4,false))))),
        Ins(BR(var_and6,sw_bb54,NewDefault))]);

        var LeafBlock1 := Block([Ins(ICMP(var_SwitchLeaf2,eq,4,var_and6,D(Int(15466496,IntType(4,false))))),
        Ins(BR(var_and6,sw_bb,NewDefault))]);

        var NodeBlock := Block([Ins(ICMP(var_Pivot,slt,4,var_and6,D(Int(15466496,IntType(4,false))))),
        Ins(BR(var_and6,LeafBlock,LeafBlock1))]);

        var if_then := Block([Ins(TRUNC(var_read_frame_sroa_0_0_extract_trunc,8,var_read_frame_coerce0,4)),
        Ins(AND(var_and6,var_read_frame_sroa_0_0_extract_trunc,D(Int(16711680,IntType(4,false))))),
        Ins(UNCONDBR(NodeBlock))]);

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
        Ins(STORE(var_conv,var_src)),
        Ins(LSHR(var_and2126,var_read_frame_coerce0,D(Int(8,IntType(8,false))))),
        Ins(TRUNC(var_0,8,var_and2126,1)),
        Ins(ICMP(var_cmp,eq,1,var_0,var_current_sa)),
        Ins(BR(var_0,if_then,if_end111))]);

        entry
    }

       function challenge_7_transport_handler_code_patch():codeRe
    {
        //placeholder
        Block([CNil])
    }

}