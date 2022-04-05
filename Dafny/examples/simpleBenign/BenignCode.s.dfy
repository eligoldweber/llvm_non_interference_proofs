include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"

module simpleBenignCode{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory

    predicate validStartingState(s:state)
    {
        var var_z := LV(" var_z ");
        var var_cmp := LV(" var_cmp ");
        var var_cmp1 := LV(" var_cmp1 ");
        var var_add := LV(" var_add ");
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0 := LV(" var_0 ");

        && "var_z" in s.lvs
        && "var_cmp" in s.lvs
        && "var_cmp1" in s.lvs
        && "var_add" in s.lvs
        && "var_cmp2" in s.lvs
        && "var_0" in s.lvs
    }

    function benign_patch_code(var_x:operand):codeRe
    {

        var var_z := LV(" var_z ");
        var var_cmp := LV(" var_cmp ");
        var var_cmp1 := LV(" var_cmp1 ");
        var var_add := LV(" var_add ");
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0 := LV(" var_0 ");

        var return_ := Block([Ins(RET(D(Void)))]);

        var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
        Ins(UNCONDBR(return_))]);

        var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
        Ins(UNCONDBR(if_end4))]);

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

    function benign_vuln_code(var_x:operand):codeRe
    {

        var var_z := LV(" var_z ");
        var var_cmp := LV(" var_cmp ");
        var var_cmp1 := LV(" var_cmp1 ");
        var var_add := LV(" var_add ");
        var var_cmp2 := LV(" var_cmp2 ");
        var var_0 := LV(" var_0 ");

        var return_ := Block([Ins(RET(D(Void)))]);

        var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
        Ins(UNCONDBR(return_))]);

        var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
        Ins(UNCONDBR(if_end4))]);

        var if_end := Block([Ins(ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false))))),
        Ins(STORE(var_add,var_z)),
        Ins(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false))))),
        Ins(BR(var_cmp2,if_then3,if_end4))]);

        var if_then := Block([Ins(UNCONDBR(return_))]);

        var lor_lhs_false := Block([Ins(ICMP(var_cmp1,sgt,4,var_x,D(Int(2,IntType(4,false))))),
        Ins(BR(var_x,if_then,if_end))]);

        var entry := Block([Ins(ALLOCA(var_z,4)),
        Ins(ICMP(var_cmp,slt,4,var_x,D(Int(0,IntType(4,false))))),
        Ins(BR(var_x,if_then,lor_lhs_false))]);

        entry
    }
    function benign_vuln_SOI(s:state):codeRe
        requires SOI_ASSIMPTIONS(s)
    {

        var var_cmp2 := LV(" var_cmp2 ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

        var return_ := Block([Ins(RET(D(Void)))]);

        var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
        Ins(UNCONDBR(return_))]);

        var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
        Ins(UNCONDBR(if_end4))]);

        var if_end := Block([
        Ins(ICMP(var_cmp2,sgt,4,var_0,D(Int(0,IntType(4,false))))),
        Ins(BR(var_cmp2,if_then3,if_end4))]);

        if_end

        // ASSUMPTIONS (ENGLISH)
        // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
    }

    function return_():codeRe
    {
        var return_ := Block([Ins(RET(D(Void)))]);

        return_
    }

    function if_end4():codeRe
    {
        // var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
        //                       Ins(UNCONDBR(return_()))]);
         var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
                              return_()]);

            if_end4
    }

    function if_then3():codeRe
    {
        // var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
        //                        Ins(UNCONDBR(if_end4()))]);
        var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
                               if_end4()]);

            if_then3
    }

    function benign_patch_SOI(s:state):codeRe
        requires SOI_ASSIMPTIONS(s)
    {   

        var var_cmp2 := LV(" var_cmp2 ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

        //var if_end := Block([
        //Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        //Ins(BR(var_cmp2,if_then3(),if_end4()))]);
        var if_end := Block([
        Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
        IfElse(true,if_then3().block,if_end4().block)]); // fix

        if_end

        // ASSUMPTIONS (ENGLISH)
        // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
    }

    predicate SOI_ASSIMPTIONS(s:state)
    {
        var var_0 := LV("var_0");
        ValidState(s)
        && ValidOperand(s,var_0)
        && s.lvs["var_0"].Int?
        && s.lvs["var_0"].val >= 2147483646
        && s.lvs["var_0"].val < 2147483648
        && s.lvs["var_0"].itype.size == 4
        && !s.lvs["var_0"].itype.signed
    }




    function global_str():Data
    {
       // "z is positive" 
        var str:Bytes := [0x7a, 0x20, 0x69, 0x73, 0x20, 0x70, 0x6f, 0x73, 0x69, 0x74, 0x69, 0x76, 0x65];
        Bytes(str)
    }

    function global_str1():Data
    {
       // "done" 
        var str1:Bytes := [0x64, 0x6f, 0x6e, 0x65];
        Bytes(str1)
    }



    function printf_code(o:Data):codeRe
    {
        Block([Ins(VISIBLE_OUT(Out(o)))])
    }

}