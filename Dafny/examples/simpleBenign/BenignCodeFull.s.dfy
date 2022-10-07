include "../../LLVM/llvmREFACTOR_Multi.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"

module simpleBenignCodeFull{
    import opened control_flow
    import opened LLVM_defRE_Multi
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory

    

    /////////////////////////////////////////////////////////////////////////


    function return_():codeRe
    {
        var return_ := Block([Ins(RET(D(Void)))]);

        return_
    }

    // function if_end4():codeRe
    // {

    //      var if_end4 := Block([Ins(LOAD(var_s,4,var_x)),
    //                            Ins(CALL(D(Void),printf_code(global_str1()).block)),
    //                           return_()]);

    //         if_end4
    // }

    // function if_then3():codeRe
    // {
    //     var if_end4 := Block([Ins(LOAD(var_s,4,var_x)),
    //                            Ins(CALL(D(Void),printf_code(global_str1()).block)),
    //                           return_()]);

    //     // var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
    //     //                        Ins(UNCONDBR(if_end4()))]);
    //     var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
    //                            if_end4]);

    //         if_then3
    // }

    // function benign_patch_SOI(s:state):codeRe
    //     requires SOI_ASSIMPTIONS(s)
    // {   

    //     var var_cmp2 := LV(" var_cmp2 ");
    //     var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

    //     //var if_end := Block([
    //     //Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
    //     //Ins(BR(var_cmp2,if_then3(),if_end4()))]);

    //      var if_end4 := Block([Ins(LOAD(var_s,4,var_x)),
    //                            Ins(CALL(D(Void),printf_code(global_str1()).block)),
    //                           return_()]);

    //     // var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
    //     //                        Ins(UNCONDBR(if_end4()))]);
    //     var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
    //                            if_end4]);


    //     var if_end := Block([
    //     Ins(ICMP(var_cmp2,ugt,4,var_0,D(Int(0,IntType(4,false))))),
    //     IfElse(var_cmp2,if_then3.block,if_end4.block)]); // fix

    //     if_end

    //     // ASSUMPTIONS (ENGLISH)
    //     // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
    // }

    // function benign_vuln_SOI(s:state):codeRe
    //     requires SOI_ASSIMPTIONS(s)
    // {

    //      var var_cmp2 := LV(" var_cmp2 ");
    //     var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

    //     var if_end := Block([
    //     Ins(ICMP(var_cmp2,sgt,4,var_0,D(Int(0,IntType(4,false))))),
    //     IfElse(var_cmp2,if_then3().block,if_end4().block)]); // fix

    //     if_end

    //     // ASSUMPTIONS (ENGLISH)
    //     // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
    // }


    function MergedTest(var_x:operand,s:state,patched:bool):codeRe
        requires SOI_ASSIMPTIONS(s)
        requires ValidOperand(s,var_x);
        requires isInt(OperandContents(s,var_x))
        requires OperandContents(s,var_x).itype.size == 4;
        requires !OperandContents(s,var_x).itype.signed

        requires OperandContents(s,var_x).val == 2 ==> patched
        
    {
        var var_cmp := LV(" var_cmp ");
        var var_cmp1 := LV(" var_cmp1 ");
        var var_cmp2 := LV(" var_cmp2 ");
        var var_2 := LV(" var_2 ");
        var var_add := LV(" var_add ");
                // var var_sub := LV(" var_sub ");
        var var_sub := D(Int(0,IntType(4,false)));
                var var_add6 := D(Int(0,IntType(4,false)));

        var var_z := LV(" var_z ");
        var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

        var if_end4 := Block([Ins(SUB(var_sub,4,var_add,D(Int(3,IntType(4,false))))),
                              Ins(CALL(D(Void),printf_code(Bytes(concatBytes(global_str1().bytes,IntToBytes(var_sub.d)))).block)),
                              NonImpactIns(ADD(var_add6,4,D(Int(4,IntType(4,false))),D(Int(99,IntType(4,false))))),
                              NonImpactIns(CALL(D(Void),printf_code(Bytes(concatBytes(global_str2().bytes,IntToBytes(var_add6.d)))).block)),
                              return_()]);

        var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
                               if_end4]);


        var if_end := Block([Ins(ADD(var_add,4,var_x,D(Int(2147483646,IntType(4,false))))),
        Divergence([Ins(ICMP(var_cmp2,sgt,4,var_add,D(Int(0,IntType(4,false)))))], [Ins(ICMP(var_cmp2,ugt,4,var_add,D(Int(0,IntType(4,false)))))],patched),
        IfElse(var_cmp2,if_then3.block,if_end4.block)]);

        var if_then := Block([return_()]);


        // lor.lhs.false:                                    ; preds = %entry
        //     %cmp1 = icmp sgt i32 %x, 2
        //     br i1 %cmp1, label %if.then, label %if.end

        var lor_lhs_false :=  Block([Ins(ICMP(var_cmp1,sgt,4,var_x,D(Int(2,IntType(4,false))))),
                              IfElse(var_cmp1,if_then.block,if_end.block)]);

        // entry:
        //     %z = alloca i32, align 4
        //     %cmp = icmp slt i32 %x, 0
        //     br i1 %cmp, label %if.then, label %lor.lhs.false
        var entry :=  Block([Ins(ICMP(var_cmp,slt,4,var_x,D(Int(0,IntType(4,false))))),
                      IfElse(var_cmp,if_then.block,lor_lhs_false.block)]);

        entry

        // ASSUMPTIONS (ENGLISH)
        // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
    }



    predicate SOI_ASSIMPTIONS(s:state)
    {
        var var_0 := LV("var_0"); // z
        ValidState(s)
        && ValidOperand(s,var_0)
        && s.o.Nil?
        && s.lvs["var_0"].Int?
        && s.lvs["var_0"].val >= 2147483646
        && s.lvs["var_0"].val <= 2147483648
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

    function global_str2():Data
    {
       // "done" 
       var str2:Bytes := [0x61, 0x20, 0x3D, 0x0A];
        // var str2:Bytes := concatBytes([0x61, 0x20, 0x3D, 0x0A], IntToBytes((Int(4,IntType(4,false)))));
        Bytes(str2)
    }



    function printf_code(o:Data):codeRe
    {
        Block([Ins(VISIBLE_OUT(Out(o)))])
    }

}


// function benign_vuln_SOI(s:state):codeRe
//         requires SOI_ASSIMPTIONS(s)
//     {

//         var var_cmp2 := LV(" var_cmp2 ");
//         var var_0:operand :| var_0.LV? && var_0.l in s.lvs && var_0.l == "var_0";

//         var return_ := Block([Ins(RET(D(Void)))]);

//         var if_end4 := Block([Ins(CALL(D(Void),printf_code(global_str1()).block)),
//         Ins(UNCONDBR(return_))]);

//         var if_then3 := Block([Ins(CALL(D(Void),printf_code(global_str()).block)),
//         Ins(UNCONDBR(if_end4))]);

//         var if_end := Block([
//         Ins(ICMP(var_cmp2,sgt,4,var_0,D(Int(0,IntType(4,false))))),
//         Ins(BR(var_cmp2,if_then3,if_end4))]);

//         if_end

//         // ASSUMPTIONS (ENGLISH)
//         // var_0 has the value of x :: MAX_INT-1 >= x && x < MAX_INT+1
//     }