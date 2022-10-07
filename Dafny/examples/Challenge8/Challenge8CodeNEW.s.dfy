include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"


module challenge8CodeNEW{
    import opened control_flow
    import opened LLVM_def_NEW
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory


// function challenge_8_transport_handler_create_conn_vuln():codeRe {
//     Block([prefixCode(), Block([CNil]),postfixCode()])
// }

function allVariablesConfig():Configuration
{
    var var_11 := LV("var_11");
    var var_num_packets := LV("var_num_packets");
    var var_conv15 := LV("var_conv15");
    var var_12 := LV("var_12");
    var var_size_addr := LV("var_size_addr");
    var var_conv16 := LV("var_conv16");
    var var_div := LV("var_div");
    var var_cmp17 := LV("var_cmp17");
    var var_call20 := LV("var_call20");
    var var_retval := LV("var_retval");
    var var_26 := LV("var_26");
    var var_size := LV("var_size");
    Config(map["var_11" := var_11,
            "var_num_packets" := var_num_packets,
            "var_conv15" := var_conv15,
            "var_12" := var_12,
            "var_size_addr" := var_size_addr,
            "var_conv16" := var_conv16,
            "var_div" := var_div,
            "var_cmp17" := var_cmp17,
            "var_call20" := var_call20,
            "var_retval" := var_retval,
            "var_26" := var_26,
            "var_size" := var_size])
}

predicate validConfig(s:State)
    requires ValidState(s)
{
    var c := allVariablesConfig();
    && (forall op :: op in c.ops ==> 
        && c.ops[op].LV? 
        && c.ops[op].l in s.lvs
        && ValidOperand(s,c.ops[op]))
    && "var_11" in c.ops
    && "var_num_packets" in c.ops
    && "var_conv15" in c.ops
    && "var_12" in c.ops
    && "var_size_addr" in c.ops
    && "var_size" in c.ops
    && "var_conv16" in c.ops
    && "var_div" in c.ops
    && "var_cmp17" in c.ops
    && "var_call20" in c.ops
    && "var_retval" in c.ops
    && "var_26" in c.ops
    && s.lvs["var_11"].Ptr?
    && s.lvs["var_num_packets"].Int?
    && s.lvs["var_size"].Int?
    && s.lvs["var_conv15"].Int?
    && s.lvs["var_12"].Ptr?
    && s.lvs["var_size_addr"].Int?
    && s.lvs["var_conv16"].Int?
    && s.lvs["var_div"].Int?
    && s.lvs["var_cmp17"].Int?
    && s.lvs["var_call20"].Int?
    && s.lvs["var_retval"].Ptr?
    && s.lvs["var_26"].Int?
    && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].mb? 
    && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].size == 1
    // assumption becasue skipping alloc step
}

function challenge_8_transport_handler_create_conn_vuln_test():seq<Code> {
    [prefixCode(), Block([CNil]),postfixCode()]
}

function challenge_8_transport_handler_create_conn_vuln_postfix_simple(size:Operand):seq<Code> 
    requires size.D?;
    requires size.d.Int?;
    requires size.d.itype == IntType(4,false);
{
    [prefixCode(), Block([CNil]),postfixCodeSimple()]
}

function prefixCode():Code{
    Block([CNil])
}

function postfixCode():Code{
    Block([CNil])
}

function postfixCodeSimple():Code{

    var config := allVariablesConfig();

    Block([Ins(STORE(D(Int(1,IntType(1,false))),config.ops["var_retval"])),
    Ins(LOAD(config.ops["var_26"],1,config.ops["var_retval"])),
    Ins(RET(config.ops["var_26"]))])
}

function return_():Code{
    var config := allVariablesConfig();
    
    var return_ := 
    Block(
        [Ins(LOAD(config.ops["var_26"],1,config.ops["var_retval"])),
        Ins(RET(config.ops["var_26"]))]);
    
    return_

}


function if_then19():Code {
        // 
    var config := allVariablesConfig();
    var if_then19 := Block([Ins(CALL(D(Void),delete_connection())),
    Ins(STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"])),
    return_()]); // UNCONDBR is just converted to Block
    if_then19
}

function patch_block(size:Operand):Code
    requires size.D?;
    requires size.d.Int?;
    requires size.d.itype == IntType(4,false);
{
        var config := allVariablesConfig();

    // var patch_block := Block([Ins(LOAD(var_11,1,var_num_packets)),
    // Ins(ZEXT(var_conv15,1,var_11,4)),
    // Ins(LOAD(var_12,2,var_size_addr)),
    // Ins(ZEXT(var_conv16,2,var_12,4)),
    // Ins(SDIV(var_div,var_conv16,D(Int(7,IntType(4,false))))),
    // Ins(ICMP(var_cmp17,sgt,4,var_conv15,var_div)),
    // Ins(BR(var_cmp17,if_then19,postfix))]);

    
    var patch_block := Block(
        [Ins(SDIV(config.ops["var_div"],size,D(Int(7,IntType(4,false))))),
        Ins(ICMP(config.ops["var_cmp17"],sgt,4,config.ops["var_num_packets"],config.ops["var_div"])),
        IfElse(config.ops["var_cmp17"],
            if_then19(),
            postfixCodeSimple())]);//CNil
    patch_block
}


function challenge_8_transport_handler_create_conn_patch(size:Operand):seq<Code>  
    requires size.D?;
    requires size.d.Int?;
    requires size.d.itype == IntType(4,false);
    {

    // var num_packets := LV(" num_packets ");
    // var size := LV(" size ");
        //     ; Function Attrs: noinline nounwind optnone uwtable
        // define internal zeroext i8 @create_conn(i16 zeroext %size) #0 {
        // entry:
        //   %retval = alloca i8, align 1
        //   %size.addr = alloca i16, align 2
        //   store i16 %size, i16* %size.addr, align 2
        //   %0 = load i8, i8* @src, align 1
        //   %idxprom = zext i8 %0 to i64
        //   %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
        //   %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8
        //   %cmp = icmp eq %struct.ConnectionInfo* %1, null
        //   br i1 %cmp, label %if.then, label %if.end

        // if.then:                                          ; preds = %entry
        //   %call = call noalias align 16 i8* @calloc(i64 1, i64 16) #9
        //   %2 = bitcast i8* %call to %struct.ConnectionInfo*
        //   %3 = load i8, i8* @src, align 1
        //   %idxprom1 = zext i8 %3 to i64
        //   %arrayidx2 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom1
        //   store %struct.ConnectionInfo* %2, %struct.ConnectionInfo** %arrayidx2, align 8
        //   %4 = load i8, i8* @src, align 1
        //   %idxprom3 = zext i8 %4 to i64
        //   %arrayidx4 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom3
        //   %5 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx4, align 8
        //   %State = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %5, i32 0, i32 0
        //   store i32 0, i32* %State, align 8
        //   %6 = load i8, i8* @src, align 1
        //   %idxprom5 = zext i8 %6 to i64
        //   %arrayidx6 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom5
        //   %7 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx6, align 8
        //   %data = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %7, i32 0, i32 3
        //   store i8* null, i8** %data, align 8
        //   br label %if.end

        // if.end:                                           ; preds = %if.then, %entry
        //   %8 = load i16, i16* %size.addr, align 2
        //   %conv = zext i16 %8 to i32
        //   %rem = srem i32 %conv, 7
        //   %cmp7 = icmp ne i32 %rem, 0
        //   br i1 %cmp7, label %if.then9, label %if.end14

        // if.then9:                                         ; preds = %if.end
        //   %9 = load i16, i16* %size.addr, align 2
        //   %conv10 = zext i16 %9 to i32
        //   %add = add nsw i32 %conv10, 7
        //   %10 = load i16, i16* %size.addr, align 2
        //   %conv11 = zext i16 %10 to i32
        //   %rem12 = srem i32 %conv11, 7
        //   %sub = sub nsw i32 %add, %rem12
        //   %conv13 = trunc i32 %sub to i16
        //   store i16 %conv13, i16* %size.addr, align 2
        //   br label %if.end14

    // var prefix := Block([]);

        //     if.end14:                                         ; preds = %if.then9, %if.end
        //   %11 = load i8, i8* @num_packets, align 1
        //   %conv15 = zext i8 %11 to i32
        //   %12 = load i16, i16* %size.addr, align 2
        //   %conv16 = zext i16 %12 to i32
        //   %div = sdiv i32 %conv16, 7
        //   %cmp17 = icmp sgt i32 %conv15, %div
        //   br i1 %cmp17, label %if.then19, label %if.end21

        // if.then19:                                        ; preds = %if.end14
        //   %call20 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.6, i64 0, i64 0))
        //   call void @delete_connection()
        //   store i8 0, i8* %retval, align 1
        //   br label %return

        //if.end21:                                         ; preds = %if.end14
        //   %13 = load i8, i8* @src, align 1
        //   %idxprom22 = zext i8 %13 to i64
        //   %arrayidx23 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom22
        //   %14 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx23, align 8
        //   %data24 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %14, i32 0, i32 3
        //   %15 = load i8*, i8** %data24, align 8
        //   %cmp25 = icmp eq i8* %15, null
        //   br i1 %cmp25, label %if.then27, label %if.else

        // if.then27:                                        ; preds = %if.end21
        //   %16 = load i16, i16* %size.addr, align 2
        //   %conv28 = zext i16 %16 to i64
        //   %call29 = call noalias align 16 i8* @calloc(i64 %conv28, i64 1) #9
        //   %17 = load i8, i8* @src, align 1
        //   %idxprom30 = zext i8 %17 to i64
        //   %arrayidx31 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom30
        //   %18 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx31, align 8
        //   %data32 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %18, i32 0, i32 3
        //   store i8* %call29, i8** %data32, align 8
        //   br label %if.end41

        // if.else:                                          ; preds = %if.end21
        //   %19 = load i8, i8* @src, align 1
        //   %idxprom33 = zext i8 %19 to i64
        //   %arrayidx34 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom33
        //   %20 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx34, align 8
        //   %data35 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %20, i32 0, i32 3
        //   %21 = load i8*, i8** %data35, align 8
        //   %22 = load i16, i16* %size.addr, align 2
        //   %conv36 = zext i16 %22 to i64
        //   %call37 = call align 16 i8* @realloc(i8* %21, i64 %conv36) #9
        //   %23 = load i8, i8* @src, align 1
        //   %idxprom38 = zext i8 %23 to i64
        //   %arrayidx39 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom38
        //   %24 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx39, align 8
        //   %data40 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %24, i32 0, i32 3
        //   store i8* %call37, i8** %data40, align 8
        //   br label %if.end41

        // if.end41:                                         ; preds = %if.else, %if.then27
        //   %25 = load i8, i8* @num_connections, align 1
        //   %inc = add i8 %25, 1
        //   store i8 %inc, i8* @num_connections, align 1
        //   store i8 1, i8* %retval, align 1
        //   br label %return

        // return:                                           ; preds = %if.end41, %if.then19
        //   %26 = load i8, i8* %retval, align 1
        //   ret i8 %26

    [prefixCode(),patch_block(size)]
}

// function challenge_8_transport_handler_create_conn_mergerd_simple(patched:bool):codeRe {
    
//     var postfix := postfixCode();

//     var var_11 := LV("var_11");
//     var var_num_packets := LV("var_num_packets");
//     var var_conv15 := LV("var_conv15");
//     var var_12 := LV("var_12");
//     var var_size := LV("var_size");

//     var var_size_addr := LV(" var_size_addr ");
//     var var_conv16 := LV(" var_conv16 ");
//     var var_div := LV(" var_div ");
//     var var_cmp17 := LV(" var_cmp17 ");
//     var var_call20 := LV(" var_call20 ");
//     var var_retval := LV(" var_retval ");
//     var var_26 := LV(" var_26 ");



//     var return_ := Block([Ins(LOAD(var_26,1,var_retval)),
//     Ins(RET(var_26))]);

//     // 
//     var if_then19 := Block([Ins(CALL(D(Void),delete_connection())),
//     Ins(STORE(D(Int(0,IntType(1,false))),var_retval)),
//     Ins(UNCONDBR(return_))]);

//     var splitBlock := Divergence([if_then19],[CNil],patched);

//     // var patch_block := Block([Ins(LOAD(var_11,1,var_num_packets)),
//     // Ins(ZEXT(var_conv15,1,var_11,4)),
//     // Ins(LOAD(var_12,2,var_size_addr)),
//     // Ins(ZEXT(var_conv16,2,var_12,4)),
//     // Ins(SDIV(var_div,var_conv16,D(Int(7,IntType(4,false))))),
//     // Ins(ICMP(var_cmp17,sgt,4,var_conv15,var_div)),
//     // Ins(BR(var_conv15,splitBlock,postfix))]);

//     var patch_block := Block([Ins(SDIV(var_div,var_size,D(Int(7,IntType(4,false))))),
//     Ins(ICMP(var_cmp17,sgt,4,var_num_packets,var_div)),
//     Ins(BR(var_cmp17,splitBlock,postfix))]);
    


//     Block([prefixCode(),patch_block,postfixCode()])
// }


// lemma prefixAndPostfixAreEqual()
//     ensures challenge_8_transport_handler_create_conn_vuln().block[2] 
//     == challenge_8_transport_handler_create_conn_patch().block[2];
//     ensures challenge_8_transport_handler_create_conn_vuln().block[0] 
//     == challenge_8_transport_handler_create_conn_patch().block[0];
// {
//     // var vuln := challenge_8_transport_handler_create_conn_vuln();
//     // var patch := challenge_8_transport_handler_create_conn_patch();
//     // assert vuln.Block?;
//     // assert patch.Block?;
//     // assert |vuln.block| == 3;
//     // assert |patch.block| == 3;
//     // assert vuln.block[0] == prefixCode();
//     // assert patch.block[0] == prefixCode();
//     // assert vuln.block[0] == patch.block[0];

//     // assert vuln.block[2] == postfixCode();
//     // assert patch.block[2] == postfixCode();
//     // assert vuln.block[2] == patch.block[2];
// }

    function delete_connection():seq<Code>
    {
        [CNil]
    }

    predicate validStartingState(s:State)
        // requires ValidState(s)
    {
        
        var var_11 := LV("var_11");
        var var_num_packets := LV("var_num_packets");
        var var_conv15 := LV("var_conv15");
        var var_12 := LV("var_12");
        var var_size_addr := LV("var_size_addr");
        var var_size := LV("var_size");
        var var_conv16 := LV("var_conv16");
        var var_div := LV("var_div");
        var var_cmp17 := LV("var_cmp17");
        var var_call20 := LV("var_call20");
        var var_retval := LV("var_retval");
        var var_26 := LV("var_26");
        && ValidOperand(s,var_11)
        && ValidOperand(s,var_num_packets)
        && ValidOperand(s,var_conv15)
        && ValidOperand(s,var_12)
        && ValidOperand(s,var_size_addr)
        && ValidOperand(s,var_size)
        && ValidOperand(s,var_conv16)
        && ValidOperand(s,var_div)
        && ValidOperand(s,var_cmp17)
        && ValidOperand(s,var_call20)
        && ValidOperand(s,var_retval)
        && ValidOperand(s,var_26)
        && s.lvs["var_11"].Ptr?
        && s.lvs["var_num_packets"].Int?
        && s.lvs["var_size"].Int?
        && s.lvs["var_conv15"].Int?
        && s.lvs["var_12"].Ptr?
        && s.lvs["var_size_addr"].Int?
        && s.lvs["var_conv16"].Int?
        && s.lvs["var_div"].Int?
        && s.lvs["var_cmp17"].Int?
        && s.lvs["var_call20"].Int?
        && s.lvs["var_retval"].Ptr?
        && s.lvs["var_26"].Int?
        && s.lvs["var_11"] == (Ptr(0,0,0,1))
        // && s.lvs["var_num_packets"] == (Int(0,IntType(1,false)))
        && s.lvs["var_conv15"] == (Int(0,IntType(1,false)))
        && s.lvs["var_12"] == (Ptr(0,0,0,1))
        && s.lvs["var_size_addr"] == (Int(0,IntType(1,false)))
        && s.lvs["var_conv16"] == (Int(0,IntType(1,false)))
        && s.lvs["var_div"] == (Int(0,IntType(1,false)))
        && s.lvs["var_cmp17"] == (Int(0,IntType(1,true)))
        && s.lvs["var_call20"] == (Int(0,IntType(1,false)))
        && s.lvs["var_retval"] == (Ptr(0,0,0,1))
        && s.lvs["var_26"] == (Int(0,IntType(1,false)))
        && s.m.mem[0][0].mb? 
        && s.m.mem[0][0].size == 1
        && s.lvs["var_num_packets"].itype.signed
        && s.lvs["var_num_packets"].itype.size == 4
        && s.lvs["var_num_packets"].val >= 0 
        && s.lvs["var_num_packets"].val < 0x10000
        && !s.lvs["var_size"].itype.signed
        && s.lvs["var_size"].itype.size == 4
        && s.lvs["var_size"].val >= 0 
        && s.lvs["var_size"].val < 0x10000
    }
predicate validIntState(s:State)
        // requires ValidState(s)
    {
        var config := allVariablesConfig();
        forall v :: v in config.ops ==> ValidOperand(s,config.ops[v])

        // var var_11 := LV("var_11");
        // var var_num_packets := LV("var_num_packets");
        // var var_conv15 := LV("var_conv15");
        // var var_12 := LV("var_12");
        // var var_size_addr := LV("var_size_addr");
        // var var_size := LV("var_size");
        // var var_conv16 := LV("var_conv16");
        // var var_div := LV("var_div");
        // var var_cmp17 := LV("var_cmp17");
        // var var_call20 := LV("var_call20");
        // var var_retval := LV("var_retval");
        // var var_26 := LV("var_26");
        // && ValidOperand(s,var_11)
        // && ValidOperand(s,var_num_packets)
        // && ValidOperand(s,var_conv15)
        // && ValidOperand(s,var_12)
        // && ValidOperand(s,var_size_addr)
        // && ValidOperand(s,var_size)
        // && ValidOperand(s,var_conv16)
        // && ValidOperand(s,var_div)
        // && ValidOperand(s,var_cmp17)
        // && ValidOperand(s,var_call20)
        // && ValidOperand(s,var_retval)
        // && ValidOperand(s,var_26)
        // && s.lvs["var_11"].Ptr?
        // && s.lvs["var_num_packets"].Int?
        // && s.lvs["var_size"].Int?
        // && s.lvs["var_conv15"].Int?
        // && s.lvs["var_12"].Ptr?
        // && s.lvs["var_size_addr"].Int?
        // && s.lvs["var_conv16"].Int?
        // && s.lvs["var_div"].Int?
        // && s.lvs["var_cmp17"].Int?
        // && s.lvs["var_call20"].Int?
        // && s.lvs["var_retval"].Ptr?
        // && s.lvs["var_26"].Int?
    }


}