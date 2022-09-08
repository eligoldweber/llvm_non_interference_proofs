include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"

module challenge8Code{
    import opened control_flow
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened memory



function challenge_8_transport_handler_create_conn():codeRe {

    var num_packets := LV(" num_packets ");
    var size := LV(" size ");
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
        //   %state = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %5, i32 0, i32 0
        //   store i32 0, i32* %state, align 8
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

    var prefix := Block([]);

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
    var patch_block := Block([]);
        //         if.end21:                                         ; preds = %if.end14
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

    var postfix := Block([]);

    Block([prefix,patch_block,postfix])
}


}