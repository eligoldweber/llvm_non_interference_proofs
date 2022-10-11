; ModuleID = 'transport.ll'
source_filename = "transport.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.ConnectionInfo = type { i32, i8, i8, i8* }
%struct.can_frame = type { i32, i8, i8, i8, i8, [8 x i8] }

@src = internal global i8 73, align 1
@num_packets = internal global i8 0, align 1
@.str = private unnamed_addr constant [74 x i8] c"Recieved RTS from %d to allocate %d bytes of data from %d no. of packets\0A\00", align 1
@connection_infos = internal global [256 x %struct.ConnectionInfo*] zeroinitializer, align 16
@CTS = internal global %struct.can_frame zeroinitializer, align 8
@.str.1 = private unnamed_addr constant [19 x i8] c"could not send CTS\00", align 1
@.str.2 = private unnamed_addr constant [24 x i8] c"Recieved Abort from %d\0A\00", align 1
@.str.3 = private unnamed_addr constant [33 x i8] c"Recieved packet %d from SA %02x\0A\00", align 1
@.str.4 = private unnamed_addr constant [50 x i8] c"Arbit packet location detected! Connected closed\0A\00", align 1
@.str.5 = private unnamed_addr constant [45 x i8] c"Recieved all %d packets, closing connection\0A\00", align 1
@num_connections = internal global i8 0, align 1
@.str.6 = private unnamed_addr constant [44 x i8] c"RTS mismatch detected!! Connected rejected\0A\00", align 1

; Function Attrs: noinline nounwind uwtable
define dso_local void @transport_handler(i64 %read_frame.coerce0, i64 %read_frame.coerce1, i32 %can_socket_desc, i8 zeroext %current_sa) #0 {
entry:
  %read_frame = alloca %struct.can_frame, align 8
  %can_socket_desc.addr = alloca i32, align 4
  %current_sa.addr = alloca i8, align 1
  %size = alloca i16, align 2
  %__v = alloca i16, align 2
  %__x = alloca i16, align 2
  %tmp = alloca i16, align 2
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %0 = bitcast %struct.can_frame* %read_frame to { i64, i64 }*
  %1 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 0
  store i64 %read_frame.coerce0, i64* %1, align 8
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 1
  store i64 %read_frame.coerce1, i64* %2, align 8
  store i32 %can_socket_desc, i32* %can_socket_desc.addr, align 4
  store i8 %current_sa, i8* %current_sa.addr, align 1
  store i16 0, i16* %size, align 2
  %can_id = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 0
  %3 = load i32, i32* %can_id, align 8
  %and = and i32 %3, 255
  %conv = trunc i32 %and to i8
  store i8 %conv, i8* @src, align 1
  %can_id1 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 0
  %4 = load i32, i32* %can_id1, align 8
  %and2 = and i32 %4, 65280
  %shr = lshr i32 %and2, 8
  %5 = load i8, i8* %current_sa.addr, align 1
  %conv3 = zext i8 %5 to i32
  %cmp = icmp eq i32 %shr, %conv3
  br i1 %cmp, label %if.then, label %entry.if.end123_crit_edge

entry.if.end123_crit_edge:                        ; preds = %entry
  br label %if.end123

if.then:                                          ; preds = %entry
  %can_id5 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 0
  %6 = load i32, i32* %can_id5, align 8
  %and6 = and i32 %6, 16711680
  switch i32 %and6, label %if.then.sw.epilog122_crit_edge [
    i32 15466496, label %sw.bb
    i32 15400960, label %sw.bb54
  ]

if.then.sw.epilog122_crit_edge:                   ; preds = %if.then
  br label %sw.epilog122

sw.bb:                                            ; preds = %if.then
  %data = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx = getelementptr inbounds [8 x i8], [8 x i8]* %data, i64 0, i64 0
  %7 = load i8, i8* %arrayidx, align 8
  %conv7 = zext i8 %7 to i32
  switch i32 %conv7, label %sw.bb.sw.epilog_crit_edge [
    i32 16, label %sw.bb8
    i32 255, label %sw.bb45
  ]

sw.bb.sw.epilog_crit_edge:                        ; preds = %sw.bb
  br label %sw.epilog

sw.bb8:                                           ; preds = %sw.bb
  %8 = bitcast i16* %size to i8*
  %data9 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx10 = getelementptr inbounds [8 x i8], [8 x i8]* %data9, i64 0, i64 1
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 2 %8, i8* align 1 %arrayidx10, i64 2, i1 false)
  %9 = load i16, i16* %size, align 2
  store i16 %9, i16* %__x, align 2
  %10 = load i16, i16* %__x, align 2
  %11 = call i1 @llvm.is.constant.i16(i16 %10)
  br i1 %11, label %if.then11, label %if.else

if.then11:                                        ; preds = %sw.bb8
  %12 = load i16, i16* %__x, align 2
  %conv12 = zext i16 %12 to i32
  %shr13 = ashr i32 %conv12, 8
  %and14 = and i32 %shr13, 255
  %13 = load i16, i16* %__x, align 2
  %conv15 = zext i16 %13 to i32
  %and16 = and i32 %conv15, 255
  %shl = shl i32 %and16, 8
  %or = or i32 %and14, %shl
  %conv17 = trunc i32 %or to i16
  store i16 %conv17, i16* %__v, align 2
  br label %if.end

if.else:                                          ; preds = %sw.bb8
  %14 = load i16, i16* %__x, align 2
  %15 = call i16 asm "rorw $$8, ${0:w}", "=r,0,~{cc},~{dirflag},~{fpsr},~{flags}"(i16 %14) #8, !srcloc !4
  store i16 %15, i16* %__v, align 2
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then11
  %16 = load i16, i16* %__v, align 2
  store i16 %16, i16* %tmp, align 2
  %17 = load i16, i16* %tmp, align 2
  store i16 %17, i16* %size, align 2
  %data18 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx19 = getelementptr inbounds [8 x i8], [8 x i8]* %data18, i64 0, i64 3
  %18 = load i8, i8* %arrayidx19, align 1
  store i8 %18, i8* @num_packets, align 1
  %19 = load i8, i8* @src, align 1
  %conv20 = zext i8 %19 to i32
  %20 = load i16, i16* %size, align 2
  %conv21 = zext i16 %20 to i32
  %21 = load i8, i8* @num_packets, align 1
  %conv22 = zext i8 %21 to i32
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([74 x i8], [74 x i8]* @.str, i64 0, i64 0), i32 %conv20, i32 %conv21, i32 %conv22)
  %22 = load i16, i16* %size, align 2
  %call23 = call zeroext i8 @create_conn(i16 zeroext %22)
  %conv24 = zext i8 %call23 to i32
  %cmp25 = icmp eq i32 %conv24, 1
  br i1 %cmp25, label %if.then27, label %if.end.if.end44_crit_edge

if.end.if.end44_crit_edge:                        ; preds = %if.end
  br label %if.end44

if.then27:                                        ; preds = %if.end
  %23 = load i8, i8* @src, align 1
  %idxprom = zext i8 %23 to i64
  %arrayidx28 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  %24 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx28, align 8
  %state = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %24, i32 0, i32 0
  store i32 1, i32* %state, align 8
  %25 = load i8, i8* @num_packets, align 1
  %26 = load i8, i8* @src, align 1
  %idxprom29 = zext i8 %26 to i64
  %arrayidx30 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom29
  %27 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx30, align 8
  %num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %27, i32 0, i32 1
  store i8 %25, i8* %num_packets, align 4
  %28 = load i32, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 0), align 8
  %and31 = and i32 %28, -65281
  %29 = load i8, i8* @src, align 1
  %conv32 = zext i8 %29 to i32
  %shl33 = shl i32 %conv32, 8
  %or34 = or i32 %and31, %shl33
  store i32 %or34, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 0), align 8
  %data35 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx36 = getelementptr inbounds [8 x i8], [8 x i8]* %data35, i64 0, i64 4
  %30 = load i8, i8* %arrayidx36, align 4
  store i8 %30, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 5, i64 1), align 1
  %data37 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx38 = getelementptr inbounds [8 x i8], [8 x i8]* %data37, i64 0, i64 5
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 5, i64 5), i8* align 1 %arrayidx38, i64 3, i1 false)
  %31 = load i32, i32* %can_socket_desc.addr, align 4
  %call39 = call i64 @write(i32 %31, i8* bitcast (%struct.can_frame* @CTS to i8*), i64 16)
  %cmp40 = icmp ne i64 %call39, 16
  br i1 %cmp40, label %if.then42, label %if.end43

if.then42:                                        ; preds = %if.then27
  call void (i32, i8*, ...) @err(i32 1, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.1, i64 0, i64 0)) #9
  unreachable

if.end43:                                         ; preds = %if.then27
  br label %if.end44

if.end44:                                         ; preds = %if.end.if.end44_crit_edge, %if.end43
  br label %sw.epilog

sw.bb45:                                          ; preds = %sw.bb
  %32 = load i8, i8* @src, align 1
  %idxprom46 = zext i8 %32 to i64
  %arrayidx47 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom46
  %33 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx47, align 8
  %cmp48 = icmp eq %struct.ConnectionInfo* %33, null
  br i1 %cmp48, label %if.then50, label %if.end51

if.then50:                                        ; preds = %sw.bb45
  br label %sw.epilog

if.end51:                                         ; preds = %sw.bb45
  %34 = load i8, i8* @src, align 1
  %conv52 = zext i8 %34 to i32
  %call53 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([24 x i8], [24 x i8]* @.str.2, i64 0, i64 0), i32 %conv52)
  call void @delete_connection()
  br label %sw.epilog

sw.epilog:                                        ; preds = %sw.bb.sw.epilog_crit_edge, %if.end51, %if.then50, %if.end44
  br label %sw.epilog122

sw.bb54:                                          ; preds = %if.then
  %35 = load i8, i8* @src, align 1
  %idxprom55 = zext i8 %35 to i64
  %arrayidx56 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom55
  %36 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx56, align 8
  %cmp57 = icmp eq %struct.ConnectionInfo* %36, null
  br i1 %cmp57, label %if.then59, label %if.end60

if.then59:                                        ; preds = %sw.bb54
  br label %sw.epilog122

if.end60:                                         ; preds = %sw.bb54
  %37 = load i8, i8* @src, align 1
  %idxprom61 = zext i8 %37 to i64
  %arrayidx62 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom61
  %38 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx62, align 8
  %state63 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %38, i32 0, i32 0
  %39 = load i32, i32* %state63, align 8
  %cmp64 = icmp ne i32 %39, 1
  br i1 %cmp64, label %if.then66, label %if.end67

if.then66:                                        ; preds = %if.end60
  br label %sw.epilog122

if.end67:                                         ; preds = %if.end60
  %40 = load i8, i8* @src, align 1
  %idxprom68 = zext i8 %40 to i64
  %arrayidx69 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom68
  %41 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx69, align 8
  %recv_num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %41, i32 0, i32 2
  %42 = load i8, i8* %recv_num_packets, align 1
  %inc = add i8 %42, 1
  store i8 %inc, i8* %recv_num_packets, align 1
  %43 = load i8, i8* @src, align 1
  %idxprom70 = zext i8 %43 to i64
  %arrayidx71 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom70
  %44 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx71, align 8
  %recv_num_packets72 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %44, i32 0, i32 2
  %45 = load i8, i8* %recv_num_packets72, align 1
  %conv73 = zext i8 %45 to i32
  %46 = load i8, i8* @src, align 1
  %conv74 = zext i8 %46 to i32
  %call75 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str.3, i64 0, i64 0), i32 %conv73, i32 %conv74)
  %data76 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx77 = getelementptr inbounds [8 x i8], [8 x i8]* %data76, i64 0, i64 0
  %47 = load i8, i8* %arrayidx77, align 8
  %conv78 = zext i8 %47 to i32
  %cmp79 = icmp eq i32 %conv78, 0
  br i1 %cmp79, label %if.then81, label %if.end82

if.then81:                                        ; preds = %if.end67
  br label %sw.epilog122

if.end82:                                         ; preds = %if.end67
  %data83 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx84 = getelementptr inbounds [8 x i8], [8 x i8]* %data83, i64 0, i64 0
  %48 = load i8, i8* %arrayidx84, align 8
  %conv85 = zext i8 %48 to i32
  %49 = load i8, i8* @src, align 1
  %idxprom86 = zext i8 %49 to i64
  %arrayidx87 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom86
  %50 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx87, align 8
  %num_packets88 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %50, i32 0, i32 1
  %51 = load i8, i8* %num_packets88, align 4
  %conv89 = zext i8 %51 to i32
  %cmp90 = icmp sgt i32 %conv85, %conv89
  br i1 %cmp90, label %if.then92, label %if.end94

if.then92:                                        ; preds = %if.end82
  %call93 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([50 x i8], [50 x i8]* @.str.4, i64 0, i64 0))
  call void @delete_connection()
  br label %sw.epilog122

if.end94:                                         ; preds = %if.end82
  %52 = load i8, i8* @src, align 1
  %idxprom95 = zext i8 %52 to i64
  %arrayidx96 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom95
  %53 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx96, align 8
  %data97 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %53, i32 0, i32 3
  %54 = load i8*, i8** %data97, align 8
  %data98 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx99 = getelementptr inbounds [8 x i8], [8 x i8]* %data98, i64 0, i64 0
  %55 = load i8, i8* %arrayidx99, align 8
  %conv100 = zext i8 %55 to i32
  %sub = sub nsw i32 %conv100, 1
  %mul = mul nsw i32 %sub, 7
  %idxprom101 = sext i32 %mul to i64
  %arrayidx102 = getelementptr inbounds i8, i8* %54, i64 %idxprom101
  %data103 = getelementptr inbounds %struct.can_frame, %struct.can_frame* %read_frame, i32 0, i32 5
  %arrayidx104 = getelementptr inbounds [8 x i8], [8 x i8]* %data103, i64 0, i64 1
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %arrayidx102, i8* align 1 %arrayidx104, i64 7, i1 false)
  %56 = load i8, i8* @src, align 1
  %idxprom105 = zext i8 %56 to i64
  %arrayidx106 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom105
  %57 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx106, align 8
  %recv_num_packets107 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %57, i32 0, i32 2
  %58 = load i8, i8* %recv_num_packets107, align 1
  %conv108 = zext i8 %58 to i32
  %59 = load i8, i8* @src, align 1
  %idxprom109 = zext i8 %59 to i64
  %arrayidx110 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom109
  %60 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx110, align 8
  %num_packets111 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %60, i32 0, i32 1
  %61 = load i8, i8* %num_packets111, align 4
  %conv112 = zext i8 %61 to i32
  %cmp113 = icmp sge i32 %conv108, %conv112
  br i1 %cmp113, label %if.then115, label %if.end94.if.end121_crit_edge

if.end94.if.end121_crit_edge:                     ; preds = %if.end94
  br label %if.end121

if.then115:                                       ; preds = %if.end94
  %62 = load i8, i8* @src, align 1
  %idxprom116 = zext i8 %62 to i64
  %arrayidx117 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom116
  %63 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx117, align 8
  %recv_num_packets118 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %63, i32 0, i32 2
  %64 = load i8, i8* %recv_num_packets118, align 1
  %conv119 = zext i8 %64 to i32
  %call120 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([45 x i8], [45 x i8]* @.str.5, i64 0, i64 0), i32 %conv119)
  call void @delete_connection()
  br label %if.end121

if.end121:                                        ; preds = %if.end94.if.end121_crit_edge, %if.then115
  br label %sw.epilog122

sw.epilog122:                                     ; preds = %if.then.sw.epilog122_crit_edge, %if.end121, %if.then92, %if.then81, %if.then66, %if.then59, %sw.epilog
  br label %if.end123

if.end123:                                        ; preds = %entry.if.end123_crit_edge, %sw.epilog122
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: convergent nofree nosync nounwind readnone willreturn
declare i1 @llvm.is.constant.i16(i16) #2

declare dso_local i32 @printf(i8*, ...) #3

; Function Attrs: noinline nounwind uwtable
define internal zeroext i8 @create_conn(i16 zeroext %size) #0 {
entry:
  %retval = alloca i8, align 1
  %size.addr = alloca i16, align 2
  %"reg2mem alloca point" = bitcast i32 0 to i32
  store i16 %size, i16* %size.addr, align 2
  %0 = load i8, i8* @num_connections, align 1
  %conv = zext i8 %0 to i32
  %cmp = icmp sge i32 %conv, 255
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i8 0, i8* %retval, align 1
  br label %return

if.end:                                           ; preds = %entry
  %1 = load i8, i8* @src, align 1
  %idxprom = zext i8 %1 to i64
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  %2 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8
  %cmp2 = icmp eq %struct.ConnectionInfo* %2, null
  br i1 %cmp2, label %if.then4, label %if.end.if.end11_crit_edge

if.end.if.end11_crit_edge:                        ; preds = %if.end
  br label %if.end11

if.then4:                                         ; preds = %if.end
  %call = call noalias align 16 i8* @calloc(i64 1, i64 16) #10
  %3 = bitcast i8* %call to %struct.ConnectionInfo*
  %4 = load i8, i8* @src, align 1
  %idxprom5 = zext i8 %4 to i64
  %arrayidx6 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom5
  store %struct.ConnectionInfo* %3, %struct.ConnectionInfo** %arrayidx6, align 8
  %5 = load i8, i8* @src, align 1
  %idxprom7 = zext i8 %5 to i64
  %arrayidx8 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom7
  %6 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx8, align 8
  %state = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %6, i32 0, i32 0
  store i32 0, i32* %state, align 8
  %7 = load i8, i8* @src, align 1
  %idxprom9 = zext i8 %7 to i64
  %arrayidx10 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom9
  %8 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx10, align 8
  %data = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %8, i32 0, i32 3
  store i8* null, i8** %data, align 8
  br label %if.end11

if.end11:                                         ; preds = %if.end.if.end11_crit_edge, %if.then4
  %9 = load i16, i16* %size.addr, align 2
  %conv12 = zext i16 %9 to i32
  %rem = srem i32 %conv12, 7
  %cmp13 = icmp ne i32 %rem, 0
  br i1 %cmp13, label %if.then15, label %if.end11.if.end20_crit_edge

if.end11.if.end20_crit_edge:                      ; preds = %if.end11
  br label %if.end20

if.then15:                                        ; preds = %if.end11
  %10 = load i16, i16* %size.addr, align 2
  %conv16 = zext i16 %10 to i32
  %add = add nsw i32 %conv16, 7
  %11 = load i16, i16* %size.addr, align 2
  %conv17 = zext i16 %11 to i32
  %rem18 = srem i32 %conv17, 7
  %sub = sub nsw i32 %add, %rem18
  %conv19 = trunc i32 %sub to i16
  store i16 %conv19, i16* %size.addr, align 2
  br label %if.end20

if.end20:                                         ; preds = %if.end11.if.end20_crit_edge, %if.then15
  %12 = load i8, i8* @num_packets, align 1
  %conv21 = zext i8 %12 to i32
  %conv22 = sitofp i32 %conv21 to double
  %13 = load i16, i16* %size.addr, align 2
  %conv23 = uitofp i16 %13 to float
  %div = fdiv float %conv23, 7.000000e+00
  %conv24 = fpext float %div to double
  %14 = call double @llvm.ceil.f64(double %conv24)
  %cmp25 = fcmp ogt double %conv22, %14
  br i1 %cmp25, label %if.then27, label %if.end29

if.then27:                                        ; preds = %if.end20
  %call28 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.6, i64 0, i64 0))
  call void @delete_connection()
  store i8 0, i8* %retval, align 1
  br label %return

if.end29:                                         ; preds = %if.end20
  %15 = load i8, i8* @src, align 1
  %idxprom30 = zext i8 %15 to i64
  %arrayidx31 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom30
  %16 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx31, align 8
  %data32 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %16, i32 0, i32 3
  %17 = load i8*, i8** %data32, align 8
  %cmp33 = icmp eq i8* %17, null
  br i1 %cmp33, label %if.then35, label %if.else

if.then35:                                        ; preds = %if.end29
  %18 = load i16, i16* %size.addr, align 2
  %conv36 = zext i16 %18 to i64
  %call37 = call noalias align 16 i8* @calloc(i64 %conv36, i64 1) #10
  %19 = load i8, i8* @src, align 1
  %idxprom38 = zext i8 %19 to i64
  %arrayidx39 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom38
  %20 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx39, align 8
  %data40 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %20, i32 0, i32 3
  store i8* %call37, i8** %data40, align 8
  br label %if.end49

if.else:                                          ; preds = %if.end29
  %21 = load i8, i8* @src, align 1
  %idxprom41 = zext i8 %21 to i64
  %arrayidx42 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom41
  %22 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx42, align 8
  %data43 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %22, i32 0, i32 3
  %23 = load i8*, i8** %data43, align 8
  %24 = load i16, i16* %size.addr, align 2
  %conv44 = zext i16 %24 to i64
  %call45 = call align 16 i8* @realloc(i8* %23, i64 %conv44) #10
  %25 = load i8, i8* @src, align 1
  %idxprom46 = zext i8 %25 to i64
  %arrayidx47 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom46
  %26 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx47, align 8
  %data48 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %26, i32 0, i32 3
  store i8* %call45, i8** %data48, align 8
  br label %if.end49

if.end49:                                         ; preds = %if.else, %if.then35
  %27 = load i8, i8* @num_connections, align 1
  %inc = add i8 %27, 1
  store i8 %inc, i8* @num_connections, align 1
  store i8 1, i8* %retval, align 1
  br label %return

return:                                           ; preds = %if.end49, %if.then27, %if.then
  %28 = load i8, i8* %retval, align 1
  ret i8 %28
}

declare dso_local i64 @write(i32, i8*, i64) #3

; Function Attrs: noreturn
declare dso_local void @err(i32, i8*, ...) #4

; Function Attrs: noinline nounwind uwtable
define dso_local void @transport_setup() #0 {
entry:
  %"reg2mem alloca point" = bitcast i32 0 to i32
  store i8 8, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 1), align 4
  store i32 -1729298615, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 0), align 8
  call void @llvm.memset.p0i8.i64(i8* align 8 getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 5, i64 0), i8 -1, i64 8, i1 false)
  store i8 17, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 5, i64 0), align 8
  store i8 1, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i32 0, i32 5, i64 2), align 2
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #5

; Function Attrs: noinline nounwind uwtable
define dso_local void @transport_takedown() #0 {
entry:
  %i = alloca i32, align 4
  %"reg2mem alloca point" = bitcast i32 0 to i32
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %0 = load i32, i32* %i, align 4
  %cmp = icmp slt i32 %0, 256
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %1 = load i32, i32* %i, align 4
  %idxprom = sext i32 %1 to i64
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  %2 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8
  %cmp1 = icmp ne %struct.ConnectionInfo* %2, null
  br i1 %cmp1, label %if.then, label %for.body.if.end_crit_edge

for.body.if.end_crit_edge:                        ; preds = %for.body
  br label %if.end

if.then:                                          ; preds = %for.body
  %3 = load i32, i32* %i, align 4
  %conv = trunc i32 %3 to i8
  store i8 %conv, i8* @src, align 1
  call void @delete_connection()
  br label %if.end

if.end:                                           ; preds = %for.body.if.end_crit_edge, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %4 = load i32, i32* %i, align 4
  %inc = add nsw i32 %4, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond, !llvm.loop !5

for.end:                                          ; preds = %for.cond
  ret void
}

; Function Attrs: nounwind
declare dso_local noalias align 16 i8* @calloc(i64, i64) #6

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare double @llvm.ceil.f64(double) #7

; Function Attrs: nounwind
declare dso_local align 16 i8* @realloc(i8*, i64) #6

; Function Attrs: noinline nounwind uwtable
define internal void @delete_connection() #0 {
entry:
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %0 = load i8, i8* @src, align 1
  %idxprom = zext i8 %0 to i64
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8
  %data = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %1, i32 0, i32 3
  %2 = load i8*, i8** %data, align 8
  %cmp = icmp ne i8* %2, null
  br i1 %cmp, label %if.then, label %entry.if.end_crit_edge

entry.if.end_crit_edge:                           ; preds = %entry
  br label %if.end

if.then:                                          ; preds = %entry
  %3 = load i8, i8* @src, align 1
  %idxprom1 = zext i8 %3 to i64
  %arrayidx2 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom1
  %4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx2, align 8
  %data3 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %4, i32 0, i32 3
  %5 = load i8*, i8** %data3, align 8
  call void @free(i8* %5) #10
  %6 = load i8, i8* @src, align 1
  %idxprom4 = zext i8 %6 to i64
  %arrayidx5 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom4
  %7 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx5, align 8
  %data6 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %7, i32 0, i32 3
  store i8* null, i8** %data6, align 8
  br label %if.end

if.end:                                           ; preds = %entry.if.end_crit_edge, %if.then
  %8 = load i8, i8* @src, align 1
  %idxprom7 = zext i8 %8 to i64
  %arrayidx8 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom7
  %9 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx8, align 8
  %10 = bitcast %struct.ConnectionInfo* %9 to i8*
  call void @free(i8* %10) #10
  %11 = load i8, i8* @src, align 1
  %idxprom9 = zext i8 %11 to i64
  %arrayidx10 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom9
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx10, align 8
  %12 = load i8, i8* @num_connections, align 1
  %dec = add i8 %12, -1
  store i8 %dec, i8* @num_connections, align 1
  ret void
}

; Function Attrs: nounwind
declare dso_local void @free(i8*) #6

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { argmemonly nofree nosync nounwind willreturn }
attributes #2 = { convergent nofree nosync nounwind readnone willreturn }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { argmemonly nofree nosync nounwind willreturn writeonly }
attributes #6 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #7 = { nofree nosync nounwind readnone speculatable willreturn }
attributes #8 = { nounwind readnone }
attributes #9 = { noreturn }
attributes #10 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"uwtable", i32 1}
!2 = !{i32 7, !"frame-pointer", i32 2}
!3 = !{!"clang version 13.0.0 (https://github.com/llvm/llvm-project.git 4eff9469475384a59a9da407e78aa00262edcdd0)"}
!4 = !{i32 -2146795010}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
