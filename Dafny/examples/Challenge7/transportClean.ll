; ModuleID = 'transportNoSwitch.ll'
source_filename = "transport.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.ConnectionInfo = type { i32, i8, i8, i8* }
%struct.can_frame = type { i32, i8, i8, i8, i8, [8 x i8] }

@src = internal unnamed_addr global i8 73, align 1
@num_packets = internal unnamed_addr global i8 0, align 1
@.str = private unnamed_addr constant [74 x i8] c"Recieved RTS from %d to allocate %d bytes of data from %d no. of packets\0A\00", align 1
@connection_infos = internal unnamed_addr global [256 x %struct.ConnectionInfo*] zeroinitializer, align 16
@CTS = internal global %struct.can_frame zeroinitializer, align 8
@.str.1 = private unnamed_addr constant [19 x i8] c"could not send CTS\00", align 1
@.str.2 = private unnamed_addr constant [24 x i8] c"Recieved Abort from %d\0A\00", align 1
@.str.3 = private unnamed_addr constant [43 x i8] c"Recieved packet %d for connection with %d\0A\00", align 1
@.str.4 = private unnamed_addr constant [67 x i8] c"Recieved all packets for connection with %d. Closing connection!!\0A\00", align 1
@num_connections = internal unnamed_addr global i8 0, align 1

; Function Attrs: nounwind uwtable
define dso_local void @transport_handler(i64 %read_frame.coerce0, i64 %read_frame.coerce1, i32 %can_socket_desc, i8 zeroext %current_sa) local_unnamed_addr #0 {
entry:
  %.reg2mem = alloca i8, align 1
  %conv78.reg2mem = alloca i32, align 4
  %.reg2mem3 = alloca %struct.ConnectionInfo*, align 8
  %.reg2mem7 = alloca i8*, align 8
  %.reg2mem10 = alloca %struct.ConnectionInfo*, align 8
  %arrayidx.i129.reg2mem = alloca %struct.ConnectionInfo**, align 8
  %call29.i.reg2mem = alloca i8*, align 8
  %call21.i.reg2mem = alloca i8*, align 8
  %.reg2mem14 = alloca %struct.ConnectionInfo*, align 8
  %.pre.i.reg2mem = alloca i8*, align 8
  %.cast.i.reg2mem = alloca %struct.ConnectionInfo*, align 8
  %.reg2mem17 = alloca %struct.ConnectionInfo*, align 8
  %arrayidx.i.reg2mem = alloca %struct.ConnectionInfo**, align 8
  %.reg2mem23 = alloca i8, align 1
  %.reg2mem26 = alloca i16, align 2
  %and6.reg2mem = alloca i32, align 4
  %read_frame.sroa.0.0.extract.trunc.reg2mem = alloca i32, align 4
  %read_frame.sroa.12.8.extract.trunc.reg2mem = alloca i24, align 4
  %read_frame.sroa.11.8.extract.trunc.reg2mem = alloca i8, align 1
  %read_frame.sroa.10.8.extract.trunc.reg2mem = alloca i8, align 1
  %read_frame.sroa.10.8.extract.shift.reg2mem = alloca i64, align 8
  %read_frame.sroa.8.8.extract.trunc.reg2mem = alloca i16, align 2
  %read_frame.sroa.4122.8.extract.trunc.reg2mem = alloca i8, align 1
  %storemerge.i.reg2mem = alloca i8*, align 8
  %.reg2mem44 = alloca %struct.ConnectionInfo*, align 8
  %.reg2mem46 = alloca %struct.ConnectionInfo*, align 8
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %read_frame.sroa.4122.8.extract.trunc = trunc i64 %read_frame.coerce1 to i8
  store i8 %read_frame.sroa.4122.8.extract.trunc, i8* %read_frame.sroa.4122.8.extract.trunc.reg2mem, align 1
  %read_frame.sroa.8.8.extract.shift = lshr i64 %read_frame.coerce1, 8
  %read_frame.sroa.8.8.extract.trunc = trunc i64 %read_frame.sroa.8.8.extract.shift to i16
  store i16 %read_frame.sroa.8.8.extract.trunc, i16* %read_frame.sroa.8.8.extract.trunc.reg2mem, align 2
  %read_frame.sroa.10.8.extract.shift = lshr i64 %read_frame.coerce1, 24
  store i64 %read_frame.sroa.10.8.extract.shift, i64* %read_frame.sroa.10.8.extract.shift.reg2mem, align 8
  %read_frame.sroa.10.8.extract.shift.reload40 = load i64, i64* %read_frame.sroa.10.8.extract.shift.reg2mem, align 8
  %read_frame.sroa.10.8.extract.trunc = trunc i64 %read_frame.sroa.10.8.extract.shift.reload40 to i8
  store i8 %read_frame.sroa.10.8.extract.trunc, i8* %read_frame.sroa.10.8.extract.trunc.reg2mem, align 1
  %read_frame.sroa.11.8.extract.shift = lshr i64 %read_frame.coerce1, 32
  %read_frame.sroa.11.8.extract.trunc = trunc i64 %read_frame.sroa.11.8.extract.shift to i8
  store i8 %read_frame.sroa.11.8.extract.trunc, i8* %read_frame.sroa.11.8.extract.trunc.reg2mem, align 1
  %read_frame.sroa.12.8.extract.shift = lshr i64 %read_frame.coerce1, 40
  %read_frame.sroa.12.8.extract.trunc = trunc i64 %read_frame.sroa.12.8.extract.shift to i24
  store i24 %read_frame.sroa.12.8.extract.trunc, i24* %read_frame.sroa.12.8.extract.trunc.reg2mem, align 4
  %conv = trunc i64 %read_frame.coerce0 to i8
  store i8 %conv, i8* @src, align 1, !tbaa !3
  %and2126 = lshr i64 %read_frame.coerce0, 8
  %0 = trunc i64 %and2126 to i8
  %cmp = icmp eq i8 %0, %current_sa
  br i1 %cmp, label %if.then, label %entry.if.end111_crit_edge

entry.if.end111_crit_edge:                        ; preds = %entry
  br label %if.end111

if.then:                                          ; preds = %entry
  %read_frame.sroa.0.0.extract.trunc = trunc i64 %read_frame.coerce0 to i32
  store i32 %read_frame.sroa.0.0.extract.trunc, i32* %read_frame.sroa.0.0.extract.trunc.reg2mem, align 4
  %read_frame.sroa.0.0.extract.trunc.reload36 = load i32, i32* %read_frame.sroa.0.0.extract.trunc.reg2mem, align 4
  %and6 = and i32 %read_frame.sroa.0.0.extract.trunc.reload36, 16711680
  store i32 %and6, i32* %and6.reg2mem, align 4
  br label %NodeBlock

NodeBlock:                                        ; preds = %if.then
  %and6.reload33 = load i32, i32* %and6.reg2mem, align 4
  %Pivot = icmp slt i32 %and6.reload33, 15466496
  br i1 %Pivot, label %LeafBlock, label %LeafBlock1

LeafBlock1:                                       ; preds = %NodeBlock
  %and6.reload32 = load i32, i32* %and6.reg2mem, align 4
  %SwitchLeaf2 = icmp eq i32 %and6.reload32, 15466496
  br i1 %SwitchLeaf2, label %sw.bb, label %LeafBlock1.NewDefault_crit_edge

LeafBlock1.NewDefault_crit_edge:                  ; preds = %LeafBlock1
  br label %NewDefault

LeafBlock:                                        ; preds = %NodeBlock
  %and6.reload = load i32, i32* %and6.reg2mem, align 4
  %SwitchLeaf = icmp eq i32 %and6.reload, 15400960
  br i1 %SwitchLeaf, label %sw.bb54, label %LeafBlock.NewDefault_crit_edge

LeafBlock.NewDefault_crit_edge:                   ; preds = %LeafBlock
  br label %NewDefault

sw.bb:                                            ; preds = %LeafBlock1
  br label %NodeBlock8

NodeBlock8:                                       ; preds = %sw.bb
  %read_frame.sroa.4122.8.extract.trunc.reload43 = load i8, i8* %read_frame.sroa.4122.8.extract.trunc.reg2mem, align 1
  %Pivot9 = icmp slt i8 %read_frame.sroa.4122.8.extract.trunc.reload43, 19
  br i1 %Pivot9, label %LeafBlock4, label %LeafBlock6

LeafBlock6:                                       ; preds = %NodeBlock8
  %read_frame.sroa.4122.8.extract.trunc.reload42 = load i8, i8* %read_frame.sroa.4122.8.extract.trunc.reg2mem, align 1
  %SwitchLeaf7 = icmp eq i8 %read_frame.sroa.4122.8.extract.trunc.reload42, 19
  br i1 %SwitchLeaf7, label %sw.bb45, label %LeafBlock6.NewDefault3_crit_edge

LeafBlock6.NewDefault3_crit_edge:                 ; preds = %LeafBlock6
  br label %NewDefault3

LeafBlock4:                                       ; preds = %NodeBlock8
  %read_frame.sroa.4122.8.extract.trunc.reload = load i8, i8* %read_frame.sroa.4122.8.extract.trunc.reg2mem, align 1
  %SwitchLeaf5 = icmp eq i8 %read_frame.sroa.4122.8.extract.trunc.reload, 16
  br i1 %SwitchLeaf5, label %if.else, label %LeafBlock4.NewDefault3_crit_edge

LeafBlock4.NewDefault3_crit_edge:                 ; preds = %LeafBlock4
  br label %NewDefault3

if.else:                                          ; preds = %LeafBlock4
  %read_frame.sroa.8.8.extract.trunc.reload41 = load i16, i16* %read_frame.sroa.8.8.extract.trunc.reg2mem, align 2
  %1 = tail call i16 asm "rorw $$8, ${0:w}", "=r,0,~{cc},~{dirflag},~{fpsr},~{flags}"(i16 %read_frame.sroa.8.8.extract.trunc.reload41) #8, !srcloc !6
  store i16 %1, i16* %.reg2mem26, align 2
  %read_frame.sroa.10.8.extract.trunc.reload39 = load i8, i8* %read_frame.sroa.10.8.extract.trunc.reg2mem, align 1
  store i8 %read_frame.sroa.10.8.extract.trunc.reload39, i8* @num_packets, align 1, !tbaa !3
  %read_frame.sroa.0.0.extract.trunc.reload35 = load i32, i32* %read_frame.sroa.0.0.extract.trunc.reg2mem, align 4
  %conv20 = and i32 %read_frame.sroa.0.0.extract.trunc.reload35, 255
  %.reload31 = load i16, i16* %.reg2mem26, align 2
  %conv21 = zext i16 %.reload31 to i32
  %read_frame.sroa.10.8.extract.shift.reload = load i64, i64* %read_frame.sroa.10.8.extract.shift.reg2mem, align 8
  %2 = trunc i64 %read_frame.sroa.10.8.extract.shift.reload to i32
  %conv22 = and i32 %2, 255
  %call = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([74 x i8], [74 x i8]* @.str, i64 0, i64 0), i32 %conv20, i32 %conv21, i32 %conv22)
  %3 = load i8, i8* @src, align 1, !tbaa !3
  store i8 %3, i8* %.reg2mem23, align 1
  %.reload25 = load i8, i8* %.reg2mem23, align 1
  %idxprom.i = zext i8 %.reload25 to i64
  %arrayidx.i = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i
  store %struct.ConnectionInfo** %arrayidx.i, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  %arrayidx.i.reload22 = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  %4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i.reload22, align 8, !tbaa !7
  store %struct.ConnectionInfo* %4, %struct.ConnectionInfo** %.reg2mem17, align 8
  %.reload21 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem17, align 8
  %cmp.i = icmp eq %struct.ConnectionInfo* %.reload21, null
  br i1 %cmp.i, label %if.end.thread.i, label %if.end.i

if.end.thread.i:                                  ; preds = %if.else
  %call.i = tail call noalias align 16 dereferenceable_or_null(16) i8* @calloc(i64 1, i64 16) #9
  %arrayidx.i.reload = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  %5 = bitcast %struct.ConnectionInfo** %arrayidx.i.reload to i8**
  store i8* %call.i, i8** %5, align 8, !tbaa !7
  %.cast.i = bitcast i8* %call.i to %struct.ConnectionInfo*
  store %struct.ConnectionInfo* %.cast.i, %struct.ConnectionInfo** %.cast.i.reg2mem, align 8
  %.cast.i.reload = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.cast.i.reg2mem, align 8
  store %struct.ConnectionInfo* %.cast.i.reload, %struct.ConnectionInfo** %.reg2mem46, align 8
  br label %if.then11.i

if.end.i:                                         ; preds = %if.else
  %.reload20 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem17, align 8
  %data9.phi.trans.insert.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload20, i64 0, i32 3
  %.pre.i = load i8*, i8** %data9.phi.trans.insert.i, align 8, !tbaa !9
  store i8* %.pre.i, i8** %.pre.i.reg2mem, align 8
  %.pre.i.reload16 = load i8*, i8** %.pre.i.reg2mem, align 8
  %cmp10.i = icmp eq i8* %.pre.i.reload16, null
  br i1 %cmp10.i, label %if.end.i.if.then11.i_crit_edge, label %if.else.i

if.end.i.if.then11.i_crit_edge:                   ; preds = %if.end.i
  %.reload19 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem17, align 8
  store %struct.ConnectionInfo* %.reload19, %struct.ConnectionInfo** %.reg2mem46, align 8
  br label %if.then11.i

if.then11.i:                                      ; preds = %if.end.i.if.then11.i_crit_edge, %if.end.thread.i
  %.reload47 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem46, align 8
  store %struct.ConnectionInfo* %.reload47, %struct.ConnectionInfo** %.reg2mem14, align 8
  %.reload30 = load i16, i16* %.reg2mem26, align 2
  %rem1.i = urem i16 %.reload30, 7
  %cmp12.not.i = icmp eq i16 %rem1.i, 0
  %.reload29 = load i16, i16* %.reg2mem26, align 2
  %add.i = add i16 %.reload29, 7
  %sub.i = sub i16 %add.i, %rem1.i
  %.reload28 = load i16, i16* %.reg2mem26, align 2
  %size.addr.0.i = select i1 %cmp12.not.i, i16 %.reload28, i16 %sub.i
  %conv20.i = zext i16 %size.addr.0.i to i64
  %call21.i = tail call noalias align 16 i8* @calloc(i64 %conv20.i, i64 1) #9
  store i8* %call21.i, i8** %call21.i.reg2mem, align 8
  %call21.i.reload = load i8*, i8** %call21.i.reg2mem, align 8
  %.reload15 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem14, align 8
  store i8* %call21.i.reload, i8** %storemerge.i.reg2mem, align 8
  store %struct.ConnectionInfo* %.reload15, %struct.ConnectionInfo** %.reg2mem44, align 8
  br label %create_conn.exit

if.else.i:                                        ; preds = %if.end.i
  %.reload27 = load i16, i16* %.reg2mem26, align 2
  %conv28.i = zext i16 %.reload27 to i64
  %.pre.i.reload = load i8*, i8** %.pre.i.reg2mem, align 8
  %call29.i = tail call align 16 i8* @realloc(i8* nonnull %.pre.i.reload, i64 %conv28.i) #9
  store i8* %call29.i, i8** %call29.i.reg2mem, align 8
  %call29.i.reload = load i8*, i8** %call29.i.reg2mem, align 8
  %.reload18 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem17, align 8
  store i8* %call29.i.reload, i8** %storemerge.i.reg2mem, align 8
  store %struct.ConnectionInfo* %.reload18, %struct.ConnectionInfo** %.reg2mem44, align 8
  br label %create_conn.exit

create_conn.exit:                                 ; preds = %if.else.i, %if.then11.i
  %.reload45 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem44, align 8
  %storemerge.i.reload = load i8*, i8** %storemerge.i.reg2mem, align 8
  %data9.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload45, i64 0, i32 3
  store i8* %storemerge.i.reload, i8** %data9.i, align 8, !tbaa !9
  %6 = load i8, i8* @num_connections, align 1, !tbaa !3
  %inc.i = add i8 %6, 1
  store i8 %inc.i, i8* @num_connections, align 1, !tbaa !3
  %state = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload45, i64 0, i32 0
  store i32 1, i32* %state, align 8, !tbaa !11
  %7 = load i8, i8* @num_packets, align 1, !tbaa !3
  %num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload45, i64 0, i32 1
  store i8 %7, i8* %num_packets, align 4, !tbaa !12
  %8 = load i32, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  %and31 = and i32 %8, -65281
  %.reload24 = load i8, i8* %.reg2mem23, align 1
  %conv32 = zext i8 %.reload24 to i32
  %shl33 = shl nuw nsw i32 %conv32, 8
  %or34 = or i32 %and31, %shl33
  store i32 %or34, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  %read_frame.sroa.11.8.extract.trunc.reload38 = load i8, i8* %read_frame.sroa.11.8.extract.trunc.reg2mem, align 1
  store i8 %read_frame.sroa.11.8.extract.trunc.reload38, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 1), align 1, !tbaa !3
  %read_frame.sroa.12.8.extract.trunc.reload37 = load i24, i24* %read_frame.sroa.12.8.extract.trunc.reg2mem, align 4
  store i24 %read_frame.sroa.12.8.extract.trunc.reload37, i24* bitcast (i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 5) to i24*), align 1
  %call39 = tail call i64 @write(i32 %can_socket_desc, i8* bitcast (%struct.can_frame* @CTS to i8*), i64 16) #9
  %cmp40.not = icmp eq i64 %call39, 16
  br i1 %cmp40.not, label %create_conn.exit.if.end111_crit_edge, label %if.then42

create_conn.exit.if.end111_crit_edge:             ; preds = %create_conn.exit
  br label %if.end111

if.then42:                                        ; preds = %create_conn.exit
  tail call void (i32, i8*, ...) @err(i32 1, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.1, i64 0, i64 0)) #10
  unreachable

sw.bb45:                                          ; preds = %LeafBlock6
  %idxprom46 = and i64 %read_frame.coerce0, 255
  %arrayidx47 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom46
  %9 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx47, align 8, !tbaa !7
  %cmp48 = icmp eq %struct.ConnectionInfo* %9, null
  br i1 %cmp48, label %sw.bb45.if.end111_crit_edge, label %if.end51

sw.bb45.if.end111_crit_edge:                      ; preds = %sw.bb45
  br label %if.end111

if.end51:                                         ; preds = %sw.bb45
  %read_frame.sroa.0.0.extract.trunc.reload34 = load i32, i32* %read_frame.sroa.0.0.extract.trunc.reg2mem, align 4
  %conv52 = and i32 %read_frame.sroa.0.0.extract.trunc.reload34, 255
  %call53 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([24 x i8], [24 x i8]* @.str.2, i64 0, i64 0), i32 %conv52)
  %10 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom.i128 = zext i8 %10 to i64
  %arrayidx.i129 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i128
  store %struct.ConnectionInfo** %arrayidx.i129, %struct.ConnectionInfo*** %arrayidx.i129.reg2mem, align 8
  %arrayidx.i129.reload13 = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i129.reg2mem, align 8
  %11 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i129.reload13, align 8, !tbaa !7
  store %struct.ConnectionInfo* %11, %struct.ConnectionInfo** %.reg2mem10, align 8
  %.reload12 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem10, align 8
  %data.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload12, i64 0, i32 3
  %12 = load i8*, i8** %data.i, align 8, !tbaa !9
  store i8* %12, i8** %.reg2mem7, align 8
  %.reload9 = load i8*, i8** %.reg2mem7, align 8
  %cmp.not.i = icmp eq i8* %.reload9, null
  br i1 %cmp.not.i, label %if.end51.delete_connection.exit_crit_edge, label %if.then.i

if.end51.delete_connection.exit_crit_edge:        ; preds = %if.end51
  br label %delete_connection.exit

if.then.i:                                        ; preds = %if.end51
  %.reload8 = load i8*, i8** %.reg2mem7, align 8
  tail call void @free(i8* nonnull %.reload8) #9
  br label %delete_connection.exit

delete_connection.exit:                           ; preds = %if.end51.delete_connection.exit_crit_edge, %if.then.i
  %.reload11 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem10, align 8
  %13 = bitcast %struct.ConnectionInfo* %.reload11 to i8*
  tail call void @free(i8* %13) #9
  %arrayidx.i129.reload = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i129.reg2mem, align 8
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx.i129.reload, align 8, !tbaa !7
  %14 = load i8, i8* @num_connections, align 1, !tbaa !3
  %dec.i = add i8 %14, -1
  store i8 %dec.i, i8* @num_connections, align 1, !tbaa !3
  br label %if.end111

sw.bb54:                                          ; preds = %LeafBlock
  %idxprom55 = and i64 %read_frame.coerce0, 255
  %arrayidx56 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom55
  %15 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx56, align 8, !tbaa !7
  store %struct.ConnectionInfo* %15, %struct.ConnectionInfo** %.reg2mem3, align 8
  %.reload6 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem3, align 8
  %cmp57 = icmp eq %struct.ConnectionInfo* %.reload6, null
  br i1 %cmp57, label %sw.bb54.if.end111_crit_edge, label %if.end60

sw.bb54.if.end111_crit_edge:                      ; preds = %sw.bb54
  br label %if.end111

if.end60:                                         ; preds = %sw.bb54
  %.reload5 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem3, align 8
  %state63 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload5, i64 0, i32 0
  %16 = load i32, i32* %state63, align 8, !tbaa !11
  %cmp64.not = icmp eq i32 %16, 1
  br i1 %cmp64.not, label %if.end67, label %if.end60.if.end111_crit_edge

if.end60.if.end111_crit_edge:                     ; preds = %if.end60
  br label %if.end111

if.end67:                                         ; preds = %if.end60
  %.reload4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem3, align 8
  %recv_num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload4, i64 0, i32 2
  %17 = load i8, i8* %recv_num_packets, align 1, !tbaa !16
  %inc = add i8 %17, 1
  store i8 %inc, i8* %recv_num_packets, align 1, !tbaa !16
  %conv73 = zext i8 %inc to i32
  %read_frame.sroa.0.0.extract.trunc.reload = load i32, i32* %read_frame.sroa.0.0.extract.trunc.reg2mem, align 4
  %conv74 = and i32 %read_frame.sroa.0.0.extract.trunc.reload, 255
  %call75 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([43 x i8], [43 x i8]* @.str.3, i64 0, i64 0), i32 %conv73, i32 %conv74)
  %18 = trunc i64 %read_frame.coerce1 to i32
  %conv78 = and i32 %18, 255
  store i32 %conv78, i32* %conv78.reg2mem, align 4
  %conv78.reload2 = load i32, i32* %conv78.reg2mem, align 4
  %cmp79 = icmp eq i32 %conv78.reload2, 0
  br i1 %cmp79, label %if.end67.if.end111_crit_edge, label %if.end82

if.end67.if.end111_crit_edge:                     ; preds = %if.end67
  br label %if.end111

if.end82:                                         ; preds = %if.end67
  %19 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom83 = zext i8 %19 to i64
  %arrayidx84 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom83
  %20 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx84, align 8, !tbaa !7
  %data85 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %20, i64 0, i32 3
  %21 = load i8*, i8** %data85, align 8, !tbaa !9
  %conv78.reload = load i32, i32* %conv78.reg2mem, align 4
  %22 = mul nuw nsw i32 %conv78.reload, 7
  %mul = add nsw i32 %22, -7
  %idxprom89131 = zext i32 %mul to i64
  %arrayidx90 = getelementptr inbounds i8, i8* %21, i64 %idxprom89131
  %read_frame.sroa.8.9.arrayidx90.sroa_cast = bitcast i8* %arrayidx90 to i16*
  %read_frame.sroa.8.8.extract.trunc.reload = load i16, i16* %read_frame.sroa.8.8.extract.trunc.reg2mem, align 2
  store i16 %read_frame.sroa.8.8.extract.trunc.reload, i16* %read_frame.sroa.8.9.arrayidx90.sroa_cast, align 1
  %read_frame.sroa.10.9.arrayidx90.sroa_raw_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 2
  %read_frame.sroa.10.8.extract.trunc.reload = load i8, i8* %read_frame.sroa.10.8.extract.trunc.reg2mem, align 1
  store i8 %read_frame.sroa.10.8.extract.trunc.reload, i8* %read_frame.sroa.10.9.arrayidx90.sroa_raw_idx, align 1
  %read_frame.sroa.11.9.arrayidx90.sroa_raw_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 3
  %read_frame.sroa.11.8.extract.trunc.reload = load i8, i8* %read_frame.sroa.11.8.extract.trunc.reg2mem, align 1
  store i8 %read_frame.sroa.11.8.extract.trunc.reload, i8* %read_frame.sroa.11.9.arrayidx90.sroa_raw_idx, align 1
  %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 4
  %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_cast = bitcast i8* %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_idx to i24*
  %read_frame.sroa.12.8.extract.trunc.reload = load i24, i24* %read_frame.sroa.12.8.extract.trunc.reg2mem, align 4
  store i24 %read_frame.sroa.12.8.extract.trunc.reload, i24* %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_cast, align 1
  %recv_num_packets95 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %20, i64 0, i32 2
  %23 = load i8, i8* %recv_num_packets95, align 1, !tbaa !16
  store i8 %23, i8* %.reg2mem, align 1
  %num_packets99 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %20, i64 0, i32 1
  %24 = load i8, i8* %num_packets99, align 4, !tbaa !12
  %.reload1 = load i8, i8* %.reg2mem, align 1
  %cmp101.not = icmp ult i8 %.reload1, %24
  br i1 %cmp101.not, label %if.end82.if.end111_crit_edge, label %if.then103

if.end82.if.end111_crit_edge:                     ; preds = %if.end82
  br label %if.end111

if.then103:                                       ; preds = %if.end82
  %.reload = load i8, i8* %.reg2mem, align 1
  %conv96 = zext i8 %.reload to i32
  %call108 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([67 x i8], [67 x i8]* @.str.4, i64 0, i64 0), i32 %conv96)
  tail call fastcc void @delete_connection()
  br label %if.end111

NewDefault:                                       ; preds = %LeafBlock.NewDefault_crit_edge, %LeafBlock1.NewDefault_crit_edge
  br label %if.end111

NewDefault3:                                      ; preds = %LeafBlock4.NewDefault3_crit_edge, %LeafBlock6.NewDefault3_crit_edge
  br label %if.end111

if.end111:                                        ; preds = %if.end82.if.end111_crit_edge, %if.end67.if.end111_crit_edge, %if.end60.if.end111_crit_edge, %sw.bb54.if.end111_crit_edge, %sw.bb45.if.end111_crit_edge, %create_conn.exit.if.end111_crit_edge, %entry.if.end111_crit_edge, %NewDefault3, %NewDefault, %if.then103, %delete_connection.exit
  ret void
}

; Function Attrs: nofree nounwind
declare dso_local noundef i32 @printf(i8* nocapture noundef readonly, ...) local_unnamed_addr #1

; Function Attrs: nofree
declare dso_local noundef i64 @write(i32 noundef, i8* nocapture noundef readonly, i64 noundef) local_unnamed_addr #2

; Function Attrs: noreturn
declare dso_local void @err(i32, i8*, ...) local_unnamed_addr #3

; Function Attrs: nofree norecurse nosync nounwind uwtable willreturn writeonly mustprogress
define dso_local void @transport_setup() local_unnamed_addr #4 {
entry:
  %"reg2mem alloca point" = bitcast i32 0 to i32
  store i8 8, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 1), align 4, !tbaa !17
  store i32 -1729298615, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  store i64 -16646383, i64* bitcast (i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 0) to i64*), align 8
  ret void
}

; Function Attrs: nounwind uwtable
define dso_local void @transport_takedown() local_unnamed_addr #0 {
entry:
  %indvars.iv.next.reg2mem = alloca i64, align 8
  %.reg2mem = alloca i8*, align 8
  %.reg2mem3 = alloca %struct.ConnectionInfo*, align 8
  %indvars.iv.reg2mem = alloca i64, align 8
  %arrayidx.i.reg2mem = alloca %struct.ConnectionInfo**, align 8
  %indvars.iv.reg2mem8 = alloca i64, align 8
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %0 = load i8, i8* @src, align 1
  %idxprom.i = zext i8 %0 to i64
  %arrayidx.i = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i
  store %struct.ConnectionInfo** %arrayidx.i, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  store i64 0, i64* %indvars.iv.reg2mem8, align 8
  br label %for.body

for.cond.cleanup:                                 ; preds = %for.inc
  ret void

for.body:                                         ; preds = %for.inc.for.body_crit_edge, %entry
  %indvars.iv.reload9 = load i64, i64* %indvars.iv.reg2mem8, align 8
  store i64 %indvars.iv.reload9, i64* %indvars.iv.reg2mem, align 8
  %indvars.iv.reload6 = load i64, i64* %indvars.iv.reg2mem, align 8
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %indvars.iv.reload6
  %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8, !tbaa !7
  %cmp1.not = icmp eq %struct.ConnectionInfo* %1, null
  br i1 %cmp1.not, label %for.body.for.inc_crit_edge, label %if.then

for.body.for.inc_crit_edge:                       ; preds = %for.body
  br label %for.inc

if.then:                                          ; preds = %for.body
  %arrayidx.i.reload7 = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  %2 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i.reload7, align 8, !tbaa !7
  store %struct.ConnectionInfo* %2, %struct.ConnectionInfo** %.reg2mem3, align 8
  %.reload5 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem3, align 8
  %data.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload5, i64 0, i32 3
  %3 = load i8*, i8** %data.i, align 8, !tbaa !9
  store i8* %3, i8** %.reg2mem, align 8
  %.reload2 = load i8*, i8** %.reg2mem, align 8
  %cmp.not.i = icmp eq i8* %.reload2, null
  br i1 %cmp.not.i, label %if.then.delete_connection.exit_crit_edge, label %if.then.i

if.then.delete_connection.exit_crit_edge:         ; preds = %if.then
  br label %delete_connection.exit

if.then.i:                                        ; preds = %if.then
  %.reload = load i8*, i8** %.reg2mem, align 8
  tail call void @free(i8* nonnull %.reload) #9
  br label %delete_connection.exit

delete_connection.exit:                           ; preds = %if.then.delete_connection.exit_crit_edge, %if.then.i
  %.reload4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem3, align 8
  %4 = bitcast %struct.ConnectionInfo* %.reload4 to i8*
  tail call void @free(i8* %4) #9
  %arrayidx.i.reload = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.i.reg2mem, align 8
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx.i.reload, align 8, !tbaa !7
  %5 = load i8, i8* @num_connections, align 1, !tbaa !3
  %dec.i = add i8 %5, -1
  store i8 %dec.i, i8* @num_connections, align 1, !tbaa !3
  br label %for.inc

for.inc:                                          ; preds = %for.body.for.inc_crit_edge, %delete_connection.exit
  %indvars.iv.reload = load i64, i64* %indvars.iv.reg2mem, align 8
  %indvars.iv.next = add nuw nsw i64 %indvars.iv.reload, 1
  store i64 %indvars.iv.next, i64* %indvars.iv.next.reg2mem, align 8
  %indvars.iv.next.reload = load i64, i64* %indvars.iv.next.reg2mem, align 8
  %exitcond.not = icmp eq i64 %indvars.iv.next.reload, 256
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.inc.for.body_crit_edge, !llvm.loop !18

for.inc.for.body_crit_edge:                       ; preds = %for.inc
  %indvars.iv.next.reload1 = load i64, i64* %indvars.iv.next.reg2mem, align 8
  store i64 %indvars.iv.next.reload1, i64* %indvars.iv.reg2mem8, align 8
  br label %for.body
}

; Function Attrs: nofree nounwind willreturn mustprogress
declare dso_local noalias noundef align 16 i8* @calloc(i64 noundef, i64 noundef) local_unnamed_addr #5

; Function Attrs: inaccessiblemem_or_argmemonly nounwind willreturn mustprogress
declare dso_local noalias noundef align 16 i8* @realloc(i8* nocapture, i64 noundef) local_unnamed_addr #6

; Function Attrs: nounwind uwtable willreturn mustprogress
define internal fastcc void @delete_connection() unnamed_addr #7 {
entry:
  %.reg2mem = alloca i8*, align 8
  %.reg2mem2 = alloca %struct.ConnectionInfo*, align 8
  %arrayidx.reg2mem = alloca %struct.ConnectionInfo**, align 8
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %0 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom = zext i8 %0 to i64
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  store %struct.ConnectionInfo** %arrayidx, %struct.ConnectionInfo*** %arrayidx.reg2mem, align 8
  %arrayidx.reload5 = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.reg2mem, align 8
  %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.reload5, align 8, !tbaa !7
  store %struct.ConnectionInfo* %1, %struct.ConnectionInfo** %.reg2mem2, align 8
  %.reload4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem2, align 8
  %data = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %.reload4, i64 0, i32 3
  %2 = load i8*, i8** %data, align 8, !tbaa !9
  store i8* %2, i8** %.reg2mem, align 8
  %.reload1 = load i8*, i8** %.reg2mem, align 8
  %cmp.not = icmp eq i8* %.reload1, null
  br i1 %cmp.not, label %entry.if.end_crit_edge, label %if.then

entry.if.end_crit_edge:                           ; preds = %entry
  br label %if.end

if.then:                                          ; preds = %entry
  %.reload = load i8*, i8** %.reg2mem, align 8
  tail call void @free(i8* nonnull %.reload) #9
  br label %if.end

if.end:                                           ; preds = %entry.if.end_crit_edge, %if.then
  %.reload3 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %.reg2mem2, align 8
  %3 = bitcast %struct.ConnectionInfo* %.reload3 to i8*
  tail call void @free(i8* %3) #9
  %arrayidx.reload = load %struct.ConnectionInfo**, %struct.ConnectionInfo*** %arrayidx.reg2mem, align 8
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx.reload, align 8, !tbaa !7
  %4 = load i8, i8* @num_connections, align 1, !tbaa !3
  %dec = add i8 %4, -1
  store i8 %dec, i8* @num_connections, align 1, !tbaa !3
  ret void
}

; Function Attrs: inaccessiblemem_or_argmemonly nounwind willreturn mustprogress
declare dso_local void @free(i8* nocapture noundef) local_unnamed_addr #6

attributes #0 = { nounwind uwtable "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nofree nounwind "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { nofree "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nofree norecurse nosync nounwind uwtable willreturn writeonly mustprogress "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { nofree nounwind willreturn mustprogress "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #6 = { inaccessiblemem_or_argmemonly nounwind willreturn mustprogress "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #7 = { nounwind uwtable willreturn mustprogress "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #8 = { nounwind readnone }
attributes #9 = { nounwind }
attributes #10 = { noreturn nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"uwtable", i32 1}
!2 = !{!"clang version 13.0.0 (https://github.com/llvm/llvm-project.git 4eff9469475384a59a9da407e78aa00262edcdd0)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"omnipotent char", !5, i64 0}
!5 = !{!"Simple C/C++ TBAA"}
!6 = !{i32 -2146645194}
!7 = !{!8, !8, i64 0}
!8 = !{!"any pointer", !4, i64 0}
!9 = !{!10, !8, i64 8}
!10 = !{!"ConnectionInfo", !4, i64 0, !4, i64 4, !4, i64 5, !8, i64 8}
!11 = !{!10, !4, i64 0}
!12 = !{!10, !4, i64 4}
!13 = !{!14, !15, i64 0}
!14 = !{!"can_frame", !15, i64 0, !4, i64 4, !4, i64 5, !4, i64 6, !4, i64 7, !4, i64 8}
!15 = !{!"int", !4, i64 0}
!16 = !{!10, !4, i64 5}
!17 = !{!14, !4, i64 4}
!18 = distinct !{!18, !19}
!19 = !{!"llvm.loop.mustprogress"}
