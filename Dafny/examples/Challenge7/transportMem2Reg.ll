; ModuleID = 'transport.ll'
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
  %read_frame.sroa.4122.8.extract.trunc = trunc i64 %read_frame.coerce1 to i8
  %read_frame.sroa.8.8.extract.shift = lshr i64 %read_frame.coerce1, 8
  %read_frame.sroa.8.8.extract.trunc = trunc i64 %read_frame.sroa.8.8.extract.shift to i16
  %read_frame.sroa.10.8.extract.shift = lshr i64 %read_frame.coerce1, 24
  %read_frame.sroa.10.8.extract.trunc = trunc i64 %read_frame.sroa.10.8.extract.shift to i8
  %read_frame.sroa.11.8.extract.shift = lshr i64 %read_frame.coerce1, 32
  %read_frame.sroa.11.8.extract.trunc = trunc i64 %read_frame.sroa.11.8.extract.shift to i8
  %read_frame.sroa.12.8.extract.shift = lshr i64 %read_frame.coerce1, 40
  %read_frame.sroa.12.8.extract.trunc = trunc i64 %read_frame.sroa.12.8.extract.shift to i24
  %conv = trunc i64 %read_frame.coerce0 to i8
  store i8 %conv, i8* @src, align 1, !tbaa !3
  %and2126 = lshr i64 %read_frame.coerce0, 8
  %0 = trunc i64 %and2126 to i8
  %cmp = icmp eq i8 %0, %current_sa
  br i1 %cmp, label %if.then, label %if.end111

if.then:                                          ; preds = %entry
  %read_frame.sroa.0.0.extract.trunc = trunc i64 %read_frame.coerce0 to i32
  %and6 = and i32 %read_frame.sroa.0.0.extract.trunc, 16711680
  switch i32 %and6, label %if.end111 [
    i32 15466496, label %sw.bb
    i32 15400960, label %sw.bb54
  ]

sw.bb:                                            ; preds = %if.then
  switch i8 %read_frame.sroa.4122.8.extract.trunc, label %if.end111 [
    i8 16, label %if.else
    i8 19, label %sw.bb45
  ]

if.else:                                          ; preds = %sw.bb
  %1 = tail call i16 asm "rorw $$8, ${0:w}", "=r,0,~{cc},~{dirflag},~{fpsr},~{flags}"(i16 %read_frame.sroa.8.8.extract.trunc) #8, !srcloc !6
  store i8 %read_frame.sroa.10.8.extract.trunc, i8* @num_packets, align 1, !tbaa !3
  %conv20 = and i32 %read_frame.sroa.0.0.extract.trunc, 255
  %conv21 = zext i16 %1 to i32
  %2 = trunc i64 %read_frame.sroa.10.8.extract.shift to i32
  %conv22 = and i32 %2, 255
  %call = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([74 x i8], [74 x i8]* @.str, i64 0, i64 0), i32 %conv20, i32 %conv21, i32 %conv22)
  %3 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom.i = zext i8 %3 to i64
  %arrayidx.i = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i
  %4 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i, align 8, !tbaa !7
  %cmp.i = icmp eq %struct.ConnectionInfo* %4, null
  br i1 %cmp.i, label %if.end.thread.i, label %if.end.i

if.end.thread.i:                                  ; preds = %if.else
  %call.i = tail call noalias align 16 dereferenceable_or_null(16) i8* @calloc(i64 1, i64 16) #9
  %5 = bitcast %struct.ConnectionInfo** %arrayidx.i to i8**
  store i8* %call.i, i8** %5, align 8, !tbaa !7
  %.cast.i = bitcast i8* %call.i to %struct.ConnectionInfo*
  br label %if.then11.i

if.end.i:                                         ; preds = %if.else
  %data9.phi.trans.insert.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %4, i64 0, i32 3
  %.pre.i = load i8*, i8** %data9.phi.trans.insert.i, align 8, !tbaa !9
  %cmp10.i = icmp eq i8* %.pre.i, null
  br i1 %cmp10.i, label %if.then11.i, label %if.else.i

if.then11.i:                                      ; preds = %if.end.i, %if.end.thread.i
  %6 = phi %struct.ConnectionInfo* [ %.cast.i, %if.end.thread.i ], [ %4, %if.end.i ]
  %rem1.i = urem i16 %1, 7
  %cmp12.not.i = icmp eq i16 %rem1.i, 0
  %add.i = add i16 %1, 7
  %sub.i = sub i16 %add.i, %rem1.i
  %size.addr.0.i = select i1 %cmp12.not.i, i16 %1, i16 %sub.i
  %conv20.i = zext i16 %size.addr.0.i to i64
  %call21.i = tail call noalias align 16 i8* @calloc(i64 %conv20.i, i64 1) #9
  br label %create_conn.exit

if.else.i:                                        ; preds = %if.end.i
  %conv28.i = zext i16 %1 to i64
  %call29.i = tail call align 16 i8* @realloc(i8* nonnull %.pre.i, i64 %conv28.i) #9
  br label %create_conn.exit

create_conn.exit:                                 ; preds = %if.else.i, %if.then11.i
  %7 = phi %struct.ConnectionInfo* [ %4, %if.else.i ], [ %6, %if.then11.i ]
  %storemerge.i = phi i8* [ %call29.i, %if.else.i ], [ %call21.i, %if.then11.i ]
  %data9.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %7, i64 0, i32 3
  store i8* %storemerge.i, i8** %data9.i, align 8, !tbaa !9
  %8 = load i8, i8* @num_connections, align 1, !tbaa !3
  %inc.i = add i8 %8, 1
  store i8 %inc.i, i8* @num_connections, align 1, !tbaa !3
  %state = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %7, i64 0, i32 0
  store i32 1, i32* %state, align 8, !tbaa !11
  %9 = load i8, i8* @num_packets, align 1, !tbaa !3
  %num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %7, i64 0, i32 1
  store i8 %9, i8* %num_packets, align 4, !tbaa !12
  %10 = load i32, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  %and31 = and i32 %10, -65281
  %conv32 = zext i8 %3 to i32
  %shl33 = shl nuw nsw i32 %conv32, 8
  %or34 = or i32 %and31, %shl33
  store i32 %or34, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  store i8 %read_frame.sroa.11.8.extract.trunc, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 1), align 1, !tbaa !3
  store i24 %read_frame.sroa.12.8.extract.trunc, i24* bitcast (i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 5) to i24*), align 1
  %call39 = tail call i64 @write(i32 %can_socket_desc, i8* bitcast (%struct.can_frame* @CTS to i8*), i64 16) #9
  %cmp40.not = icmp eq i64 %call39, 16
  br i1 %cmp40.not, label %if.end111, label %if.then42

if.then42:                                        ; preds = %create_conn.exit
  tail call void (i32, i8*, ...) @err(i32 1, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @.str.1, i64 0, i64 0)) #10
  unreachable

sw.bb45:                                          ; preds = %sw.bb
  %idxprom46 = and i64 %read_frame.coerce0, 255
  %arrayidx47 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom46
  %11 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx47, align 8, !tbaa !7
  %cmp48 = icmp eq %struct.ConnectionInfo* %11, null
  br i1 %cmp48, label %if.end111, label %if.end51

if.end51:                                         ; preds = %sw.bb45
  %conv52 = and i32 %read_frame.sroa.0.0.extract.trunc, 255
  %call53 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([24 x i8], [24 x i8]* @.str.2, i64 0, i64 0), i32 %conv52)
  %12 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom.i128 = zext i8 %12 to i64
  %arrayidx.i129 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i128
  %13 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i129, align 8, !tbaa !7
  %data.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %13, i64 0, i32 3
  %14 = load i8*, i8** %data.i, align 8, !tbaa !9
  %cmp.not.i = icmp eq i8* %14, null
  br i1 %cmp.not.i, label %delete_connection.exit, label %if.then.i

if.then.i:                                        ; preds = %if.end51
  tail call void @free(i8* nonnull %14) #9
  br label %delete_connection.exit

delete_connection.exit:                           ; preds = %if.then.i, %if.end51
  %15 = bitcast %struct.ConnectionInfo* %13 to i8*
  tail call void @free(i8* %15) #9
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx.i129, align 8, !tbaa !7
  %16 = load i8, i8* @num_connections, align 1, !tbaa !3
  %dec.i = add i8 %16, -1
  store i8 %dec.i, i8* @num_connections, align 1, !tbaa !3
  br label %if.end111

sw.bb54:                                          ; preds = %if.then
  %idxprom55 = and i64 %read_frame.coerce0, 255
  %arrayidx56 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom55
  %17 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx56, align 8, !tbaa !7
  %cmp57 = icmp eq %struct.ConnectionInfo* %17, null
  br i1 %cmp57, label %if.end111, label %if.end60

if.end60:                                         ; preds = %sw.bb54
  %state63 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %17, i64 0, i32 0
  %18 = load i32, i32* %state63, align 8, !tbaa !11
  %cmp64.not = icmp eq i32 %18, 1
  br i1 %cmp64.not, label %if.end67, label %if.end111

if.end67:                                         ; preds = %if.end60
  %recv_num_packets = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %17, i64 0, i32 2
  %19 = load i8, i8* %recv_num_packets, align 1, !tbaa !16
  %inc = add i8 %19, 1
  store i8 %inc, i8* %recv_num_packets, align 1, !tbaa !16
  %conv73 = zext i8 %inc to i32
  %conv74 = and i32 %read_frame.sroa.0.0.extract.trunc, 255
  %call75 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([43 x i8], [43 x i8]* @.str.3, i64 0, i64 0), i32 %conv73, i32 %conv74)
  %20 = trunc i64 %read_frame.coerce1 to i32
  %conv78 = and i32 %20, 255
  %cmp79 = icmp eq i32 %conv78, 0
  br i1 %cmp79, label %if.end111, label %if.end82

if.end82:                                         ; preds = %if.end67
  %21 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom83 = zext i8 %21 to i64
  %arrayidx84 = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom83
  %22 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx84, align 8, !tbaa !7
  %data85 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %22, i64 0, i32 3
  %23 = load i8*, i8** %data85, align 8, !tbaa !9
  %24 = mul nuw nsw i32 %conv78, 7
  %mul = add nsw i32 %24, -7
  %idxprom89131 = zext i32 %mul to i64
  %arrayidx90 = getelementptr inbounds i8, i8* %23, i64 %idxprom89131
  %read_frame.sroa.8.9.arrayidx90.sroa_cast = bitcast i8* %arrayidx90 to i16*
  store i16 %read_frame.sroa.8.8.extract.trunc, i16* %read_frame.sroa.8.9.arrayidx90.sroa_cast, align 1
  %read_frame.sroa.10.9.arrayidx90.sroa_raw_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 2
  store i8 %read_frame.sroa.10.8.extract.trunc, i8* %read_frame.sroa.10.9.arrayidx90.sroa_raw_idx, align 1
  %read_frame.sroa.11.9.arrayidx90.sroa_raw_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 3
  store i8 %read_frame.sroa.11.8.extract.trunc, i8* %read_frame.sroa.11.9.arrayidx90.sroa_raw_idx, align 1
  %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_idx = getelementptr inbounds i8, i8* %arrayidx90, i64 4
  %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_cast = bitcast i8* %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_idx to i24*
  store i24 %read_frame.sroa.12.8.extract.trunc, i24* %read_frame.sroa.12.sroa.0.0.read_frame.sroa.12.9.arrayidx90.sroa_raw_idx.sroa_cast, align 1
  %recv_num_packets95 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %22, i64 0, i32 2
  %25 = load i8, i8* %recv_num_packets95, align 1, !tbaa !16
  %num_packets99 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %22, i64 0, i32 1
  %26 = load i8, i8* %num_packets99, align 4, !tbaa !12
  %cmp101.not = icmp ult i8 %25, %26
  br i1 %cmp101.not, label %if.end111, label %if.then103

if.then103:                                       ; preds = %if.end82
  %conv96 = zext i8 %25 to i32
  %call108 = tail call i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([67 x i8], [67 x i8]* @.str.4, i64 0, i64 0), i32 %conv96)
  tail call fastcc void @delete_connection()
  br label %if.end111

if.end111:                                        ; preds = %if.then103, %if.end82, %if.end67, %if.end60, %sw.bb54, %delete_connection.exit, %sw.bb45, %create_conn.exit, %sw.bb, %if.then, %entry
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
  store i8 8, i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 1), align 4, !tbaa !17
  store i32 -1729298615, i32* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 0), align 8, !tbaa !13
  store i64 -16646383, i64* bitcast (i8* getelementptr inbounds (%struct.can_frame, %struct.can_frame* @CTS, i64 0, i32 5, i64 0) to i64*), align 8
  ret void
}

; Function Attrs: nounwind uwtable
define dso_local void @transport_takedown() local_unnamed_addr #0 {
entry:
  %0 = load i8, i8* @src, align 1
  %idxprom.i = zext i8 %0 to i64
  %arrayidx.i = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom.i
  br label %for.body

for.cond.cleanup:                                 ; preds = %for.inc
  ret void

for.body:                                         ; preds = %for.inc, %entry
  %indvars.iv = phi i64 [ 0, %entry ], [ %indvars.iv.next, %for.inc ]
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %indvars.iv
  %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8, !tbaa !7
  %cmp1.not = icmp eq %struct.ConnectionInfo* %1, null
  br i1 %cmp1.not, label %for.inc, label %if.then

if.then:                                          ; preds = %for.body
  %2 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx.i, align 8, !tbaa !7
  %data.i = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %2, i64 0, i32 3
  %3 = load i8*, i8** %data.i, align 8, !tbaa !9
  %cmp.not.i = icmp eq i8* %3, null
  br i1 %cmp.not.i, label %delete_connection.exit, label %if.then.i

if.then.i:                                        ; preds = %if.then
  tail call void @free(i8* nonnull %3) #9
  br label %delete_connection.exit

delete_connection.exit:                           ; preds = %if.then.i, %if.then
  %4 = bitcast %struct.ConnectionInfo* %2 to i8*
  tail call void @free(i8* %4) #9
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx.i, align 8, !tbaa !7
  %5 = load i8, i8* @num_connections, align 1, !tbaa !3
  %dec.i = add i8 %5, -1
  store i8 %dec.i, i8* @num_connections, align 1, !tbaa !3
  br label %for.inc

for.inc:                                          ; preds = %delete_connection.exit, %for.body
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, 256
  br i1 %exitcond.not, label %for.cond.cleanup, label %for.body, !llvm.loop !18
}

; Function Attrs: nofree nounwind willreturn mustprogress
declare dso_local noalias noundef align 16 i8* @calloc(i64 noundef, i64 noundef) local_unnamed_addr #5

; Function Attrs: inaccessiblemem_or_argmemonly nounwind willreturn mustprogress
declare dso_local noalias noundef align 16 i8* @realloc(i8* nocapture, i64 noundef) local_unnamed_addr #6

; Function Attrs: nounwind uwtable willreturn mustprogress
define internal fastcc void @delete_connection() unnamed_addr #7 {
entry:
  %0 = load i8, i8* @src, align 1, !tbaa !3
  %idxprom = zext i8 %0 to i64
  %arrayidx = getelementptr inbounds [256 x %struct.ConnectionInfo*], [256 x %struct.ConnectionInfo*]* @connection_infos, i64 0, i64 %idxprom
  %1 = load %struct.ConnectionInfo*, %struct.ConnectionInfo** %arrayidx, align 8, !tbaa !7
  %data = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %1, i64 0, i32 3
  %2 = load i8*, i8** %data, align 8, !tbaa !9
  %cmp.not = icmp eq i8* %2, null
  br i1 %cmp.not, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  tail call void @free(i8* nonnull %2) #9
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %3 = bitcast %struct.ConnectionInfo* %1 to i8*
  tail call void @free(i8* %3) #9
  store %struct.ConnectionInfo* null, %struct.ConnectionInfo** %arrayidx, align 8, !tbaa !7
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
