entry:
	%20 = trunc i64 %read_frame.coerce1 to i32	
	%conv78 = and i32 %20, 255
	%num_packets88 = getelementptr inbounds %struct.ConnectionInfo, %struct.ConnectionInfo* %22, i64 0, i32 1
	%23 = load i8, i8* %num_packets88, align 4, !tbaa !12
	%conv89 = zext i8 %23 to i32
	%cmp90 = icmp ugt i32 %conv78, %conv89
	br i1 %cmp90, label %if.then92, label %if.end93

if.then92: ; preds = %if.end82
	tail call fastcc void @delete_connection()
	br label %if.end122


if.end122:
	ret void 
	
if.end93:
	ret void
	
	