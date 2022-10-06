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
  br label %NodeBlock

NodeBlock:                                        ; preds = %if.then
  %Pivot = icmp slt i32 %and6, 15466496
  br i1 %Pivot, label %LeafBlock, label %LeafBlock1

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i32 %and6, 15466496
  br i1 %SwitchLeaf2, label %sw.bb, label %NewDefault

LeafBlock:                                        ; preds = %NodeBlock
  %SwitchLeaf = icmp eq i32 %and6, 15400960
  br i1 %SwitchLeaf, label %sw.bb54, label %NewDefault

sw.bb:                                            ; preds = %LeafBlock1
  br label %NodeBlock8

NodeBlock8:                                       ; preds = %sw.bb
  %Pivot9 = icmp slt i8 %read_frame.sroa.4122.8.extract.trunc, 19
  br i1 %Pivot9, label %LeafBlock4, label %LeafBlock6

LeafBlock6:                                       ; preds = %NodeBlock8
  %SwitchLeaf7 = icmp eq i8 %read_frame.sroa.4122.8.extract.trunc, 19
  br i1 %SwitchLeaf7, label %sw.bb45, label %NewDefault3

LeafBlock4:                                       ; preds = %NodeBlock8
  %SwitchLeaf5 = icmp eq i8 %read_frame.sroa.4122.8.extract.trunc, 16
  br i1 %SwitchLeaf5, label %if.else, label %NewDefault3


NewDefault:                                       ; preds = %LeafBlock1, %LeafBlock
  br label %if.end111

NewDefault3:                                      ; preds = %LeafBlock6, %LeafBlock4
  br label %if.end111
  
if.else:
	br label %if.end111

sw.bb45:                                          ; preds = %LeafBlock6
	br label %if.end111
  
sw.bb54:                                          ; preds = %LeafBlock6
	br label %if.end111
		
if.end111:                                        ; preds = %NewDefault3, %NewDefault, %if.then103, %if.end82, %if.end67, %if.end60, %sw.bb54, %delete_connection.exit, %sw.bb45, %create_conn.exit, %entry
  ret void
  