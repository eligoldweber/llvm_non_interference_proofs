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
  