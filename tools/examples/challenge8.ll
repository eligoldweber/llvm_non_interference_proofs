if.end14:                                      
  %11 = load i8, i8* @num_packets, align 1
  %conv15 = zext i8 %11 to i32
  %12 = load i16, i16* %size.addr, align 2
  %conv16 = zext i16 %12 to i32
  %div = sdiv i32 %conv16, 7
  %cmp17 = icmp sgt i32 %conv15, %div
  br i1 %cmp17, label %if.then19, label %if.end21

if.then19:                                        
  %call20 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.6, i64 0, i64 0))
  call void @delete_connection()
  store i8 0, i8* %retval, align 1
  br label %return
	