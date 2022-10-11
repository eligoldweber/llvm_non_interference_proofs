entry:
  %retval = alloca i8, align 1
  %size.addr = alloca i16, align 2
  store i16 %size, i16* %size.addr, align 2
  %0 = load i8, i8* @num_connections, align 1
  %conv = zext i8 %0 to i32
  %cmp = icmp sge i32 %conv, 255
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i8 0, i8* %retval, align 1
  br label %return

if.end:  
  store i8 1, i8* %retval, align 1
  br label %return
  
return:                                           ; preds = %if.end49, %if.then27, %if.then
  %28 = load i8, i8* %retval, align 1
  ret i8 %28

