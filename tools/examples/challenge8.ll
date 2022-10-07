if.end14:                                      
  %div = sdiv i32 %conv16, 7
  %cmp17 = icmp sgt i32 %conv15, %div
  br i1 %cmp17, label %if.then19, label %if.end21

if.then19:                                        
  call void @delete_connection()
  store i8 0, i8* %retval, align 1
  br label %return

return:
  %26 = load i8, i8* %retval, align 1
  ret i8 %26
	