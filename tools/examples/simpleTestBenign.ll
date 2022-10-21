entry:
  %cmp = icmp sle i32 %x, 0
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %cmp1 = icmp sgt i32 %x, 2
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  store i32 0, i32* %retval, align 4
  br label %return

if.end:                                           ; preds = %lor.lhs.false
  store i32 %x, i32* %retval, align 4
  br label %return

return:                                           ; preds = %if.end, %if.then
  %3 = load i32, i32* %retval, align 4
  ret i32 %3
  