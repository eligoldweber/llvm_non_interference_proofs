entry:
  %z = alloca i32, align 4
  %cmp = icmp slt i32 %x, 0
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %cmp1 = icmp sgt i32 %x, 2
  br i1 %cmp1, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  br label %return

if.end:                                           ; preds = %lor.lhs.false
  %add = add nsw i32 %x, 2147483646
  store volatile i32 %add, i32* %z, align 4
  %0 = load volatile i32, i32* %z, align 4
  %cmp2 = icmp ugt i32 %0, 0
  br i1 %cmp2, label %if.then3, label %if.end4

if.then3:                                         ; preds = %if.end
  %call = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str, i64 0, i6
4 0))
  br label %if.end4

if.end4:                                          ; preds = %if.then3, %if.end
  %call5 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.1, i64 0, i
64 0))
  br label %return

return:                                           ; preds = %if.end4, %if.then
  ret void

