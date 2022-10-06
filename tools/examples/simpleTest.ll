entry:
	store i32 2147483646, i32* %y, align 4
	%add = add nsw i32 %2, %3
	store i32 %add, i32* %z, align 4
	%cmp2 = icmp sgt i32 %4, 0
	