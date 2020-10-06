Challenge Problem 1 LLVM Instruction Subset
--------------------------------------------

## Add 
###### [https://llvm.org/docs/LangRef.html#add-instruction] 
The ‘add’ instruction returns the sum of its two operands.

	<result> = add <ty> <op1>, <op2>          ; yields ty:result
	
## Alloca 
###### [https://llvm.org/docs/LangRef.html#alloca-instruction]
The ‘alloca’ instruction allocates memory on the stack frame of the currently executing function, to be automatically released when this function returns to its caller. The object is always allocated in the address space for allocas indicated in the datalayout.

    <result> = alloca [inalloca] <type> [, <ty> <NumElements>] [, align <alignment>] [, addrspace(<num>)]     ; yields type addrspace(num)*:result	

## Br 
###### [https://llvm.org/docs/LangRef.html#br-instruction] 
The ‘br’ instruction is used to cause control flow to transfer to a different basic block in the current function. There are two forms of this instruction, corresponding to a conditional branch and an unconditional branch.

    br i1 <cond>, label <iftrue>, label <iffalse>	
## Call 
###### [https://llvm.org/docs/LangRef.html#call-instruction]
The ‘call’ instruction represents a simple function call.

    <result> = [tail | musttail | notail ] call [fast-math flags] [cconv] [ret attrs] [addrspace(<num>)]
           <ty>|<fnty> <fnptrval>(<function args>) [fn attrs] [ operand bundles ]

## Getelementptr 
###### [https://llvm.org/docs/LangRef.html#getelementptr-instruction]
The ‘getelementptr’ instruction is used to get the address of a subelement of an aggregate data structure. It performs address calculation only and does not access memory. The instruction can also be used to calculate a vector of such addresses.

    <result> = getelementptr <ty>, <ty>* <ptrval>{, [inrange] <ty> <idx>}*
## Icmp 
###### [https://llvm.org/docs/LangRef.html#icmp-instruction]
The ‘icmp’ instruction returns a boolean value or a vector of boolean values based on comparison of its two integer, integer vector, pointer, or pointer vector operands.

    <result> = icmp <cond> <ty> <op1>, <op2>   ; yields i1 or <N x i1>:result
## Load 
###### [https://llvm.org/docs/LangRef.html#load-instruction]
The ‘load’ instruction is used to read from memory.	

    <result> = load [volatile] <ty>, <ty>* <pointer>[, align <alignment>][, !nontemporal !<index>][, !invariant.load !<index>][, !invariant.group !<index>][, !nonnull !<index>][, !dereferenceable !<deref_bytes_node>][, !dereferenceable_or_null !<deref_bytes_node>][, !align !<align_node>]

## Store 
###### [https://llvm.org/docs/LangRef.html#store-instruction] 
The ‘store’ instruction is used to write to memory.
	
    store [volatile] <ty> <value>, <ty>* <pointer>[, align <alignment>][, !nontemporal !<index>][, !invariant.group !<index>]        ; yields void
	
## Ret 
###### [https://llvm.org/docs/LangRef.html#ret-instruction]
The ‘ret’ instruction is used to return control flow (and optionally a value) from a function back to the caller.

    ret <type> <value>       ; Return a value from a non-void function
	  ret void                 ; Return from void function
## Sext 
###### [https://llvm.org/docs/LangRef.html#sext-to-instruction]
The ‘sext’ sign extends value to the type ty2.
	
    <result> = sext <ty> <value> to <ty2>             ; yields ty2
	
## Shl 
###### [https://llvm.org/docs/LangRef.html#shl-instruction]
The ‘shl’ instruction returns the first operand shifted to the left a specified number of bits.

    <result> = shl <ty> <op1>, <op2>           ; yields ty:result
## Trunc 
###### [https://llvm.org/docs/LangRef.html#trunc-to-instruction]
The ‘trunc’ instruction truncates its operand to the type ty2.
	
    <result> = trunc <ty> <value> to <ty2>             ; yields ty2
## Zext 
###### [https://llvm.org/docs/LangRef.html#zext-to-instruction]
The ‘zext’ instruction zero extends its operand to type ty2.

    <result> = zext <ty> <value> to <ty2>             ; yields ty2

Others
--------
Align -- This struct is a compact representation of a valid (non-zero power of two) alignment. It is suitable for use as static global constants.



