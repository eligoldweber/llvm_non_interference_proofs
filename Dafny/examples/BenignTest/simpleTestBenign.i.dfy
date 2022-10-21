//make sure to add proper paths for the following..
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"

module simpleTestBenign
{
	import opened LLVM_def_NEW
	import opened types

function allVariablesConfigVuln():Configuration
{
	var var_retval := LV("var_retval");
	var var_cmp1 := LV("var_cmp1");
	var var_3 := LV("var_3");
	var var_cmp := LV("var_cmp");
	var var_x := LV("var_x");
	Config(map[
		 "var_retval" := var_retval,
		 "var_cmp1" := var_cmp1,
		 "var_3" := var_3,
		 "var_cmp" := var_cmp,
		 "var_x" := var_x])
}
predicate validConfigVuln(s:State)
	requires ValidState(s)
{
	var c := allVariablesConfigVuln(); 
	&& (forall op :: op in c.ops ==> 
		&& c.ops[op].LV? 
		&& c.ops[op].l in s.lvs
		&& ValidOperand(s,c.ops[op]))
		 &&"var_retval" in c.ops
		 &&"var_cmp1" in c.ops
		 &&"var_3" in c.ops
		 &&"var_cmp" in c.ops
		 &&"var_x" in c.ops
		//... add any additional state information

		 && s.lvs["var_x"].Int?
		 && s.lvs["var_x"].itype.size == 1
		 && !s.lvs["var_x"].itype.signed
		 && s.lvs["var_3"].Int?
		 && s.lvs["var_retval"].Ptr?
         && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].mb? 
         && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].size == 1
}

function return_():Code{
	var config := allVariablesConfigVuln();
	var return_ := Block([Ins(LOAD(config.ops["var_3"],1,config.ops["var_retval"])),
	Ins(RET(config.ops["var_3"]))]);
	return_
}

function if_end():Code{
	var config := allVariablesConfigVuln();
	var if_end := Block([Ins(STORE(config.ops["var_x"],config.ops["var_retval"])),
	return_()]);
	if_end
}

function if_then():Code{
	var config := allVariablesConfigVuln();
	var if_then := Block([Ins(STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"])),
	return_()]);
	if_then
}

function lor_lhs_false():Code{
	var config := allVariablesConfigVuln();
	var lor_lhs_false := Block([Ins(ICMP(config.ops["var_cmp1"],sgt,1,config.ops["var_x"],D(Int(2,IntType(1,false))))),
	IfElse(config.ops["var_cmp1"],if_then(),if_end())]);
	lor_lhs_false
}

function entryVuln():Code{
	var config := allVariablesConfigVuln();
	var entry := Block([Ins(ICMP(config.ops["var_cmp"],sle,1,config.ops["var_x"],D(Int(0,IntType(1,false))))),
	IfElse(config.ops["var_cmp"],if_then(),lor_lhs_false())]);
	entry
}
}


// entry:
//   %cmp = icmp sle i32 %x, 0
//   br i1 %cmp, label %if.then, label %lor.lhs.false

// lor.lhs.false:                                    ; preds = %entry
//   %cmp1 = icmp sgt i32 %x, 2
//   br i1 %cmp1, label %if.then, label %if.end

// if.then:                                          ; preds = %lor.lhs.false, %entry
//   store i32 0, i32* %retval, align 4
//   br label %return

// if.end:                                           ; preds = %lor.lhs.false
//   store i32 %x, i32* %retval, align 4
//   br label %return

// return:                                           ; preds = %if.end, %if.then
//   %3 = load i32, i32* %retval, align 4
//   ret i32 %3
  
