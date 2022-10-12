include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"


module challenge9CodeExample
{
	import opened LLVM_def_NEW
	import opened types

function allVariablesConfig():Configuration
{
	var var_retval := LV("var_retval");
	var var_conv := LV("var_conv");
	var var_num_connections := LV("var_num_connections");
	var var_size_addr := LV("var_size_addr");
	var var_cmp := LV("var_cmp");
	var var_28 := LV("var_28");
	var var_size := LV("var_size");
	var var_0 := LV("var_0");
	Config(map[
		 "var_retval" := var_retval,
		 "var_conv" := var_conv,
		 "var_num_connections" := var_num_connections,
		 "var_size_addr" := var_size_addr,
		 "var_cmp" := var_cmp,
		 "var_28" := var_28,
		 "var_size" := var_size,
		 "var_0" := var_0])
}
predicate validConfig(s:State)
	requires ValidState(s)
{
	var c := allVariablesConfig(); 
	&& (forall op :: op in c.ops ==> 
		&& c.ops[op].LV? 
		&& c.ops[op].l in s.lvs
		&& ValidOperand(s,c.ops[op]))
		 &&"var_retval" in c.ops
		 &&"var_conv" in c.ops
		 &&"var_num_connections" in c.ops
		 &&"var_size_addr" in c.ops
		 &&"var_cmp" in c.ops
		 &&"var_28" in c.ops
		 &&"var_size" in c.ops
		 &&"var_0" in c.ops
		//... add any additional state information

        && s.lvs["var_28"].Int?
        && s.lvs["var_0"].Int?
        && s.lvs["var_num_connections"].Ptr?
        && s.lvs["var_retval"].Ptr?
        && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].mb? 
        && s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].size == 1
        && s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].mb? 
        && s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].size == 1
        && s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].data >= 0
}

function return_():Code{
	var config := allVariablesConfig();
	var return_ := Block([Ins(LOAD(config.ops["var_28"],1,config.ops["var_retval"])),
	Ins(RET(config.ops["var_28"]))]);
	return_
}

function if_end():Code{
	var config := allVariablesConfig();
	var if_end := Block([Ins(STORE(D(Int(1,IntType(1,false))),config.ops["var_retval"])),
	return_()]);
	if_end
}

function if_then():Code{
	var config := allVariablesConfig();
	var if_then := Block([Ins(STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"])),
	return_()]);
	if_then
}

function entry():Code{
	var config := allVariablesConfig();
	var entry := Block([Ins(ALLOCA(config.ops["var_retval"],1)),
	Ins(ALLOCA(config.ops["var_size_addr"],2)),
	Ins(STORE(config.ops["var_size"],config.ops["var_size_addr"])),
	Ins(LOAD(config.ops["var_0"],1,config.ops["var_num_connections"])),
	Ins(ZEXT(config.ops["var_conv"],1,config.ops["var_0"],4)),
	Ins(ICMP(config.ops["var_cmp"],sge,4,config.ops["var_conv"],D(Int(255,IntType(4,false))))),
	IfElse(config.ops["var_conv"],if_then(),if_end())]);
	entry
}

function entrySimple():Code{
	var config := allVariablesConfig();
	var entry := Block([Ins(LOAD(config.ops["var_0"],1,config.ops["var_num_connections"])),
	Ins(ZEXT(config.ops["var_conv"],1,config.ops["var_0"],4)),
	Ins(ICMP(config.ops["var_cmp"],sge,4,config.ops["var_conv"],D(Int(255,IntType(4,false))))),
	IfElse(config.ops["var_cmp"],if_then(),if_end())]);
	entry
}

}