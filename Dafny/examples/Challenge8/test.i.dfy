
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"


module test{
    import opened LLVM_def_NEW
    import opened types

function allVariablesConfig():Configuration
{
	var var_retval := LV("var_retval");
	var var_cmp17 := LV("var_cmp17");
	var var_conv15 := LV("var_conv15");
	var var_conv16 := LV("var_conv16");
	var var_26 := LV("var_26");
	var var_div := LV("var_div");
	Config(map[
		 "var_retval" := var_retval,
		 "var_cmp17" := var_cmp17,
		 "var_conv15" := var_conv15,
		 "var_conv16" := var_conv16,
		 "var_26" := var_26,
		 "var_div" := var_div])
}

function return_():Code{
	var config := allVariablesConfig();
	var return_ := Block([Ins(LOAD(config.ops["var_26"],1,config.ops["var_retval"])),
	Ins(RET(config.ops["var_26"]))]);
	return_
}

function if_then19():Code{
	var config := allVariablesConfig();
	var if_then19 := Block([Ins(CALL(D(Void),delete_connection())),
	Ins(STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"])),
	return_()]);
	if_then19
}

function if_end14():Code{
	var config := allVariablesConfig();
	var if_end14 := Block([Ins(SDIV(config.ops["var_div"],config.ops["var_conv16"],D(Int(7,IntType(4,false))))),
	Ins(ICMP(config.ops["var_cmp17"],sgt,4,config.ops["var_conv15"],config.ops["var_div"])),
	IfElse(config.ops["var_conv15"],if_then19(),if_end21())]);
	if_end14
}

    function delete_connection():seq<Code>
    {
        [CNil]
    }

        function if_end21():Code
    {
        CNil
    }

}