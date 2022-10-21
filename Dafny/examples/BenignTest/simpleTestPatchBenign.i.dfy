//make sure to add proper paths for the following..
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"

module simpleTestPatchBenign
{
	import opened LLVM_def_NEW
	import opened types

function allVariablesConfigPatch():Configuration
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
predicate validConfigPatch(s:State)
	requires ValidState(s)
{
	var c := allVariablesConfigPatch(); 
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
function entryPatch():Code{
	var config := allVariablesConfigPatch();
	var entry := Block([Ins(RET(D(Int(0,IntType(4,false)))))]);
	entry
}
}