include "Challenge9CodeExample.i.dfy"
include "Challenge9PropertiesExample.i.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"

module a{
    import opened challenge9CodeExample
    import opened LLVM_def_NEW
    import opened types
    import opened Collections__Seqs_s
    import opened challenge9PropertiesExample


    lemma  vulnIs(s:State, b:Behavior)
        requires ValidState(s) 
        requires validConfig(s) 
        requires b == [s] + evalCodeFn(entrySimplVuln(),s)
               requires ValidOperand(last(b),allVariablesConfig().ops["var_28"])
       requires OperandContents(last(b),allVariablesConfig().ops["var_28"]).Int?
       requires ValidOperand(last(b),allVariablesConfig().ops["var_0"])
       requires OperandContents(last(b),allVariablesConfig().ops["var_0"]).Int?
        // ensures testVal(b)
        // ensures badbehavior(s,b)
        // ensures OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 ==> miniSpec(s,b);
    {
        // vulnAlwaysReturns1();
        var bVuln := unwrapVuln(s);
        assert b == bVuln;
        assert OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1;  
        assert OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 ==> miniSpec(s,b);
    }


}