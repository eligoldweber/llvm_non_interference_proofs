include "Challenge9Code.i.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"

module challenge9Properties{
    import opened challenge9Code
    import opened LLVM_def_NEW
    import opened types
    import opened Collections__Seqs_s


    lemma patch(s:State) returns (b:Behavior)
        requires ValidState(s);
        // requires validConfig(s);
    {
        // var config := allVariablesConfig();
        // b := [s] + evalCodeFn(entrySimple(),s);

    }

    // predicate miniSpec(s:State,b:Behavior)
    // {
        
    // }


}