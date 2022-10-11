include "Challenge9Code.i.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Seqs.i.dfy"
include "../../LLVM/memory.i.dfy"
include "../../LLVM/Operations/binaryOperations.i.dfy"
include "../../LLVM/ops.dfy"

module challenge9Properties{
    import opened challenge9Code
    import opened LLVM_def_NEW
    import opened types
    import opened memory
    import opened behavior_lemmas
    import opened Collections__Seqs_s
    import opened Collections__Seqs_i
    import opened binary_operations_i
    import opened ops


}