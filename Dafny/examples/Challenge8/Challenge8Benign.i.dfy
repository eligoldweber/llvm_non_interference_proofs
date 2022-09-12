include "Challenge8Code.s.dfy"
include "../../LLVM/llvmREFACTOR_Multi.i.dfy"
include "../../LLVM/types.dfy"


module challenge8Benign{
    import opened challenge8Code
    import opened LLVM_defRE_Multi
    import opened types


    lemma equalBlocksEvalEqually(blockA:codeRe,blockB:codeRe)
        requires blockA == blockB
        ensures forall s :: ValidState(s) ==> evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    {
        assert forall s :: ValidState(s) ==> evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    }


}

