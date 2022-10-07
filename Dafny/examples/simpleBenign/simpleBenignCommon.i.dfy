include "BenignCode.s.dfy"
include "../../LLVM/llvmREFACTOR_Multi.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBenignCommon{
    import opened simpleBenignCode
    import opened LLVM_defRE_Multi
    import opened types
    import opened Collections__Seqs_s


    lemma unwrapPrintf(s:state,s':state, d:Data)// returns (b:behavior)
        requires ValidState(s)
        requires s' == evalInsRe(CALL(D(Void),printf_code(d).block),s)
        requires ValidInstruction(s,CALL(D(Void),printf_code(d).block));
        //ensures b == evalBlockRE(printf_code(d).block,s);
        ensures StateNext(s,s')
        ensures NextStep(s,s',Step.evalInsStep(CALL(D(Void),printf_code(d).block)));
        {
            reveal_behaviorOutput();
            reveal_ValidBehavior();
          //  b := [];
            var subB := [s] + evalBlockRE(printf_code(d).block,s);
            // assert |subB| == 2;
            var step,remainder,subBehavior := unwrapBlockWitness(subB,printf_code(d).block,s); 
            assert subB[0] == s;
            assert NextStep(subB[0],subB[1],Step.evalInsStep(VISIBLE_OUT(Out(d))));
            var s'' := s.(o := Out(d));
            assert s'' == subB[1];
            // assert s'' == s';
            step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
            assert subB[1] == subB[2];  
            assert NextStep(subB[1],subB[2],Step.stutterStep());
            assert |subB| == 3;
            assert ValidBehavior(subB);
            assert ValidOperand(last(subB),D(Void));
            //assert !D(Void).LV? && !D(Void).GV?;
            assert validEvalIns(CALL(D(Void),printf_code(d).block),s,s');
            assert s'.ok;
            assert NextStep(s,s',Step.evalInsStep(CALL(D(Void),printf_code(d).block))) && StateNext(s,s');
            assert evalBlockRE(printf_code(d).block,s) == [subB[1],subB[2]];
            var x :=  evalInsRe(CALL(D(Void),printf_code(d).block),s);
            assert s' == s.(o := SubOut(behaviorOutput([subB[1],subB[2]])));


            // return [subB[1],subB[2]];


        }
}