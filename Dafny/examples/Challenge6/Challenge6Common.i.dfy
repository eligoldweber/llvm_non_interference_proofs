include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../LLVM/control_flow.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/memory.i.dfy"
include "Challenge6Code.s.dfy"

module challenge6common{
        import opened control_flow
        import opened LLVM_defRE
        import opened types
        import opened Collections__Seqs_s
        import opened behavior_lemmas
        import opened memory
        import opened challenge6Code


    lemma unwrapDumpWitness(s:state,op1:operand,op2:operand,sNext:state) returns (b:behavior)
        requires ValidState(s)
        requires ValidOperand(s,op1)
        requires ValidOperand(s,op2)
        requires sNext == evalInsRe(CALL(D(Void),stateOutputDump(op1,op2)),s)
        requires ValidInstruction(s,CALL(D(Void),stateOutputDump(op1,op2)));
        requires s.o == Nil

        ensures |b| == 4
        ensures ValidBehavior(b);
        ensures ValidOperand(last(b),D(Void));
        // ensures ValidOperand(b[1],op2);
        ensures behaviorOutput(b) == [Nil,Out(OperandContents(s,op1)),Out(OperandContents(s,op2)),Out(OperandContents(s,op2))];
        ensures NextStep(s,sNext,Step.evalInsStep(CALL(D(Void),stateOutputDump(op1,op2))));
        ensures StateNext(s,sNext);
        ensures ValidState(sNext);
        ensures sNext.o == SubOut([Out(OperandContents(s,op1)),Out(OperandContents(s,op2)),Out(OperandContents(s,op2))]);

    {
        reveal_behaviorOutput();
        var subB := [s] + evalCodeRE(Block(stateOutputDump(op1,op2)),s);// alBlockRE(stateOutputDump(op1,op2),s);
        assert stateOutputDump(op1,op2) == [Ins(RET((op1))),Ins(RET((op2)))];

        var step,remainder,subBehavior := unwrapBlockWitness(subB,stateOutputDump(op1,op2),s);
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
        
        assert subB[0] == s;
        assert NextStep(subB[0],subB[1],Step.evalInsStep(RET((op1))));
        assert ValidState(subB[1]);
        assert subB[1].o == Out(OperandContents(s,op1));
        assert NextStep(subB[1],subB[2],Step.evalInsStep(RET((op2))));
        assert ValidState(subB[2]);
        assert subB[2].o == Out(OperandContents(s,op2));
        assert subB[2] == subB[3];
        equalStatesAreStutter(subB[2],subB[3]);
        assert StateNext(subB[2],subB[3]);
        assert behaviorOutput(subB) == [Nil,Out(OperandContents(s,op1)),Out(OperandContents(s,op2)),Out(OperandContents(s,op2))];
        assert sNext == evalInsRe(CALL(D(Void),stateOutputDump(op1,op2)),s);
        assert sNext.ok;
        var rest := evalBlockRE(stateOutputDump(op1,op2),s);
        assert subB == [s] + rest;
        assert behaviorOutput(rest) == [Out(OperandContents(s,op1)),Out(OperandContents(s,op2)),Out(OperandContents(s,op2))];
        assert sNext.o == SubOut(behaviorOutput(rest));
        return subB;
    }



    lemma equalStatesAreStutter(s:state,s':state)
        requires s==s'
        requires ValidState(s);
        ensures ValidState(s');
        ensures NextStep(s,s',Step.stutterStep());
        ensures StateNext(s,s');
    {
         assert ValidState(s');
         assert NextStep(s,s',Step.stutterStep());
         assert StateNext(s,s');
    }

    lemma intsTypeMatch(x:Data,y:Data)
        requires (isInt(x) && isInt(y))
        requires x.itype.size == y.itype.size
        requires x.itype.signed == y.itype.signed
        ensures typesMatch(x,y);
    {
        assert typesMatch(x,y);
    }

    function validZero16bitInt(s:state) : (val:operand)
        ensures val.D?;
        ensures val.d.Int?;
        ensures ValidData(s, val.d)
        ensures !val.d.itype.signed
        ensures val.d.itype.size == 4
    {
        var val := D(Int(0,IntType(4,false)));
        assert  IntFits(val.d.val,val.d.itype);
        val
    }




    predicate validPracticalBehavior(preB:behavior)
    {
        |preB| == 11

        && ValidState(preB[0])
        && ValidState(preB[1])
        && ValidState(preB[2])
        && ValidState(preB[3])
        && ValidState(preB[4])
        && ValidState(preB[5])
        && ValidState(preB[6])
        && ValidState(preB[7])
        && ValidState(preB[8])
        && ValidState(preB[9])
        && ValidState(preB[10])
        && StateNext(preB[0],preB[1])
        && StateNext(preB[1],preB[2])
        && StateNext(preB[0],preB[1])
        && StateNext(preB[1],preB[2])
        && StateNext(preB[2],preB[3])
        && StateNext(preB[3],preB[4])
        && StateNext(preB[4],preB[5])
        && StateNext(preB[5],preB[6])
        && StateNext(preB[6],preB[7])
        && StateNext(preB[7],preB[8])
        && StateNext(preB[8],preB[9])
        && StateNext(preB[9],preB[10])
    }

    function validBehaviorsOuts():(validOut:seq<output>)
    {
        [Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))]),
        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(4,IntType(1,false))),Out(Int(4,IntType(1,false)))])]
    }

    function validSideEffectBehaviorsOuts():(validOut:seq<output>)
    {
        [Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        Nil,
        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(3,IntType(1,false))),Out(Int(3,IntType(1,false)))]),
        SubOut([Out((Int(16,IntType(4,false)))),Out(Int(3,IntType(1,false))),Out(Int(3,IntType(1,false)))])]
    }
    

}