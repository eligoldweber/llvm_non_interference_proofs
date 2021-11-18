include "Types.s.dfy"
include "Memory.s.dfy"

 module System_s
{
    import opened Types_s
    import opened Memory_s
//////////////

    type addr = int
    type LocalVar = string
    type GlobalVar = string

    type ins
    datatype output = Out(o:Data) | Nil

    type codeSeq = seq<codeRe>

    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)

    datatype codeRe =
    | Ins(ins:ins)
    | Block(block:codeSeq)
    | IfElse(ifCond:bool, ifTrue:codeSeq, ifFalse:codeSeq)
    | CNil
            
    type behavior = seq<state>

    datatype state = State(
        lvs:map<LocalVar, Data>,
        gvs:map<GlobalVar, Data>,
        m:MemState,
        o:output,
        ok:bool)

    predicate State_Init(s:state)
    predicate StateNext(s:state,s':state)
    predicate ValidState(s:state)

    predicate validEvalIns(ins:ins, s:state, s':state)

    predicate ValidBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1 && ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    predicate ValidBehaviorNonTrivial(b:behavior)
    {
        ValidBehavior(b) && |b| > 0
        
    }

    predicate BehaviorEvalsCode(c:codeRe,b:behavior)
    {
        |b| >= 2 && b == [b[0]] + evalCode(c,b[0])
    }

    function behaviorOutput(b:behavior) : (bOut:seq<output>)
        ensures |bOut| == |b| 
        ensures forall i :: (i >= 0 && i < |b|) ==> bOut[i] == b[i].o

    function evalCode(c:codeRe, s:state) : (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures c.Block? ==> |b| == |evalBlock(c.block, s)|
        ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlock(c.ifTrue,s)| else |b| == |evalBlock(c.ifFalse,s)|
        ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)


    function evalBlock(block:codeSeq, s:state): (b:behavior)
        ensures |b| > 0

}