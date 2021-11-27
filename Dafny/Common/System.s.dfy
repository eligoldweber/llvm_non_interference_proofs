include "Types.s.dfy"
include "Memory.s.dfy"
include "../Libraries/Seqs.s.dfy"

 module System_s
{
    import opened Types_s
    import opened Memory_s
     import opened Collections__Seqs_s

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


    function allBehaviors(a:set<behavior>) : (bOut:set<seq<output>>)
        // ensures |bOut| == |a|
        decreases |a|
    {
        if |a| == 0 then
            var empty := {};
            assert |empty| == |a|; 
            empty
        else   
            var x :| x in a;
            var a' := a - {x};
            var singleton := {behaviorOutput(x)};
            var s := singleton + allBehaviors(a');
            
            s
            //{behaviorOutput(x)} + allBehaviors(a')
    }

    function allBehaviorOutput(a:seq<behavior>) : (bOut:seq<seq<output>>)
        ensures |bOut| == |a|
        ensures forall a' :: a' in a ==> behaviorOutput(a') in bOut;
        ensures forall i :: (i >= 0 && i < |a|) ==> bOut[i] == behaviorOutput(a[i])
        // ensures forall b :: behaviorOutput(b) in bOut ==> b in a;
        // ensures forall b :: b in bOut ==> exists a' :: a' in a && behaviorOutput(a') == b
        // ensures forall a' :: behaviorOutput(a') in bOut ==> a' in a;
        // ensures forall b :: b in bOut ==> exists aa :: aa in a && behaviorOutput(aa) == b
        decreases |a|
    {
        if |a| == 0 then
            var out := [];
            assert forall a' :: behaviorOutput(a') in out ==> a' in a;
            out
        else   
            // var x :| x in a;
            // var a' := a - {x};
            // assert x in a;
            var out := [behaviorOutput(a[0])] + allBehaviorOutput(all_but_first(a));
            // assert behaviorOutput(a[0]) in out && a[0] in;
            // assert forall b :: behaviorOutput(b) in [behaviorOutput(x)] ==> behaviorOutput(b) == behaviorOutput(x);
            // assert forall b :: behaviorOutput(b) in [behaviorOutput(x)] ==> 
            out
            //{behaviorOutput(x)} + allBehaviors(a')
    }




    function evalCode(c:codeRe, s:state) : (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures c.Block? ==> |b| == |evalBlock(c.block, s)|
        ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlock(c.ifTrue,s)| else |b| == |evalBlock(c.ifFalse,s)|
        ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)


    function evalBlock(block:codeSeq, s:state): (b:behavior)
        ensures |b| > 0

}