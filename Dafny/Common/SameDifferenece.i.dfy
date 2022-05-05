
include "../LLVM/ops.dfy"
include "../LLVM/types.dfy"
include "../Libraries/Seqs.s.dfy"
include "../Libraries/Seqs.i.dfy"


// // Old      |   New
// // x := 0   |   x := 0
// // s0       |   s0
// // z := 0   |   z := 1
// // s        |   p
// // y := x   |   y := x
// // s'       |   p'
// function ExecuteOneInst(s, s') {
//   // Represents the difference between s, s' after executing instruction s.pc
//   // For example: ExecuteOneInst(s, s') == ExecuteOneInst(p, p') == UpdateStmt(y, x)
// }
// predicate NextSameDiff(s, s', p, p')
// {
//   && s.pc == p.pc       // Maybe something more sophisticated here to describe s.pc and p.pc also map to the same instruction
//   && ExecuteOneInst(s, s') == ExecuteOneInst(p, p')
// }

module AbstractSameDifference {
    import opened types
    import opened ops
    import opened Collections__Seqs_s
    import opened Collections__Seqs_i

    type name = string

    datatype state = State(
        vals:map<name, int>,
        pc:int,
        ok:bool)

    type behavior = seq<state>


    datatype codeRe =
    | Ins(ins:ins)
    | Block(block:codeSeq)
    | IfElse(ifCond:int, ifTrue:codeSeq, ifFalse:codeSeq)
    | Divergence(pre:codeSeq,post:codeSeq,patched:bool)
    | NonImpactIns(NIIns:ins)
    | CNil

     datatype ins =
    | ADD(dst:int, size:nat, src1ADD:int, src2ADD:int)
    | SUB(dst:int, size:nat, src1SUB:int, src2SUB:int)
    | ICMP(dst:int,cond:condition,size:nat,src1:int,src2:int)

    // datatype int = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    type codeSeq = seq<codeRe>

    type simpleCode = seq<stateVal>

    datatype stateVal = Val(n:name,i:int) | Nil  
    
    
    predicate ValidState(s:state)
    {
        s.ok
    }

    datatype Step =
        | updateStep(sv:stateVal) 
        | updateStepNonImpact(sv:stateVal) 
        | stutterStep()

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case updateStep(sv) => sv.Val? && s' == updateVal(s,sv.n,sv.i) && s'.pc == s.pc+1
            case updateStepNonImpact(sv) => sv.Val? && s' == updateVal(s,sv.n,sv.i) && s'.pc == s.pc+1
            case stutterStep() => stutter(s,s')
    }

    predicate StateNext(s:state,s':state)
    {
        && exists step :: NextStep(s,s',step)
        && ValidState(s)
    
    }

    predicate stutter(s:state,s':state)
    {
        s == s'
    }
    
    predicate errorStep(s:state,s':state)
    {
        ValidState(s) && !s'.ok
    }

    predicate ValidBehavior(states:behavior)
    {
        || |states| == 0
        || (|states| == 1 && ValidState(states[0])) 
        || (&& |states| >= 2
            && forall s :: s in states ==> ValidState(s)
            && forall i :: 0 <= i < |states|- 1 ==> StateNext(states[i],states[i+1]))
    }

    function evalCode(c:simpleCode, s:state) : (b:behavior)
        
        decreases c, 0
    {
        // [s]
        if |c| == 0 then    
            []
        else 
            match first(c)
                case Nil => [s] + evalCode(all_but_first(c),s)
                case Val(n,i) =>  [updateVal(s,n,i)] + evalCode(all_but_first(c),updateVal(s,n,i))
                case ValNonImpact(n,i) => [updateVal(s,n,i)] + evalCode(all_but_first(c),updateVal(s,n,i))
    
    }




    function updateVal(s:state,n:name,val:int) : (s':state)
        ensures s.ok ==> s'.ok
    {
        var s' := s.(vals := s.vals[n := val]);
        s'
    }

    function ExecuteOneInst(s:state, s':state,step:Step) : (sv:stateVal)
        requires NextStep(s,s',step)
        ensures !step.stutterStep? ==> step.sv == sv
        // ensures step.updateStepNonImpact? ==> 
    {
        // assume false;
        if step.stutterStep? then
            var sv := Nil;
            sv
        else
            assert (step.updateStep? || step.updateStepNonImpact?);
            assert s != s';
            var sv:stateVal :| sv.Val? && updateVal(s,sv.n,sv.i) == s';
            assert sv.n == step.sv.n;
            sv 
    }

    predicate NextSameDiff(s:state, s':state, p:state, p':state, step:Step)
    {
        && NextStep(s,s',step)
        && NextStep(p,p',step)
        && s.pc == p.pc       
        && ExecuteOneInst(s, s',step) == ExecuteOneInst(p, p',step)
    }

    lemma updateStepNonImpactImpliesNextSameDiff(s:state,p:state, nonDepenStep:Step)
        requires s.pc == p.pc  
        requires ValidState(s);
        requires ValidState(p);
        requires nonDepenStep.updateStepNonImpact?
        requires nonDepenStep.sv.Val?
        
        ensures forall s',p' :: (NextStep(s,s',nonDepenStep) &&  NextStep(p,p',nonDepenStep)) ==> NextSameDiff(s,s',p,p',nonDepenStep);
    {

        forall s',p' | && s' == updateVal(s,nonDepenStep.sv.n,nonDepenStep.sv.i) 
                       && p' == updateVal(p,nonDepenStep.sv.n,nonDepenStep.sv.i)
                       && s'.pc == s.pc + 1
                       && p'.pc == p.pc + 1
        ensures ExecuteOneInst(s, s',nonDepenStep) == ExecuteOneInst(p, p',nonDepenStep);
        ensures NextSameDiff(s,s',p,p',nonDepenStep);
        {
            
             assert nonDepenStep.updateStepNonImpact?;
             assert ExecuteOneInst(s,s',nonDepenStep).Val?;
             assert ExecuteOneInst(s, s',nonDepenStep) == ExecuteOneInst(p, p',nonDepenStep);
             assert NextSameDiff(s,s',p,p',nonDepenStep);
        }

    }

    

    lemma subSeqOfBehaviorNextSameDiffIsBenign(b_s:behavior,subB_s:behavior,b_p:behavior,subB_p:behavior)
        requires isSubSeq(b_s,subB_s)
        requires ValidBehavior(b_s)
        requires ValidBehavior(subB_s)

        requires isSubSeq(b_p,subB_p)
        requires ValidBehavior(b_p)
        requires ValidBehavior(subB_p)

        requires |subB_s| == |subB_p|
        requires |subB_s| > 0;
        requires |b_p| >= (FindIndexInSeq(b_p,first(subB_p)) + |subB_p|-1)
        requires forall i,step_s,step_p :: && (0 <= i < |subB_p|- 1) 
                                           && NextStep(subB_s[i], subB_s[i+1], step_s)
                                           && NextStep(subB_p[i], subB_p[i+1], step_p)  ==> step_s == step_p
                                     
        requires forall i,step :: && (0 <= i < |subB_p|- 1) 
                                  && NextStep(subB_s[i], subB_s[i+1], step)
                                  && NextStep(subB_p[i], subB_p[i+1], step)  ==> step.updateStepNonImpact?
    {

        var first_index := FindIndexInSeq(b_p,first(subB_p));
        assume (|b_p| >= (first_index + (|subB_p|-1)));

        // assume IsBenign(b_p[first_index..first_index+|subB_p|]);
    }

    lemma patchIsBenign(c:simpleCode,patched:bool)
        // ensures forall s :: ValidState(s) ==> IsBenign(evalCode(c,s))
    {

    }

}