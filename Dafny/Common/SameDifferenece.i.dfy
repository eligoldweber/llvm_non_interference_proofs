
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

    function impactedState() : (vars:set<name>) //specified 
    {
        var n:name := "x";
        {n}
    } 

    datatype Step =
        | updateStep(sv:stateVal) 
        | updateStepNonImpact(sv:stateVal) 
        | stutterStep()

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case updateStep(sv) => sv.Val? && s' == updateVal(s,sv) && s'.pc == s.pc+1
            case updateStepNonImpact(sv) => sv.Val? &&  s' == updateVal(s,sv) && s'.pc == s.pc+1 // validNonImpactStep(sv) &&
            case stutterStep() => stutter(s,s')
    }

    predicate validNonImpactStep(sv:stateVal)
    {
        sv.Val? && !(sv.n in impactedState())
    }

    predicate StateNext(s:state,s':state)
    {
        && ValidState(s)
        && exists step :: NextStep(s,s',step)
    
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

    lemma updateStepNonImpactImpliesSameImpactedState(s:state,s':state,step:Step)
        requires StateNext(s,s')
        requires NextStep(s,s',step)
        requires step.updateStepNonImpact?
        requires !(step.sv.n in impactedState())
        ensures !(step.sv.n in impactedState()) && (forall n :: n in s.vals && n != step.sv.n ==> s.vals[n] == s'.vals[n]);
        ensures forall impact :: (impact in impactedState() && impact in s.vals) ==> s.vals[impact] == s'.vals[impact];
    {
        assert !(step.sv.n in impactedState()) && (forall n :: n in s.vals && n != step.sv.n ==> s.vals[n] == s'.vals[n]);
        assert forall impact :: (impact in impactedState() && impact in s.vals) ==> s.vals[impact] == s'.vals[impact];
    }


    function updateVal(s:state,sv:stateVal) : (s':state)
        requires sv.Val?
        ensures s.ok ==> s'.ok
        ensures if sv.n in s.vals && s.vals[sv.n] == sv.i then s.vals == s'.vals else s != s'
        ensures s' == s.(vals := s.vals[sv.n := sv.i],pc := s.pc + 1)
        ensures forall n :: n in s.vals && n != sv.n ==> s.vals[n] == s'.vals[n]
    {
        var s' := s.(vals := s.vals[sv.n := sv.i],pc := s.pc + 1);
        assert s'.vals[sv.n] == sv.i;
        if(sv.n in s.vals && s.vals[sv.n] == sv.i) then
            assert s.vals == s'.vals;
            s'
        else 
            assert s != s';
            s'
    }


    function ExecuteOneInst(s:state, s':state) : (sv_diff:stateVal)
        requires StateNext(s,s')

        ensures forall step ::  (&& NextStep(s,s',step) 
                                && step.updateStepNonImpact? 
                                && !(step.sv.n in impactedState())) ==>  
                                                                      || sv_diff.Nil? 
                                                                      || (!(sv_diff.n in impactedState()) && (forall n :: n in s.vals && n != step.sv.n ==> s.vals[n] == s'.vals[n]));

    {
        var step :| NextStep(s,s',step);
        if (step.stutterStep?) then
            var sv := Nil;
            sv
        else
            assert (step.updateStep? || step.updateStepNonImpact?);
            if s.vals != s'.vals then
                if forall name :: name in s'.vals ==> name in s.vals then // update val
                    assert exists name :: name in s'.vals && name in s.vals && s.vals[name] != s'.vals[name];
                    var diffKey :| diffKey in s'.vals && diffKey in s.vals && s.vals[diffKey] != s'.vals[diffKey];
                    var diffVal := s'.vals[diffKey] - s.vals[diffKey];
                    assert s' == s.(vals := s.vals[diffKey := s.vals[diffKey]+diffVal], pc := s.pc+1);
                    assert step.updateStepNonImpact? ==> s' == updateVal(s, Val(diffKey,s'.vals[diffKey]));
                    // assert step.updateStepNonImpact? ==> validNonImpactStep(step.sv);
                    assert step.updateStepNonImpact? && !(step.sv.n in impactedState())==>  !(diffKey in impactedState()) && (forall n :: n in s.vals && n != step.sv.n ==> s.vals[n] == s'.vals[n]);
                    Val(diffKey,diffVal)
                else
                    assert exists name :: name in s'.vals && !(name in s.vals);  
                    var diffKey :|  diffKey in s'.vals && !(diffKey in s.vals);
                    var diffVal := s'.vals[diffKey];
                    assert s' == s.(vals := s.vals[diffKey := diffVal], pc := s.pc+1);
                    Val(diffKey,diffVal)
            else
                Nil // no difference 
    }

    predicate NextSameDiff(s:state, s':state, p:state, p':state)
    {
        && StateNext(s,s')
        && StateNext(p,p')
        && s.pc == p.pc       
        && ExecuteOneInst(s, s') == ExecuteOneInst(p, p')
    }

        s(x = 5, a = 1)  ,, p(x = 7, a = 900)
        impactedSet = {x}
        NonImpactStateTrans(add (a,5))
        1 -> 6 ::  900 -> 905
        s / s' == p / p'    

    lemma updateStepNonImpactImpliesNextSameDiff(s:state,p:state, nonDepenStep:Step)
        requires s.pc == p.pc  
        requires ValidState(s);
        requires ValidState(p);
        requires nonDepenStep.updateStepNonImpact?
        requires nonDepenStep.sv.Val?
        
        // ensures forall s',p' :: (NextStep(s,s',nonDepenStep) &&  NextStep(p,p',nonDepenStep)) ==> NextSameDiff(s,s',p,p');
    {

        forall s',p' | && s' == updateVal(s,nonDepenStep.sv) 
                       && p' == updateVal(p,nonDepenStep.sv)
                       && s'.pc == s.pc + 1
                       && p'.pc == p.pc + 1
        // ensures ExecuteOneInst(s, s') == ExecuteOneInst(p, p');
        // ensures NextSameDiff(s,s',p,p');
        {
            
            //  assert nonDepenStep.updateStepNonImpact?;
            //  assert ExecuteOneInst(s,s').Val?;
            //  assert ExecuteOneInst(s, s') == ExecuteOneInst(p, p');
            //  assert NextSameDiff(s,s',p,p');
        }

    }

    

    // lemma subSeqOfBehaviorNextSameDiffIsBenign(b_s:behavior,subB_s:behavior,b_p:behavior,subB_p:behavior)
    //     requires isSubSeq(b_s,subB_s)
    //     requires ValidBehavior(b_s)
    //     requires ValidBehavior(subB_s)

    //     requires isSubSeq(b_p,subB_p)
    //     requires ValidBehavior(b_p)
    //     requires ValidBehavior(subB_p)

    //     requires |subB_s| == |subB_p|
    //     requires |subB_s| > 0;
    //     requires |b_p| >= (FindIndexInSeq(b_p,first(subB_p)) + |subB_p|-1)
    //     requires forall i,step_s,step_p :: && (0 <= i < |subB_p|- 1) 
    //                                        && NextStep(subB_s[i], subB_s[i+1], step_s)
    //                                        && NextStep(subB_p[i], subB_p[i+1], step_p)  ==> step_s == step_p
                                     
    //     requires forall i,step :: && (0 <= i < |subB_p|- 1) 
    //                               && NextStep(subB_s[i], subB_s[i+1], step)
    //                               && NextStep(subB_p[i], subB_p[i+1], step)  ==> step.updateStepNonImpact?
    // {

    //     var first_index := FindIndexInSeq(b_p,first(subB_p));
    //     assume (|b_p| >= (first_index + (|subB_p|-1)));

    //     // assume IsBenign(b_p[first_index..first_index+|subB_p|]);
    // }

    lemma patchIsBenign(c:simpleCode,patched:bool)
        // ensures forall s :: ValidState(s) ==> IsBenign(evalCode(c,s))
    {

    }


    // function evalCode(c:simpleCode, s:state) : (b:behavior)
        
    //     decreases c, 0
    // {
    //     // [s]
    //     if |c| == 0 then    
    //         []
    //     else 
    //         match first(c)
    //             case Nil => [s] + evalCode(all_but_first(c),s)
    //             case Val(n,i) =>  [updateVal(s,n,i)] + evalCode(all_but_first(c),updateVal(s,n,i))
    //             // case ValNonImpact(n,i) => [updateVal(s,n,i)] + evalCode(all_but_first(c),updateVal(s,n,i))
    
    // }


}