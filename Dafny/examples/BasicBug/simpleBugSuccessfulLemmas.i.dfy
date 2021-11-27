include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"

module simpleBugBenignLemmas{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types

lemma possibleVulnOutputs(s:state, b:behavior) 
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
        }
     
    }

    lemma possiblePatchOutputs(s:state, b:behavior) 
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        // ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)) 
        //                           ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input)  && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapPatchBehaviors(s,input);
        }
        // forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
        //     ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        // {
        //     var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
        //     var b' := unwrapVulnBehaviors(s,input);
        // }
     
    }


}