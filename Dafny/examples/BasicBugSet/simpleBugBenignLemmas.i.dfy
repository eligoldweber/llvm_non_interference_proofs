include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Sets.i.dfy"

module simpleBugBenignLemmas{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Sets_i

    lemma possibleVulnOutputs(s:state, b:behavior) 
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;

        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && ValidBehaviorNonTrivial(b) &&BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
    {
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
     
    }
lemma existsVulnBehavor(s:state,b:behavior,vulnBehaviors:set<behavior>,input:operand)
        requires ValidState(s);
        requires validPatchBehavior(b)
        requires |b| > 0;
        requires |vulnBehaviors| > 0; 
        requires b[0] == s;
        requires BehaviorEvalsCode(codePatch(input),b) && |b| > 0 && validInput(b[0],input);
        requires forall v :: v in vulnBehaviors <==> (exists input :: validInput(s,input) && ValidBehaviorNonTrivial(v) && BehaviorEvalsCode(codeVuln(input),v) && v[0] == s)
        requires forall input :: validInput(s,input) ==> (exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
        ensures exists vuln, vulnIn :: vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);

    {
        reveal_BehaviorEvalsCode();
        // validInputVulnImpliesBehavior(s);
        // var input :| BehaviorEvalsCode(codePatch(input),b) && |b| > 0 && validInput(b[0],input);
        var b' := unwrapPatchBehaviors(s,input);
        assert exists vuln, vulnIn :: vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);
    }

    lemma vulnBehaviorIncludesPatchedBehavior(s:state,b:behavior,vulnBehaviors:set<behavior>)
        requires ValidState(s);
        requires validPatchBehavior(b)
        requires |b| > 0;
        requires |vulnBehaviors| > 0; 
        requires b[0] == s;
        requires forall v :: v in vulnBehaviors <==> (exists input :: validInput(s,input) && ValidBehaviorNonTrivial(v) && BehaviorEvalsCode(codeVuln(input),v) && v[0] == s)
        ensures exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));

    {
        reveal_BehaviorEvalsCode();
        validInputVulnImpliesBehavior(s);
        var input :| BehaviorEvalsCode(codePatch(input),b) && |b| > 0 && validInput(b[0],input);
        var b' := unwrapPatchBehaviors(s,input);
       
        existsVulnBehavor(s,b,vulnBehaviors,input);
        var vuln, vulnIn :| vuln in vulnBehaviors && validInput(s,vulnIn)  && OperandContents(s,vulnIn).val < 2 && BehaviorEvalsCode(codeVuln(vulnIn),vuln);
        possibleVulnOutputs(s,vuln);
        assert equalOutput(behaviorOutput(vuln),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        
        assert vuln in vulnBehaviors && equalOutput(behaviorOutput(vuln), behaviorOutput(b));
        assert exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), behaviorOutput(b)));
        var vulnOut := allBehaviorOutputSet(vulnBehaviors);
        assert forall v :: v in vulnBehaviors ==> behaviorOutput(v) in vulnOut;
        assert [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))] in vulnOut;

    }


    lemma patchIsBenignTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires |patchBehaviors| == 0
        requires |patchOut| == 0
        requires ValidState(s);
        requires forall b :: b in vulnBehaviors <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
        requires forall b :: b in patchBehaviors <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codePatch(input),b) && b[0] == s)

        ensures forall p :: p in patchOut ==> p in vulnOut
        {
           
            assert |patchBehaviors| == 0;
            assert |patchOut| == 0;
            assert forall p :: p in patchBehaviors ==> p in vulnBehaviors;
            assert forall p :: p in patchBehaviors ==> (exists v :: v in vulnBehaviors && equalOutput(behaviorOutput(v), behaviorOutput(p)));
            assert forall p :: p in patchOut ==> p in vulnOut;
            
        }


    lemma patchIsBenignNonTrivial(s:state,vulnBehaviors:set<behavior>,patchBehaviors:set<behavior>,vulnOut:set<seq<output>>,patchOut:set<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |patchBehaviors| > 0;
        requires vulnOut == allBehaviorOutputSet(vulnBehaviors);
        requires patchOut ==  allBehaviorOutputSet(patchBehaviors);
        // requires expandedAllBehaviorsSurjective(vulnBehaviors,vulnOut);
        // requires expandedAllBehaviorsSurjective(patchBehaviors,patchOut);

        // requires SurjectiveOver(vulnBehaviors,vulnOut, x => behaviorOutput(x));
        // requires SurjectiveOver(patchBehaviors,patchOut, x => behaviorOutput(x));
        ensures forall p :: p in patchBehaviors ==> exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), behaviorOutput(p)));
        ensures forall p :: p in patchBehaviors ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        ensures forall p :: p in patchBehaviors ==> behaviorOutput(p) in vulnOut;
        ensures forall p :: p in patchBehaviors ==> behaviorOutput(p) in patchOut;
    {
        reveal_BehaviorEvalsCode();
        // validInputVulnImpliesBehavior(s);
        // reveal_expandedAllBehaviorsSurjective();
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        // reveal_allBehaviorOutputSet();
        assert |patchBehaviors| > 0;
        assert forall p :: p in patchBehaviors ==> validPatchBehavior(p);

        // allBehaviorEqualityIsInjective(vulnBehaviors,vulnOut);
        //         assert SurjectiveOver(vulnBehaviors,vulnOut, x => behaviorOutput(x));// ==> forall y :: y in vulnOut ==> (exists x :: x in vulnBehaviors && behaviorOutput(x) == y);

        // allBehaviorsSetSurjective(vulnBehaviors,vulnOut);
        // assert  
        // assert forall x :: x in allBehaviors(patchBehaviors) ==> equalOutput(x,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        forall p | p in patchBehaviors
            ensures exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), behaviorOutput(p)));
            ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures behaviorOutput(p) in vulnOut;
            ensures behaviorOutput(p) in patchOut;
            {

                var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
                var b' := unwrapPatchBehaviors(s,input);
                assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

                vulnBehaviorIncludesPatchedBehavior(s,p,vulnBehaviors);
                assert exists v :: (v in vulnBehaviors && equalOutput(behaviorOutput(v), [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
                var v :| (v in vulnBehaviors && equalOutput(behaviorOutput(v), [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
                assert behaviorOutput(v) in vulnOut;
                
                transitiveEquality(behaviorOutput(p),behaviorOutput(v),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert behaviorOutput(p) == behaviorOutput(v);
                equalOutputIsTransitiveSet(behaviorOutput(v),behaviorOutput(p),vulnOut);
                assert behaviorOutput(p) in vulnOut;
            }
        assert forall p :: p in patchBehaviors ==> behaviorOutput(p) in vulnOut;
        // assert forall p :: behaviorOutput(p) in patchOut ==> behaviorOutput(p) in vulnOut;
        // forall p | p in patchOut
        // {
        //     assert exists x :: x in patchBehaviors && behaviorOutput(x) == p;

        //     assert equalOutput(p, [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        // }
        // assert forall p :: p in patchOut ==> equalOutput(p, [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
               
            
    }

   lemma validInputPatchImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: ValidBehaviorNonTrivial(b) &&  BehaviorEvalsCode(codePatch(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codePatch(input),b) && b[0] == s
        {
            var b := unwrapPatchBehaviors(s,input);
            assert exists b' :: ValidBehaviorNonTrivial(b') && BehaviorEvalsCode(codePatch(input),b') && b'[0] == s;
        }
    }

    lemma validInputVulnImpliesBehavior(s:state)
        requires ValidState(s);
        ensures forall input :: validInput(s,input) ==> (exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
    {
        forall input | validInput(s,input)
            ensures exists b :: ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s
        {
            var b := unwrapVulnBehaviors(s,input);
            assert exists b' :: ValidBehaviorNonTrivial(b') && BehaviorEvalsCode(codeVuln(input),b') && b'[0] == s;
        }
    }

    
}