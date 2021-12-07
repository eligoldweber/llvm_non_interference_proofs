include "simpleBugCode.i.dfy"
include "simpleBugGeneral.i.dfy"
include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"

module simpleBugCompleteLemmas{
    import opened simpleBugCode
    import opened simpleBugGeneral
    import opened LLVM_defRE
    import opened types
    import opened Collections__Seqs_s

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
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
        }
     
    }

    lemma possibleVulnOutputsWithMiniSpec(s:state, b:behavior)
        requires ValidState(s);
        requires |b| > 0;
        requires b[0] == s;
        requires s.o.Nil?;
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> !MiniSpec(b);
        ensures  forall input :: (validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)) 
                                  ==> MiniSpec(b);
        ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b)) ==> 
                        (!MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
         ensures forall input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),b)) ==> 
                        (MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]));
    {
        // possibleVulnOutputs(s,b);
        var inputWitness := D(Int(1,IntType(4,false)));
        assert validInput(s,inputWitness);
        forall input | validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures !MiniSpec(b);
            ensures (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures !MiniSpec(b) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
            assert !MiniSpec(b);
            assert (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        }
        forall input | validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b)
            ensures MiniSpec(b);
            ensures !(behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures MiniSpec(b) <==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
        {
            var input :| validInput(s,input) && OperandContents(s,input).val >= 2 && BehaviorEvalsCode(codeVuln(input),b);
            var b' := unwrapVulnBehaviors(s,input);
            behaviorThatEvalsSameCodeWithSameInitIsEqual(s,codeVuln(input),b');
            assert MiniSpec(b);
            assert (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
            assert !(behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        }
        // assert !MiniSpec(b) ==> (behaviorOutput(b) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
    }
    lemma constrainedBehaviorSet(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires vulnOut == allBehaviorOutput(vulnBehaviors);
        ensures forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p)) ==> behaviorOutput(p) in vulnOut;
        {
            reveal_nonTrivialBehaviorPreconditionsVuln();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            reveal_behaviorOutput();
            forall p | behaviorOutput(p) in vulnOut
                ensures !MiniSpec(p) ==> behaviorOutput(p) in vulnOut;
            {
                if (MiniSpec(p)){
                    assert behaviorOutput(p) in vulnOut;
                }else{
                    assert !MiniSpec(p);
                    assert behaviorOutput(p) in vulnOut;
                }
            }
        }

    lemma allOutputConstrainedImpliesSameBehaviorOExists(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires vulnOut == allBehaviorOutput(vulnBehaviors);
        ensures forall v :: v in vulnBehaviors ==> (!MiniSpec(v) ==> (behaviorOutput(v) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
        ensures forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutput(vulnBehaviors,p);
    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        // reveal_existsSameOutput();
        // reveal_behaviorOutput();
        assert forall v :: v in vulnBehaviors  ==> (exists input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),v)));
        forall v | v in vulnBehaviors
            ensures !MiniSpec(v) ==> (behaviorOutput(v) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        {
            assert (exists input :: ( validInput(s,input) && BehaviorEvalsCode(codeVuln(input),v)));
            possibleVulnOutputsWithMiniSpec(s,v);
            assert (!MiniSpec(v) ==>  (exists input :: (validInput(s,input) && OperandContents(s,input).val < 2 && BehaviorEvalsCode(codeVuln(input),v))));
            assert !MiniSpec(v) ==> (behaviorOutput(v) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        } 


        forall p | behaviorOutput(p) in vulnOut
             ensures !MiniSpec(p) ==> behaviorOutput(p) in vulnOut;
        {
            if (MiniSpec(p)){
                assert behaviorOutput(p) in vulnOut;
            }else{
                assert !MiniSpec(p);
                assert behaviorOutput(p) in vulnOut;
            }
        }

        assert forall p :: constrainedBehavorSet(p,vulnOut) ==> behaviorInAll(behaviorOutput(p),vulnOut);// behaviorOutput(p) in vulnOut;
        assert forall p :: behaviorInAll(behaviorOutput(p),vulnOut) ==> existsSameOutput(vulnBehaviors,p);//(exists p' :: p' in vulnBehaviors && behaviorOutput(p) == behaviorOutput(p'));
        assert forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutput(vulnBehaviors,p);//(exists p' :: p' in vulnBehaviors && behaviorOutput(p) == behaviorOutput(p'));

    }

    predicate  existsSameOutput(vulnBehaviors:seq<behavior>,p:behavior)
    {
        exists p' :: p' in vulnBehaviors && behaviorOutput(p) == behaviorOutput(p')
    }

    predicate existsSameOutputConstrained(vulnBehaviors:seq<behavior>,p:behavior)
    {
        exists p' :: p' in vulnBehaviors && !MiniSpec(p') && behaviorOutput(p) == behaviorOutput(p')
    }
    predicate behaviorInAll(out:seq<output>,vulnOut:seq<seq<output>>)
    {
        out in vulnOut
    }

    predicate constrainedBehavorSet(b:behavior,vulnOut:seq<seq<output>>)
    {
        behaviorOutput(b) in vulnOut && !MiniSpec(b)
    }

    lemma patchIsCompleteTrivial(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>,patchOut:seq<seq<output>>)
        requires |vulnBehaviors| == 0
        requires |vulnOut| == 0
        requires ValidState(s);
        requires forall b :: b in vulnBehaviors <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s)
        requires forall b :: b in patchBehaviors <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codePatch(input),b) && b[0] == s)

        ensures forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut
        {
           
            assert |vulnBehaviors| == 0;
            assert |vulnOut| == 0;
            assert forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut;
            
        }

    lemma patchIsCompleteNonTrivial(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>,patchOut:seq<seq<output>>)
        requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
        requires |vulnBehaviors| > 0
        requires ValidState(s);
                    
        requires |patchBehaviors| > 0;

        requires vulnOut == allBehaviorOutput(vulnBehaviors);
        requires patchOut ==  allBehaviorOutput(patchBehaviors);

        ensures forall p :: p in vulnBehaviors && !MiniSpec(p) ==> (behaviorOutput(p) in vulnOut && behaviorOutput(p) in patchOut);
        // ensures forall p :: (behaviorOutput(p) in vulnOut && !MiniSpec(p))  ==> behaviorOutput(p) in patchOut
        // ensures forall p :: p in (reducedVulnModMS(s,vulnBehaviors,patchBehaviors,vulnOut)) ==> p in patchOut;
        {
            reveal_BehaviorEvalsCode();
            
            reveal_nonTrivialBehaviorPreconditionsVuln();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            
            
            forall p | (p in vulnBehaviors && !MiniSpec(p))
                ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                ensures behaviorOutput(p) in vulnOut;
                ensures behaviorOutput(p) in patchOut;
            {
                var input :| BehaviorEvalsCode(codeVuln(input),p) && |p| > 0 && validInput(p[0],input);
                var b' := unwrapVulnBehaviors(s,input);
                possibleVulnOutputsWithMiniSpec(s,p);
                assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert behaviorOutput(p) in vulnOut;

                var singlePatchBehavior :| singlePatchBehavior in patchBehaviors;
                var patchInput :| BehaviorEvalsCode(codePatch(patchInput),singlePatchBehavior) && |singlePatchBehavior| > 0 && validInput(singlePatchBehavior[0],patchInput);
                var patch' := unwrapPatchBehaviors(s,patchInput);
                outputIsEqual(behaviorOutput(patch'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert equalOutput(behaviorOutput(patch'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert behaviorOutput(patch') in patchOut;
                transitiveEquality(behaviorOutput(patch'),behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                equalOutputIsTransitive(behaviorOutput(patch'),behaviorOutput(p),patchOut);

            }
             forall p | p in patchBehaviors
                ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                ensures behaviorOutput(p) in patchOut;
             {
                var input :| BehaviorEvalsCode(codePatch(input),p) && |p| > 0 && validInput(p[0],input);
                var b' := unwrapPatchBehaviors(s,input);
                assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert behaviorOutput(p) in patchOut;

             }

            allOutputConstrainedImpliesSameBehaviorOExists(s,vulnBehaviors,patchBehaviors,vulnOut);
            assert forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutput(vulnBehaviors,p);
            var reduced := reducedVulnModMS(s,vulnBehaviors,patchBehaviors,vulnOut);

            // forall p :: (behaviorOutput(p) in aOut && !MiniSpec(p)) ==> behaviorOutput(p) in bOut
            // assert forall p :: p in reduced ==> (equalOutput(p,[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))])); 
            assert forall p :: p in reduced ==> equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            // assert forall p :: p in patchOut ==> equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            forall p | p in reduced
                ensures p in patchOut;
            {
                assert equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert exists b :: b in patchOut && equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                var b :| b in patchOut && equalOutput(b,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                assert b == p;
                assert p in patchOut;
            }
            assert forall p :: p in reduced ==> p in patchOut;

        }

            // assert (forall b :: behaviorOutput(b) in vulnOut <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));

    lemma reducedVulnModMS(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>) returns (moduloMSOut:seq<seq<output>>)
            requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
            requires vulnOut == allBehaviorOutput(vulnBehaviors);
            requires forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutput(vulnBehaviors,p);
            ensures forall reducedP :: reducedP in moduloMSOut ==> equalOutput(reducedP,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

    {
        reveal_nonTrivialBehaviorPreconditionsVuln();
        reveal_nonTrivialBehaviorPreconditionsPatch();
        assert (forall b :: b in vulnBehaviors <==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));
        assert forall i :: (i >= 0 && i < |vulnBehaviors|) ==> vulnOut[i] == behaviorOutput(vulnBehaviors[i]);
        var moduloMs :| vulnModMiniSpec(s,vulnBehaviors,moduloMs);
        // assert nonTrivialBehaviorPreconditionsVuln(s,test);
        assert forall p :: p in moduloMs ==> !MiniSpec(p);
        var reducedOut := allBehaviorOutput(moduloMs);
        forall p | p in moduloMs
            ensures equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            ensures behaviorOutput(p) in reducedOut;
        {
            possibleVulnOutputsWithMiniSpec(s,p);
            assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            assert behaviorOutput(p) in reducedOut;
        }
        assert forall reducedP :: reducedP in reducedOut ==> equalOutput(reducedP,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
        moduloMSOut := reducedOut;
    }

    predicate vulnModMiniSpec(s:state,vulnBehaviors:seq<behavior>,vulnBehaviorsConstrained:seq<behavior> ) //: vulnBehaviorsConstrained:seq<behavior> 
        requires ValidState(s);
        requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors)
        {
            && (forall p :: p in vulnBehaviorsConstrained ==> (!MiniSpec(p) && p in vulnBehaviors))
            && (forall b :: b in vulnBehaviorsConstrained ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s))

        }
////

lemma makeConnection(s:state,vulnBehaviors:seq<behavior>,patchBehaviors:seq<behavior>,vulnOut:seq<seq<output>>)
            requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
            requires vulnOut == allBehaviorOutput(vulnBehaviors);
            requires forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutput(vulnBehaviors,p);
            // requires forall p :: p in vulnBehaviors ==> (equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
            //                 || equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))])); 
            requires forall p :: p in vulnBehaviors ==> (!MiniSpec(p) <==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
    {
            reveal_nonTrivialBehaviorPreconditionsVuln();
            reveal_nonTrivialBehaviorPreconditionsPatch();
            reveal_behaviorOutput();

            forall p | constrainedBehavorSet(p,vulnOut)
                {
                    var p' :| p' in vulnBehaviors && behaviorOutput(p) == behaviorOutput(p');
                    possibleVulnOutputs(s,p');
                    possibleVulnOutputsWithMiniSpec(s,p');
                    assert (equalOutput(behaviorOutput(p'),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
                            || equalOutput(behaviorOutput(p'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
                    assert (equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
                            || equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
                    // assert !MiniSpec(p');
                    assert !MiniSpec(p);
                    assert MiniSpec(p') <==> equalOutput(behaviorOutput(p'),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
                    assert MiniSpec(p') ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
                    assert !MiniSpec(p') ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

                    // possibleVulnOutputsWithMiniSpec(s,p);
                    // assert MiniSpec(p) <==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]);
                }
    }

    ////
    // function vulnModMiniSpecCreate(s:state,vulnBehaviors:seq<behavior>) : (vulnBehaviorsConst:seq<behavior>)
    //     requires ValidState(s);
    //     requires nonTrivialBehaviorPreconditionsVuln(s,vulnBehaviors)
    //     decreases |vulnBehaviors|
    //     {
    //         reveal_nonTrivialBehaviorPreconditionsVuln();
    //         if |vulnBehaviors| == 0 then
    //             []
    //         else
    //             if !MiniSpec(vulnBehaviors[0]) then
    //                    assert (forall b :: b in all_but_first(vulnBehaviors) ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));

    //                 assert nonTrivialBehaviorPreconditionsVuln(s,all_but_first(vulnBehaviors));
    //                 var out := [vulnBehaviors[0]] + vulnModMiniSpecCreate(s,all_but_first(vulnBehaviors));
    //                 out
    //             else
    //                 vulnModMiniSpecCreate(s,all_but_first(vulnBehaviors))
    //             // out

    //     }

    // function allBehaviorOutputVuln(s:state,a:seq<behavior>) : (bOut:seq<seq<output>>)
    //     requires ValidState(s);
    //     // requires nonTrivialBehaviorPreconditionsVuln(s,a)
    //     requires (forall b :: b in a ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s))

    //     ensures |bOut| == |a|
    //     ensures forall a' :: a' in a ==> behaviorOutput(a') in bOut;
    //     ensures forall i :: (i >= 0 && i < |a|) ==> bOut[i] == behaviorOutput(a[i])
    //     ensures |a| == 0 ==> |bOut| == 0;
    //     //  ensures forall i :: (i >= 0 && i < |a|) ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s))
    //     // ensures forall i :: (i >= 0 && i < |a|) ==> (bOut[i] == behaviorOutput(a[i])
    //     //                                             && (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(a[i]) && BehaviorEvalsCode(codeVuln(input),a[i]) && a[i][0] == s))
    //     // ensures forall b :: behaviorOutput(b) in bOut ==> (exists a' :: a' in a && behaviorOutput(b) == behaviorOutput(a')); 
    //     ensures forall b :: behaviorOutput(b) in bOut ==> (exists b' :: b' in a && behaviorOutput(b) == behaviorOutput(b'));
        
    //     decreases |a|
    // {
    //     reveal_nonTrivialBehaviorPreconditionsVuln();
    //     // assert 
    //     if |a| == 0 then
    //         var out := [];
    //         // assert forall a' :: behaviorOutput(a') in out ==> a' in a;
    //         out
    //     else   
    //         var subset := all_but_first(a);
    //         if |subset| == 0 then
    //             var out := [behaviorOutput(a[0])];
    //             out
    //         else
    //             subsetProperty(s,subset);
    //             var out := [behaviorOutput(a[0])] + allBehaviorOutputVuln(s,subset);
    //             out
    // }

    // lemma subsetProperty(s:state,a:seq<behavior>)
    //     requires ValidState(s);
    //     requires |a| > 0
    //     requires (forall b :: b in a ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s))
    //     ensures (forall b :: b in all_but_first(a) ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));

    // {
    //    var subset := all_but_first(a);
    //    assert (forall b :: b in subset ==> (exists input :: validInput(s,input) &&  ValidBehaviorNonTrivial(b) && BehaviorEvalsCode(codeVuln(input),b) && b[0] == s));
            
    // }


    /// OLD


            // forall p | p in vulnBehaviors
            //     ensures (equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
            //                 || equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));                
            //     ensures !MiniSpec(p) <==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            //     ensures behaviorOutput(p) in vulnOut;
            //  {
            //     var input :| BehaviorEvalsCode(codeVuln(input),p) && |p| > 0 && validInput(p[0],input);
            //     var b' := unwrapVulnBehaviors(s,input);
            //     possibleVulnOutputs(s,b');
            //     possibleVulnOutputsWithMiniSpec(s,b');
            //     assert !MiniSpec(b') <==> equalOutput(behaviorOutput(b'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            //     assert (equalOutput(behaviorOutput(b'),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
            //                 || equalOutput(behaviorOutput(b'),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));                
            //     // assert equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            //     // assert behaviorOutput(p) in patchOut;
            //     assert behaviorOutput(p) in vulnOut;

            //  }
            // assert forall p :: p in vulnOut ==> equalOutput(p,[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) || equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);

            // assert forall p :: p in patchOut ==> equalOutput(p,[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            // assert forall p :: behaviorOutput(p) in patchOut ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
            
            // var p' :| 
            // assert forall i :: (i >= 0 && i < |vulnOut|) ==> vulnOut[i] == behaviorOutput(vulnBehaviors[i]);
            // assert forall v :: (v in vulnBehaviors && !MiniSpec(v)) ==> 
            //             ((behaviorOutput(v) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
            // assert forall p :: constrainedBehavorSet(p,vulnOut) ==> (equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(0,IntType(1,false)))),Out((Int(0,IntType(1,false))))]) 
            //                 || equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))])); 
            // assert forall p :: constrainedBehavorSet(p,vulnOut) ==> !MiniSpec(p); 

            // forall p | constrainedBehavorSet(p,vulnOut)
            // {
            //     var p' :| p' in vulnBehaviors && behaviorOutput(p) == behaviorOutput(p');
            // }
            // assert forall p :: constrainedBehavorSet(p,vulnOut) ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]);
                    
                    //   assert forall p :: constrainedBehavorSet(p,vulnOut) ==> existsSameOutputConstrained(vulnBehaviors,p);

            // assert forall p :: constrainedBehavorSet(p,vulnOut)==> ((behaviorOutput(p) == [Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))]));
            // assert forall i :: (i >= 0 && i < |vulnOut|) ==> (!MiniSpec(vulnBehaviors[i]) ==>  equalOutput(vulnOut[i],[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))] ));
            
            // assert (forall p :: behaviorOutput(p) in vulnOut ==> (exists input :: validInput(s,input) && BehaviorEvalsCode(codeVuln(input),p)));
            // assert forall p :: (p in vulnBehaviors && !MiniSpec(p)) ==> equalOutput(behaviorOutput(p),[Nil,Nil,Nil,Out((Int(1,IntType(1,false)))),Out((Int(1,IntType(1,false))))] );
            




}