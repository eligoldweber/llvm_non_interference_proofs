

module surectiveSets
{
// lemma in question

lemma setIsSurjective(vulnBehaviors:set<behavior>,allVulnOut:set<seq<output>>)
    requires allVulnOut == allBehaviorOutputSet(vulnBehaviors)
    requires |vulnBehaviors| > 0
    ensures forall vulnOut :: vulnOut in allVulnOut ==> (exists vulnB :: vulnB in vulnBehaviors && behaviorOutput(vulnB) == vulnOut)
{
    assert SurjectiveOver(vulnBehaviors,allVulnOut, x => behaviorOutput(x));
    forall vulnOut | vulnOut in allVulnOut
        ensures exists vulnB :: vulnB in vulnBehaviors && behaviorOutput(vulnB) == vulnOut;
    {
        assert exists vulnB :: vulnB in vulnBehaviors && behaviorOutput(vulnB) == vulnOut;
        var vulnB :| vulnB in vulnBehaviors && behaviorOutput(vulnB) == vulnOut;
    }
}


// simplified datatypes
    datatype state = State(o:output,ok:bool)
    datatype output = Out(o:int) | Nil
    type behavior = seq<state>



// Behavior Lemmas // 

    // behavior(seq<state>) --> seq<output>
    function {:opaque} behaviorOutput(b:behavior) : (bOut:seq<output>)
        ensures |bOut| == |b| 
        ensures forall i :: (i >= 0 && i < |b|) ==> bOut[i] == b[i].o
        decreases |b|
    {
        if |b| == 0 then
            []
        else 
            [b[0].o] + behaviorOutput(all_but_first(b))
    }

    // a set of all 'outputs' from a set of behaviors
    // set<behavior> --> set<seq<output>>
    function  allBehaviorOutputSet(bSet:set<behavior>) : (allBOut:set<seq<output>>)
        ensures SurjectiveOver(bSet,allBOut, x => behaviorOutput(x));
        ensures forall b :: b in bSet ==> behaviorOutput(b) in allBOut;
        ensures |bSet| > 0 ==> |allBOut| > 0
        ensures |bSet| == 0 ==> |allBOut| == 0;
        decreases |bSet|
    {
        reveal_behaviorOutput();
        if |bSet| == 0 then
            var out := {};
            assert forall b :: behaviorOutput(b) in out ==> (exists elem :: elem in bSet && behaviorOutput(elem) == behaviorOutput(b));
            out
        else   
             var behavior :| behavior in bSet;
             var bSubset := bSet - {behavior};
             var singleOutput := {behaviorOutput(behavior)};
             var rest := allBehaviorOutputSet(bSubset);
             var out := singleOutput + rest;
             subsetUnion(singleOutput,rest,behaviorOutput(behavior));
             out

    }


/// SET/SEQ LEMMAS
    predicate SurjectiveOver<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
        reads f.reads
        requires forall x :: x in xs ==> f.requires(x)
    {
        forall y :: y in ys ==> (exists x :: x in xs && f(x) == y)
    }

    lemma ItIsASingletonSet<T>(foo:set<T>, x:T)
        requires foo=={x}
        ensures |foo|==1
    {
    }

    lemma subsetUnion<T>(x:set<T>, y:set<T>,foo:T)
        requires x=={foo}
        ensures foo in (x+y);
    {
        ItIsASingletonSet(x,foo); 
        assert foo in (x+y);
    }


    function all_but_first<T>(s:seq<T>): (t:seq<T>)
        requires |s| > 0
        ensures |all_but_first(s)| == |s| - 1
    {
        s[1..]
    }
    
////




}