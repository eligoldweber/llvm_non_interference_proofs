include "../Libraries/Maps.i.dfy"



module FunctionComparison {
    import opened Collections__Maps_i

    datatype state = State(
        vals:map<string, int>,
        pc:int,
        ok:bool,
        out:set<int>)


    function valsToOut(s:state) : (outS:multiset<int>)
        decreases |s.vals|
        ensures |outS| == |s.vals|
        ensures forall key :: key in s.vals ==> s.vals[key] in outS
        ensures forall val :: val in outS ==> (exists key :: key in s.vals && s.vals[key] == val);
    {
        if |s.vals| == 0 then
            var outS:multiset<int> := multiset{};
            assert |outS| == |s.vals|;
            multiset{}
        else
            var key :| key in s.vals;
            var val := s.vals[key];
            var sub_s := s.(vals := RemoveElt(s.vals,key));
            lemma_map_remove_one(s.vals,sub_s.vals,key);
            assert |sub_s.vals| + 1 == |s.vals|;
            assert key in s.vals && !(key in sub_s.vals);
            var remainder := valsToOut(sub_s);
            var single:multiset<int> := multiset{s.vals[key]};
            assert key in s.vals;    
            var outS:multiset<int> :=  remainder + single;
            outS
    }

    lemma mergeState(s:state,r:state,f:map<string, int>-->map<string, int>) returns (m:state)
        ensures forall val :: val in m.vals ==> val in s.vals;
    {
        var sDomain := domain(s.vals);
        m := s.(pc := (s.pc + 1),ok := s.ok, vals := s.vals);
        assert forall z :: z in sDomain <==> z in m.vals;
        while (|sDomain| > 0)
            decreases |sDomain|
            invariant forall z :: z in sDomain ==> z in m.vals;
            invariant forall z :: z in sDomain ==> z in s.vals;
            invariant forall val :: val in m.vals ==> val in s.vals;
        {
            var val :| val in sDomain;
            assert val in m.vals;
            assert val in s.vals;
            m := m.(vals := m.vals[val := s.vals[val] + 1]);
            assert m.vals[val] == s.vals[val] + 1;
            sDomain := sDomain - {val};
        }
        // assert forall v :: v in m.vals ==> m.vals[v] == (s.vals[v] + 1);
    
        return m;
    }

    function mapTestUnion(a:map<string, int>,b:map<string, int>) : (out:map<string, int>)
        // ensures |out| >= |b|
    {
        var aDomain := domain(a);
        var bDomain := domain(b);
        if |a| == 0 && |b| == 0 then
            var out := map[];
            assert |out| >= |b|;
            out
        else 
            if |a| == 0 then
                var out := b;
                assert |out| >= |b|;
                out
            else
                if |b| == 0 then
                    assert |a| >= |b|;
                    var out := a;
                    assert |out| >= |b|;
                    out
                else
                    var bVal :| bVal in b;
                    if bVal in a then
                        var temp := map[bVal := b[bVal]];
                        var a' := RemoveElt(a,bVal);
                        var b' := RemoveElt(b,bVal);
                        var out := temp + mapTestUnion(a',b');
                        // assert |mapTestUnion(a,b)| > |mapTestUnion(a',b')|;
                        out
                    else
                        var temp := map[bVal := b[bVal]];
                        var b' := RemoveElt(b,bVal);
                        var out := temp + mapTestUnion(a,b');
                        out
    }

     lemma mergeStateFn(s:state,r:state,f:(map<string, int>,map<string, int>)-->map<string, int>) returns (m:state)
        requires f.requires(s.vals,r.vals)
        // ensures forall val :: val in m.vals ==> val in s.vals;
    {
        var sDomain := domain(s.vals);
        m := s.(pc := (s.pc + 1),ok := s.ok, vals := f(s.vals,r.vals));
        // assert forall z :: z in sDomain <==> z in m.vals;
        // while (|sDomain| > 0)
        //     decreases |sDomain|
        //     invariant forall z :: z in sDomain ==> z in m.vals;
        //     invariant forall z :: z in sDomain ==> z in s.vals;
        //     invariant forall val :: val in m.vals ==> val in s.vals;
        // {
        //     var val :| val in sDomain;
        //     assert val in m.vals;
        //     assert val in s.vals;
        //     m := m.(vals := m.vals[val := s.vals[val] + 1]);
        //     assert m.vals[val] == s.vals[val] + 1;
        //     sDomain := sDomain - {val};
        // }
        // assert forall v :: v in m.vals ==> m.vals[v] == (s.vals[v] + 1);
    
        return m;
    }

    lemma b (s:state,r:state)
        requires s.vals == map["a" := 1, "b" := 2, "c" := 3];
        requires r.vals == map["a" := 1, "c" := 3];
    {
        var out_s := valsToOut(s);
        var out_r := valsToOut(r);
        // assert "a" in s.vals;
        // assert 1 in out_s;
        // assert 1 in out_s;
        forall y | y in r.vals 
        {
            assert r.vals[y] in out_r;
            var z := r.vals[y];
            // assert y == 1 || y == 3;
            // assert exists xx :: xx in s.vals && xx == y;
            // assert exists x :: x in out_s && x == z;
        }
        // var m := mergeState(s,r);
        // assert m.vals == map["a" := 2, "b" := 3, "c" := 4];
        // assert forall y :: y in out_r ==> (exists x :: x in out_s && x == y);
    }

    lemma simpleIntSet(s:state) returns (out:set<int>)
        ensures forall elem :: elem in out ==> (exists key :: (key in domain(s.vals) && s.vals[key] == elem));
    {
        out := {};
        var valsDomain := domain(s.vals);
        assert forall d :: d in valsDomain ==> d in s.vals;
        while (valsDomain != {})
            invariant forall elem :: elem in out ==> (exists key :: (key in domain(s.vals) && s.vals[key] == elem));
            // invariant forall key :: key in s.vals ==> s.vals[key] in out;
        {
            var key :| key in valsDomain;
            assert key in s.vals;
            out := out + {s.vals[key]};
            valsDomain := valsDomain - {key};
            assert key in s.vals;
            assert s.vals[key] in out;
        }
        // forall key | key in s.vals
        // {
        //     assert s.vals[key] in out;
        // }
        // assert forall key :: key in s.vals ==> s.vals[key] in out;
        // assert forall elem :: elem in out <==> (exists key :: (key in domain(s.vals) && s.vals[key] == elem));
        return out;
    }

    // function test(s:state) : (out:set<int>)
    // {

    // }

     lemma IsBenign(s:state, s':state)
        requires s.out == {1,2,3};
        requires s'.out == {1,2,3};
    {
        assert forall x :: x in s'.out ==> x in s.out;
        // assert forall x :: x in s'Out ==> x in sOut;
    }

    // lemma IsBenign(s:state, s':state)
    //     requires s.vals == map["a" := 1, "b" := 2, "c" := 3];
    //     requires s'.vals == map["a" := 1, "b" := 2, "c" := 3];
    // {
    //     var sOut := simpleIntSet(s);
    //     var s'Out := simpleIntSet(s');
    //     assert forall x :: x in s'.vals ==> x in s.vals;
    //     var sOutTest := {1,2,3};
    //     forall elem | elem in sOutTest
    //         ensures exists key :: (key in s.vals && s.vals[key] == elem);
    //     {
    //         var key :| key in s.vals && s.vals[key] == elem;
    //     }
    //     assert forall elem :: elem in sOutTest ==> (exists key :: (key in s.vals && s.vals[key] == elem));
        
    //     forall x | x in s'Out
    //     {
    //         assert exists key :: (key in domain(s.vals) && s.vals[key] == x);
    //         assert exists key :: (key in domain(s'.vals) && s'.vals[key] == x);
    //         // var w :| w in s.vals && s.vals[w] in sOut && x == s.vals[w];

    //         // assert x in sOut;
    //     }
    //     // assert forall x :: x in s'Out ==> x in sOut;
    // }

}