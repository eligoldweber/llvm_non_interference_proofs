include "../../LLVM/llvmREFACTOR.i.dfy"
include "../../LLVM/types.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../LLVM/Operations/binaryOperations.i.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../LLVM/Operations/otherOperations.i.dfy"

module diff{
    import opened types
    import opened LLVM_defRE
    import opened binary_operations_i
    import opened Collections__Seqs_s
    import opened behavior_lemmas
    import opened other_operations_i

     function codeVuln(x:operand):codeRe
    {
        var z := LV("z");
        var result := LV("result");

        var y := D(Int(2147483646,IntType(4,false)));

        var cSeq := [Ins(ADD(z,4,x,y)),
                     Ins(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }
    
    function codePatch(x:operand):codeRe
    {
        var z := LV("z");
        var result := LV("result");

        var y := D(Int(2147483646,IntType(4,false)));

        var cSeq := [Ins(ADD(z,4,x,y)),
                     Ins(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false))))),
                     Ins(RET(result))];
        Block(cSeq)
    }


    predicate validInput(s:state, input:operand)
        requires ValidState(s)
    {
        && s.o.Nil?
        && ValidOperand(s,input)
        && isInt(OperandContents(s,input))
        && typesMatch(OperandContents(s,D(Int(0,IntType(4,false)))),OperandContents(s,input))
        && OperandContents(s,input).val >= 0 
        && OperandContents(s,input).val <= 2
    }

    predicate RemovedBehaviors(b:behavior)
    {

        && ValidBehaviorNonTrivial(b)
        && exists s:state,result:operand :: (&& s in b
                                            && last(b) == s 
                                            && ValidState(s)
                                            && result.LV?
                                            && result.l == "result"
                                            && result.l in s.lvs
                                            && ValidOperand(s,result)
                                            && OperandContents(s,result).Int?
                                            && OperandContents(s,result).val == 0)
    }

    predicate rb(b:behavior)
    {
        && ValidBehaviorNonTrivial(b)
        && exists s:state,s':state, result:operand, val:operand :: (&& s in b 
                                                                    && s' in b 
                                                                    && result.LV?
                                                                    && result.l in s.lvs
                                                                    && val.LV?
                                                                    && val.l in s.lvs 
                                                                    && NextStep(s,s',Step.evalInsStep(ICMP(result,sgt,4,val,D(Int(0,IntType(4,false))))))
                                                                    && ValidOperand(s',result)
                                                                    && OperandContents(s',result).Int?
                                                                    && OperandContents(s',result).val == 0)
    }            

    predicate aoi(b:behavior)
    {
        && ValidBehaviorNonTrivial(b)
        && exists s:state,s':state, icmpIns:ins :: (&& s in b 
                                                    && s' in b
                                                    && icmpIns.ICMP?
                                                    && ValidInstruction(s,icmpIns)
                                                    && OperandContents(s,icmpIns.src1).val > 0
                                                    && OperandContents(s,icmpIns.src2).val == 0
                                                    && (icmpIns.cond == sgt || icmpIns.cond == ugt)
                                                    && icmpIns.dst.LV?
                                                    && icmpIns.dst.l in s.lvs
                                                    && NextStep(s,s',Step.evalInsStep(icmpIns)))
    } 

    //trusted
    predicate aoiSection(aoiIns:codeRe)
    {
        && aoiIns.Ins?
        && aoiIns.ins.ICMP?
        && (aoiIns.ins.cond == sgt || aoiIns.ins.cond == ugt)
        && aoiIns.ins.dst.LV?
    }

    predicate modAoiSame(s:state, pre:codeSeq,post:codeSeq)
    {
        && |pre| > 0
        && |post| > 0
        && |pre| >= |post|
        && codeLengthModAOIFn(s,pre) == codeLengthModAOIFn(s,post)
        && forall i :: (i >=0 && i <|pre| && i <|post| && !aoiSection(pre[i])) ==> pre[i] == post[i]
        // forall i :: i >= 0 && i < 
    }

    predicate modAOISameV2(s:state, pre:codeSeq,post:codeSeq)
    {
        && |pre| > 0
        && |post| > 0
        && codeLengthAOIFn(s,pre) == codeLengthAOIFn(s,post)
        && forall i :: (i >=0 && i <|pre| && i <|post| && !aoiSection(pre[i])) ==> pre[i] == post[i]
    }
    function codeLengthModAOIFn(s:state, code:codeSeq) : (len:int)
        ensures len >= 0 &&  len <= |code|
    {
        var len := 0;
        var i := 0;
        if |code| == 0 then
            len
        else
            if !aoiSection(code[i]) then
                // len := 
                (1 + codeLengthModAOIFn(s,all_but_first(code)))
            else
                codeLengthModAOIFn(s,all_but_first(code))
                // len
    }

    function codeLengthAOIFn(s:state, code:codeSeq) : (len:int)
        ensures len >= 0 &&  len <= |code|
    {
        var len := 0;
        var i := 0;
        if |code| == 0 then
            len
        else
            if aoiSection(code[i]) then
                // len := 
                (1 + codeLengthAOIFn(s,all_but_first(code)))
            else
                codeLengthAOIFn(s,all_but_first(code))
                // len
    }


    lemma codeLengthModAOI(s:state, pre:codeSeq) returns (len:int)
        requires |pre| > 0;
        ensures len >= 0 &&  len <= |pre|
    {
        len := 0;
        var i := 0;
        while (i < |pre|)
            invariant len >= 0;
            invariant len <= i;
            invariant len <= |pre|;
        {
            if(!aoiSection(pre[i])){
                len := len + 1;
            }
        
            assert i <= |pre|;
            i := i + 1;
            assert i >= len;
            assert len <= |pre|;

        }

    }

    predicate MiniSpec(b:behavior)
    {
        RemovedBehaviors(b)
    }
    lemma setOfDifferentIndecies(s:state, pre:codeSeq,post:codeSeq) returns (diffs:seq<int>)
        requires |post| > 0 && |pre| > 0;
        ensures forall i :: i in diffs ==> i < |post|
        ensures forall i :: i in diffs ==> i < |pre|
        ensures forall i :: i in diffs ==> i >= 0
        ensures forall i :: i in diffs ==> pre[i] != post[i];
        ensures forall j :: (!(j in diffs) && j >=0 && j < |pre| && j < |post|) ==> pre[j] == post[j]
    {
        diffs := [];
        var i := 0;
        while(i < |pre| && i < |post|)
            invariant i >= 0; 
            invariant i <= |pre|
            invariant i <= |post|
            invariant forall i :: i in diffs ==> i >=0
            invariant forall i :: i in diffs ==> i < |pre|
            invariant forall i :: i in diffs ==> i < |post|
            invariant forall i :: i in diffs ==> pre[i] != post[i];
            invariant forall j :: (!(j in diffs) && j >=0 && j < |pre| && j < |post| && j < i) ==> pre[j] == post[j]

        {
            if(post[i] != pre[i]){
                diffs := diffs + [i];
                assert i in diffs;
            }else{
                assert post[i] == pre[i];
                assert !(i in diffs);
            }
            i := i + 1;
        }
    }

    lemma firstDifferentIndex(s:state, pre:codeSeq,post:codeSeq) returns (diff:int)
        requires |post| > 0 && |pre| > 0;

        ensures diff >= 0;
        ensures diff <= |post| 
        ensures diff <= |pre| 
        ensures (forall i :: (i >=0 && i < diff) ==> post[i] == pre[i]);
        ensures forall d :: (d >= 0 && d < |post|) ==> post[d] == post[d];
        ensures (diff >= 0 && diff < |pre| && diff < |post|) ==> (post[diff] != pre[diff]);
    {
        diff := 0;
        if(|post| >= |pre|){
            
            while (diff < |pre| && post[diff] == pre[diff])
                invariant diff >= 0
                invariant diff <= |pre|
                invariant (forall i :: (i >=0 && i < diff) ==> post[i] == pre[i])
            {
                if(post[diff] != pre[diff]){
                    assert diff < |pre|;
                }else{
                    diff := diff + 1;
                }
              
            }
            assert diff < |pre| ==> post[diff] != pre[diff];
            assert (forall i :: (i >=0 && i < diff) ==> post[i] == pre[i]);
        }else{
            assert |post| < |pre|;
             while (diff < |post| && post[diff] == pre[diff])
                invariant diff >= 0
                invariant diff <= |post|
                invariant (forall i :: (i >=0 && i < diff) ==> post[i] == pre[i])
            {
                if(post[diff] != pre[diff]){
                    // break;
                    assert diff < |post|;
                }else{
                    diff := diff + 1;
                }
              
            }
            assert diff < |post| ==> post[diff] != pre[diff];
            assert (forall i :: (i >=0 && i < diff) ==> post[i] == pre[i]);
        }
        assert  (diff < |pre| && |post| >= |pre|) ==> (post[diff] != pre[diff]);
        assert  (diff < |post| && |post| < |pre|) ==> (post[diff] != pre[diff]);
        // return index;
    }



    lemma sameCodeSeqImpliesSameBehavior(s:state, pre:codeRe,post:codeRe)
        requires pre.Block?;
        requires post.Block?;
        requires |post.block| == |pre.block|
        requires forall i :: (i >= 0 && i < |pre.block|) ==> post.block[i] == pre.block[i];
        ensures  ([s] + evalCodeRE(post,s)) == ([s] + evalCodeRE(pre,s))
    {
        var postSeq := post.block;
        var preSeq := pre.block;
        var postB := [s] + evalCodeRE(post,s);
        var preB := [s] + evalCodeRE(pre,s);

        assert postSeq == preSeq;
        assert preB == postB;
    }

    lemma iDiffSubCode(s:state,input:operand)
        requires ValidState(s);
        requires validInput(s,input);
    {
        var preC := codeVuln(input);
        var postC := codePatch(input);
        var pre := preC.block;
        var post := postC.block;
        var idiff := firstDifferentIndex(s,pre,post);

        var pre' := pre[idiff..];
        var post' := post[idiff..];
        assert |pre'| < |pre|;
        assert |post'| < |post|;
        var preB := [s] + evalCodeRE(preC,s);
        // assert aoi(preB);
    }



    lemma iDiffTest() 
    {
        forall s:state, input:operand | ValidState(s) && validInput(s,input)
        {
            var preC := codeVuln(input);
            var postC := codePatch(input);
            var pre := preC.block;
            var post := postC.block;
            var idiff := firstDifferentIndex(s,pre,post);
            var idiffs := setOfDifferentIndecies(s,pre,post);
            assert pre[0] == post[0];
            assert post[1] != pre[1];
            assert !(|post| == 0 || |pre| == 0);
            // 

            assert idiff < |post|;
            assert idiff < |pre|;//&& |post| < |pre|
            assert (forall i :: (i >=0 && i < idiff) ==> post[i] == pre[i]);
            assert idiff <= 1;
            assert idiff >= 0;
            assert |post| >= |pre|;
            assert (post[idiff] != pre[idiff]);
            // assert (idiff >= 0 && idiff < |pre| && |post| >= |pre|) ==> (post[idiff] != pre[idiff]);
            assert idiff == 1;
            assert pre[1].Ins?; 
            assert aoiSection(pre[1]);
            assert modAoiSame(s,pre,post);
            assert modAOISameV2(s,pre,post);
                        assert |idiffs| > 0;

        }
    }

    lemma modAoiSameEqualImpliesBenign(input:operand, s:state, pre:codeSeq,post:codeSeq)
        requires modAoiSame(s,pre,post);
        requires pre == codeVuln(input).block;
        requires post == codePatch(input).block;
        requires ValidState(s);
        requires validInput(s,input);
    {

        reveal_ValidBehavior();
         var z := LV("z");
            var result := LV("result");
            var y := D(Int(2147483646,IntType(4,false)));
        var fullPreB := [s] + evalCodeRE(codeVuln(input),s);
        assert |pre| == 3;
        assert |post| == 3;
        assert pre[0] == post[0];
        assert pre[2] == post[2];
        assert pre[1] != post[1];
        var p,test := evalCodeTest(codeVuln(input).block,s);
        assert p.ok ==> ValidBehavior(test);
        assert test[0] == s;
        assert codeVuln(input).block[0] == Ins(ADD(z,4,input,y));
        
        // assert p.ok  ==> |test| > 1;
        // assert test[1] ==  evalInsRe(ADD(z,4,input,y),s);

        // assert evalCodeRE((post[0]),s) == evalCodeRE((pre[0]),s);
        var postB  := [s] + evalCodeRE(Block([post[0]]),s);
        var preB  := [s] + evalCodeRE(Block([pre[0]]),s);
        // assert preB == postB;
        // assert |postB| == 3;
        var step,remainder, subBehavior := unwrapBlockWitness(postB,Block([post[0]]).block,s);
        // assert postB[0] == s;
        // assert postB[1] == evalInsRe(ADD(z,4,input,y),s);
        // assert OperandContents(postB[1],z).val == OperandContents(s,input).val + OperandContents(s,y).val;
        // assert postB[1] == postB[2];
        // assert |postB| == 3;
        // assert forall ss :: ss in postB ==> ValidState(ss);
        // assert NextStep(s,postB[1], Step.evalInsStep(ADD(z,4,input,y))); 
        // assert NextStep(postB[1],postB[2],Step.stutterStep());
        // assert ValidBehavior(postB);
        // assert StateNext(s,postB[0]);
        assert postB[2] == preB[2];
        // // var preB' := [postB[2]] + evalCodeRE((pre[1]),postB[2]);
        // var preB' := [preB[2]] + evalCodeRE(Block([pre[1]]),preB[2]);
        // assert preB' == [preB[2]] + evalBlockRE(Block([pre[1]]).block,preB[2]);
        // step,remainder, subBehavior := unwrapBlockWitness(preB',Block([pre[1]]).block,preB[2]);
        // assert |preB'| == 3;
        
        // assert post[1].Ins?;
        // var postB' := [postB[2]] + evalCodeRE(Block([post[1]]),postB[2]);
        // assert postB' == [postB[2]] + evalBlockRE(Block([post[1]]).block,postB[2]);
        // step,remainder, subBehavior := unwrapBlockWitness(postB',Block([post[1]]).block,postB[2]);
        // assert |postB'| == 3;
        
        // assert preB'[0] == postB'[0];
        // assert post[1] == Ins(ICMP(result,ugt,4,z,D(Int(0,IntType(4,false)))));
        // assert pre[1] == Ins(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))));
        // assert preB'[1] == evalInsRe(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))),preB'[0]);
        // assert preB'[0].ok;
        // assert preB'[1].ok;
        // assert ValidInstruction(preB'[0],ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))));
        // assert OperandContents(preB'[0],z).val == OperandContents(s,input).val + OperandContents(s,y).val;
        // assert OperandContents(s,input).val == 2 ==> OperandContents(preB'[0],z).val == 2147483648;

        // assert OperandContents(preB'[0],z).val == 2147483648 ==> OperandContents(preB'[1],result).val != 1;
        // assert  OperandContents(preB'[1],result) == evalICMP(sgt,4,OperandContents(preB'[0],z),(Int(0,IntType(4,false))));
        // assert evalICMP(sgt,4,(Int(2147483649,IntType(4,false))),(Int(0,IntType(4,false)))).val == 0 ;
        // assert OperandContents(preB'[0],z).val == 2147483649 ==> preB'[1] == postB'[1];
        // assert OperandContents(preB'[0],z).Int?;
        // assert forall v :: (v >= 0 && v < 2 && OperandContents(s,input).val == v ) ==> preB' == postB';
        // // assert if OperandContents(preB'[0],z).val == 2147483649 then (evalICMP(sgt,4,OperandContents(preB'[0],z),(Int(0,IntType(4,false)))).val == 10) else false;
        // // assert preB' != postB';
        // ass

       
        forall s1:state | ValidState(s1) && s1 == s
        {
            var pre1 := evalCodeRE((pre[0]),s1);
            var post1 := evalCodeRE((post[0]),s1);
            // assert pre1[0] == preB[2];
            assert |pre1| == 1;
            assert pre1[0] == evalInsRe(ADD(z,4,input,y),s1);
            // assert pre1[0] == preB[1];
            // assert pre1[0] == preB[2];
                        assert !aoiSection((post[0]));

            assert (post1 == pre1);

        } // var x := t();

        forall s2:state | ValidState(s2) && s2 ==  preB[2] &&  (OperandContents(s,input).val == 0 || OperandContents(s,input).val == 1)//&& OperandContents(s,input).val == 0
        {
            var pre2 := evalCodeRE((pre[1]),s2);
            var post2 := evalCodeRE((post[1]),s2);
            assert aoiSection((post[1]));
            assert ValidOperand(s2,z);
            assert pre2[0] == evalInsRe(ICMP(result,sgt,4,z,D(Int(0,IntType(4,false)))),s2);
            assert OperandContents(s2,z).val == OperandContents(s,input).val + OperandContents(s,y).val;
            assert OperandContents(s2,z).val == 2147483648 ==> OperandContents(pre2[0],result).val != 1;
            assert forall v :: OperandContents(s,input).val == v && (v == 1 || v == 0) ==> OperandContents(pre2[0],result).val == OperandContents(post2[0],result).val;
            assert (post2 == pre2);

        }

        forall s3:state | ValidState(s3)
        {
            var pre3 := evalCodeRE((pre[2]),s3);
            var post3 := evalCodeRE((post[2]),s3);
            
            assert (post3 == pre3);

        }
        forall s3:state | ValidState(s3)
        {
            var pre3 := evalCodeRE((pre[2]),s3);
            var post3 := evalCodeRE((post[2]),s3);
            
            assert (post3 == pre3);

        }
    }   

    method t() returns (x:int)
    {
        return 5;
    }

    

// Old 

    // lemma diff(pre:codeSeq,post:codeSeq) returns (d:codeSeq)
    //     ensures (|post| >= |pre|) ==> (forall z :: z in d ==> z in post);
    //     ensures forall p :: (p in post && !(p in pre)) ==> p in d;
    // {
    //     var diffBlock := [];
    //     if(|pre| == 0){
    //         return post;
    //     }
    //     if(|post| == 0){
    //         return pre;
    //     }
    //     assert |post| > 0 && |pre| > 0;
    //     var remainder :=  diff(all_but_first(pre),all_but_first(post));
    //     if(pre[0] != post[0]){ 
    //         diffBlock := [post[0]] + remainder;
    //         return diffBlock;
    //     }
    //     // if(|pre| >= |post|){
    //     //     diffBlock := 
    //     // }
    //     return remainder;
    // }



    // lemma samePrefixBehavior(s:state, pre:codeRe,post:codeRe) returns (diff:int)
    //     requires pre.Block?;
    //     requires post.Block?;
    //     ensures (|post.block| == 0 || |pre.block| == 0) ==> diff == 0
    //     // ensures diff >= 0 &&  diff <= |pre.block| && diff <= |post.block|
    //     // ensures forall i :: i >= 0 && i < diff ==> post.block[i] == pre.block[i];
    //     // ensures !(|post.block| == 0 || |pre.block| == 0) ==> (diff >= 0 &&  diff <= |post.block| && diff <= |pre.block| && (forall i :: (i >=0 && i < diff) ==> post.block[i] == pre.block[i]))
    // {
    //     var postSeq := post.block;
    //     var preSeq := pre.block;
    //     var postB := [s] + evalCodeRE(post,s);
    //     var preB := [s] + evalCodeRE(pre,s);

    //     var iDiff := 0;

    //     if(|postSeq| == 0 || |preSeq| == 0)
    //     {
    //         return iDiff;
    //     }else{
    //         assert |postSeq| > 0 && |preSeq| > 0;
    //         if(|postSeq| >= |preSeq|){
    //             if (forall preIndex :: (preIndex >= 0 && preIndex < |preSeq| ) ==> postSeq[preIndex] == preSeq[preIndex]){
    //                 iDiff := |preSeq|;
    //             }else{
    //                 assert exists i :: i >=0 && i < |preSeq| && preSeq[i] != postSeq[i];//  && (forall j :: (j >=0 && j < i) ==> postSeq[j] == preSeq[j]);
    //             // iDiff :| && iDiff >= 0 
    //             //         && iDiff < |preSeq| 
    //             //         && (forall i :: (i >=0 && i < iDiff) ==> postSeq[i] == preSeq[i])
    //             //         && postSeq[iDiff] != preSeq[iDiff];
    //             }
    //         }else{
    //             // assert |preSeq| > |postSeq|;
    //             // if (forall postI :: (postI >= 0 && postI < |postSeq| ) ==> postSeq[postI] == preSeq[postI]){
    //             //     iDiff := |postSeq|;
    //             // }else{
    //             //     assert exists i :: i >=0 && i < |postSeq| && preSeq[i] != postSeq[i];
    //             // }
    //         }
    //         // iDiff :| && iDiff >= 0 
    //         //          && iDiff < |postSeq| 
    //         //          && iDiff < |preSeq| 
    //         //          && (forall i :: (i >=0 && i <= iDiff) ==> postSeq[i] == preSeq[i])
    //         //          && (forall i :: (i > iDiff && i < |postSeq| && i < |preSeq|) ==> postSeq[i] != preSeq[i]);
    //         // assert (postSeq[0] == preSeq[0]) ==> iDiff > 0;
    //     }

    //      return iDiff;
    // }

    // lemma diffV2(pre:codeSeq,post:codeSeq) returns (preD:codeSeq,postD:codeSeq)
    //     // ensures (|post| >= |pre|) ==> (forall z :: z in d ==> z in post);
    //     // ensures forall p :: (p in post && !(p in pre)) ==> p in postD;
    //     ensures |preD| == |postD|
    // {
    //     var preDiffBlock := [];
    //     var postDiffBlock := [];
    //     if(|pre| == 0){
    //         preD := post;
    //         postD := post; 
    //         return;
    //     }
    //     if(|post| == 0){
    //         preD := pre;
    //         postD := pre;
    //         return;
    //     }
    //     assert |post| > 0 && |pre| > 0;
    //     var remainderPre,remainderPost :=  diffV2(all_but_first(pre),all_but_first(post));
    //     if(pre[0] != post[0]){
    //         assert pre != post;
    //         preD := [pre[0]] + remainderPre; 
    //         postD := [post[0]] + remainderPost;
    //         // assert  post[0] in post && !(post[0] in pre);
    //         return;
    //     }
    //     preD := preDiffBlock;
    //     postD := postDiffBlock;
    //     return;
    // }



}