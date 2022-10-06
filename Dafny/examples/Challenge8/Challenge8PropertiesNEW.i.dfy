include "Challenge8CodeNEW.s.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.dfy"
include "../../LLVM/behaviorLemmas.i.dfy"
include "../../Libraries/Seqs.s.dfy"
include "../../Libraries/Seqs.i.dfy"
include "../../LLVM/memory.i.dfy"
include "../../LLVM/Operations/binaryOperations.i.dfy"
include "../../LLVM/ops.dfy"

module challenge8Properties{
    import opened challenge8CodeNEW
    import opened LLVM_def_NEW
    import opened types
    import opened memory
    import opened behavior_lemmas
    import opened Collections__Seqs_s
    import opened Collections__Seqs_i
    import opened binary_operations_i
    import opened ops


    lemma returnBlockNoStutter(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validIntState(s);
        requires validConfig(s);
    {
        var config := allVariablesConfig();

        b := [s] + evalCodeFn(return_(),s);
        assert NextStep(b[0],b[1],evalInsStep((LOAD(config.ops["var_26"],1,config.ops["var_retval"]))));
        assert NextStep(b[1],b[2],evalInsStep((RET(config.ops["var_26"]))));
        assert |b| == 3;
        assert ValidBehavior(b);
    }

    lemma ifThen19NoStutter(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validIntState(s);
        requires validConfig(s);
        ensures b == [s] + evalCodeFn(if_then19(),s);
        ensures |b| == 5;
        ensures NextStep(b[0],b[1],evalInsStep((CALL(D(Void),delete_connection()))));
        ensures NextStep(b[1],b[2],evalInsStep((STORE(D(Int(0,IntType(1,false))),allVariablesConfig().ops["var_retval"]))));
        ensures NextStep(b[2],b[3],evalInsStep((LOAD(allVariablesConfig().ops["var_26"],1,allVariablesConfig().ops["var_retval"]))));
        ensures NextStep(b[3],b[4],evalInsStep((RET(allVariablesConfig().ops["var_26"]))));

{
    var config := allVariablesConfig();
    b := [s] + evalCodeFn(if_then19(),s);
    assert |b| == 5;
    assert NextStep(b[0],b[1],evalInsStep((CALL(D(Void),delete_connection()))));

    assert NextStep(b[1],b[2],evalInsStep((STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]))));
    var rB := returnBlockNoStutter(b[2]);
}






// Eval using Stutter Step // 
        lemma vulnRefactor(s:State,c:seq<Code>) returns (preB:Behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires c == challenge_8_transport_handler_create_conn_vuln_test();
        ensures ValidBehavior(preB);
        ensures |preB| == 8;
        ensures forall i :: i >=0 && i < |preB| - 1 ==> NextStep(preB[i],preB[i+1],Step.stutterStep());
        ensures preB == [s] + evalCodeSeqFn_Stutter(c,s);
    {
        //    [prefixCode(), Block([CNil]),postfixCode()]

        reveal_ValidBehavior();
        var b:Behavior := [s] + evalCodeSeqFn_Stutter(c,s);
        assert |b| == 8;
        assert ValidBehavior(b);
        forall i | i >=0 && i < |b| - 1
            ensures  NextStep(b[i],b[i+1],Step.stutterStep());
        {
            // assert NextStep(b[i],b[i+1],Step.stutterStep());
        }

        var prefixB :=  [s] + evalCodeFn_Stutter(prefixCode(),s);
        assert |prefixB| == 3;
        assert prefixB == b[..3];

        var midB :=  evalCodeFn_Stutter(Block([CNil]),last(prefixB));
        assert |midB| == 2;
        assert midB == b[3..5];

        var postfixB :=  evalCodeFn_Stutter(postfixCode(),last(midB));
        assert |postfixB| == 2;

        assert b == prefixB + midB + postfixB + [last(postfixB)];

        preB := b;

    }

    lemma behaviorIsSumOfParts(s:State,cseq:seq<Code>,b:Behavior)
        requires b == [s] + evalCodeSeqFn_Stutter(cseq,s)
        requires |cseq| > 1;
    {
        var smalB := b;
        assert smalB[..1] == [s];
        smalB := smalB[1..];
        // var index := 1;
        var i := 0;
        var subB := evalCodeFn_Stutter(cseq[i],s);
        assert smalB[..|subB|] == subB;
        
        smalB := smalB[|subB|..];

        assert evalCodeSeqFn_Stutter(cseq,s) == evalCodeFn_Stutter(first(cseq),s) + evalCodeSeqFn_Stutter(all_but_first(cseq),last(evalCodeFn_Stutter(first(cseq),s)));
        assert subB ==  evalCodeFn_Stutter(first(cseq),s);
        // assert evalCodeSeqFn_Stutter(all_but_first(cseq),last(evalCodeFn_Stutter(first(cseq),s))) == evalCodeFn_Stutter(first(all_but_first(cseq)),last(evalCodeFn_Stutter(first(cseq),s)))
        // index := 1+|subB|;
        // i := i +1;
        // subB := evalCodeFn_Stutter(cseq[i],last(subB));
        // assert b[..|subB|] == subB;
        // while i < |cseq|
        // {
        //     var subB := evalCodeFn_Stutter(cseq[i],b[index-1]);
        //     assert b[index..index+|subB|] == subB;
        //     index := index+|subB|;
        //     i := i +1;
        // }
    //    forall i | i >= 0 && i < |cseq|
    //    {
    //      var subB := evalCodeFn_Stutter(prefixCode(),b[index-1]);
    //      assert b[index..index+|subB|] == subB;
    //      index := index+|subB|;
    //    }
    }


    lemma fullPatch(s:State,size:Operand)returns (b:Behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires size.D?;
        requires size.d.Int?;
        requires size.d.itype == IntType(4,false);
        requires ValidOperand(s,size)
        requires validConfig(s);
        ensures b ==  [s] + evalCodeSeqFn_Stutter(challenge_8_transport_handler_create_conn_patch(size),s);
    {
        var config := allVariablesConfig();    
        b := [s] + evalCodeSeqFn_Stutter(challenge_8_transport_handler_create_conn_patch(size),s);   
        var prefixB :=  [s] + evalCodeFn_Stutter(prefixCode(),s);
        var mid := evalCodeFn_Stutter(patch_block(size),last(prefixB));
        // var post := evalCodeFn_Stutter(postfixCode(),last(mid));

        assert NextStep(b[0],b[1],Step.stutterStep());
        assert NextStep(b[1],b[2],Step.stutterStep());
        assert last(prefixB) == b[2];
        // assert b == prefixB + mid + post + [last(post)];
        assert b == prefixB + mid  + [last(mid)];

        // var x := patchBlock(b[2],size);
        // assert mid == all_but_first(x);

        // assert |post| == 2;
        // assert forall i :: i>= |b|-3 && i < |b| ==> b[i] == last(mid);
        // assert NextStep(b[3],b[4],evalInsStep((ICMP(config.ops["var_cmp17"],sgt,4,config.ops["var_num_packets"],config.ops["var_div"]))));
        // assert size.d.val/7 < (OperandContents(b[4],config.ops["var_num_packets"]).val) ==> !dataToBool(OperandContents(b[4],config.ops["var_cmp17"]));

    }

    predicate miniSpec(s:State,b:Behavior,size:Operand)
        requires size.D?;
        requires size.d.Int?;
        requires size.d.itype == IntType(4,false);
    {
       assert forall s :: |evalCodeFn_Stutter(postfixCodeSimple(),s)| == 4;
        var config := allVariablesConfig();

    //    && b == [s] + evalCodeFn_Stutter(patch_block(size),s)
        // && ValidBehavior(b)
       && ValidState(s)
       && validStartingState(s)
       && |b| >= 8
       && b[|b|-5..] == evalCodeFn_Stutter(postfixCodeSimple(),b[|b|-6]) + [last(b)]
       && FromTwosComp(UInt32(size.d.val/Int(7,IntType(4,false)).val % 0x8000_0000)).val < (OperandContents(s,config.ops["var_num_packets"]).val)
    }

    lemma vulnPostfixSimple(s:State,size:Operand) returns (b:Behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires size.D?;
        requires size.d.Int?;
        requires size.d.itype == IntType(4,false);
        requires ValidOperand(s,size)
        requires validConfig(s);
    {
        var config := allVariablesConfig();
        b := [s] + evalCodeSeqFn_Stutter(challenge_8_transport_handler_create_conn_vuln_postfix_simple(size),s);

    }
    lemma patchBlock(s:State,size:Operand) returns (b:Behavior)
        requires ValidState(s);
        requires validStartingState(s);
        requires size.D?;
        requires size.d.Int?;
        requires size.d.itype == IntType(4,false);
        requires ValidOperand(s,size)
        requires validConfig(s);
        ensures b ==  [s] + evalCodeFn_Stutter(patch_block(size),s);
        ensures |b| >= 8;
        ensures !miniSpec(s,b,size);
        // ensures ValidBehavior(b);
    {
        var config := allVariablesConfig();
        b := [s] + evalCodeFn_Stutter(patch_block(size),s);

        assert NextStep(b[0],b[1],evalInsStep((SDIV(config.ops["var_div"],size,D(Int(7,IntType(4,false)))))));
        // assert ValidState(b[1]);
        assert NextStep(b[1],b[2],evalInsStep((ICMP(config.ops["var_cmp17"],sgt,4,config.ops["var_num_packets"],config.ops["var_div"]))));
        if dataToBool(OperandContents(b[2],config.ops["var_cmp17"])){
            // assert evalCodeFn_Stutter(c.ifTrue,s);
            assert patch_block(size).block[2].IfElse?;
            var ifElseB := evalCodeFn_Stutter(patch_block(size).block[2].ifTrue,b[2]);
            assert b == [s] + [b[1]] + [b[2]] + ifElseB + [last(ifElseB)];
            var ifThen19:Behavior := ifThen19(b[2]);
            assert [b[2]] + evalCodeFn_Stutter(patch_block(size).block[2].ifTrue,b[2]) == ifThen19; 
            // assert b == [s] + [b[1]] + ifThen19 + [last(ifThen19)];
            // assert b[2..2+|ifThen19|] == ifThen19;
            // assert b[2..] == ifThen19 + [last(ifThen19)];
            assert NextStep(b[2],b[3],evalInsStep((CALL(D(Void),delete_connection()))));
            assert NextStep(b[3],b[4],evalInsStep((STORE(D(Int(0,IntType(1,false))),allVariablesConfig().ops["var_retval"]))));
            assert NextStep(b[4],b[5],evalInsStep((LOAD(allVariablesConfig().ops["var_26"],1,allVariablesConfig().ops["var_retval"]))));
            assert NextStep(b[5],b[6],evalInsStep((RET(allVariablesConfig().ops["var_26"]))));
            assert NextStep(b[6],b[7],Step.stutterStep());
            assert NextStep(b[7],b[8],Step.stutterStep());

            assert NextStep(b[8],b[9],Step.stutterStep());
            // assert OperandContents(b[9],allVariablesConfig().ops["var_26"]).val == 0;
            assert |b| == 10;
            assert !miniSpec(s,b,size);
        }else{
            assert NextStep(b[2],b[3],evalInsStep((STORE(D(Int(1,IntType(1,false))),allVariablesConfig().ops["var_retval"]))));
            assert NextStep(b[3],b[4],evalInsStep((LOAD(allVariablesConfig().ops["var_26"],1,allVariablesConfig().ops["var_retval"]))));
            assert NextStep(b[4],b[5],evalInsStep((RET(allVariablesConfig().ops["var_26"]))));
           
            assert NextStep(b[5],b[6],Step.stutterStep());
            assert NextStep(b[6],b[7],Step.stutterStep());
            // assert NextStep(b[4],b[5],Step.stutterStep());
            assert |b| == 8;
            assert !miniSpec(s,b,size);
        }
        // assert (OperandContents(b[2],config.ops["var_num_packets"]).val) > (OperandContents(b[2],config.ops["var_div"]).val) ==> dataToBool(OperandContents(b[2],config.ops["var_cmp17"]));
        // assert OperandContents(b[1],config.ops["var_div"]).val == FromTwosComp(UInt32(size.d.val/Int(7,IntType(4,false)).val % 0x8000_0000)).val;
        // assert OperandContents(b[1],config.ops["var_div"]).val > (OperandContents(b[1],config.ops["var_num_packets"]).val) ==> OperandContents(b[2],config.ops["var_cmp17"]).val == 0;
        // assert OperandContents(b[1],config.ops["var_div"]).val > (OperandContents(b[1],config.ops["var_num_packets"]).val) ==>!dataToBool(OperandContents(b[2],config.ops["var_cmp17"]));
        // assert FromTwosComp(UInt32(size.d.val/Int(7,IntType(4,false)).val % 0x8000_0000)).val > (OperandContents(b[1],config.ops["var_num_packets"]).val) ==> |b| == 8;
        // assert FromTwosComp(UInt32(size.d.val/Int(7,IntType(4,false)).val % 0x8000_0000)).val < (OperandContents(b[2],config.ops["var_num_packets"]).val) ==> !dataToBool(OperandContents(b[2],config.ops["var_cmp17"]));
    }

    lemma returnBlock(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validIntState(s);
        requires validConfig(s);
        ensures b == [s] + evalCodeFn_Stutter(return_(),s);
        ensures |b| == 4;
        ensures NextStep(b[0],b[1],evalInsStep((LOAD(allVariablesConfig().ops["var_26"],1,allVariablesConfig().ops["var_retval"]))));
        ensures NextStep(b[1],b[2],evalInsStep((RET(allVariablesConfig().ops["var_26"]))));
        ensures NextStep(b[2],b[3],Step.stutterStep());
    {
    var config := allVariablesConfig();

    b := [s] + evalCodeFn_Stutter(return_(),s);
    assert StateNext(b[0],b[1]);
    assert ValidState(b[1]);
    assert ValidState(b[2]);
    assert ValidState(b[3]);
    assert |b| == 4;
    assert NextStep(b[0],b[1],evalInsStep((LOAD(config.ops["var_26"],1,config.ops["var_retval"]))));
    assert NextStep(b[1],b[2],evalInsStep((RET(config.ops["var_26"]))));
    assert NextStep(b[2],b[3],Step.stutterStep());
}

lemma ifThen19(s:State) returns (b:Behavior)
    requires ValidState(s);
    requires validIntState(s);
    requires validConfig(s);
    ensures b == [s] + evalCodeFn_Stutter(if_then19(),s);
    ensures |b| == 7;
    ensures NextStep(b[0],b[1],evalInsStep((CALL(D(Void),delete_connection()))));
    ensures NextStep(b[1],b[2],evalInsStep((STORE(D(Int(0,IntType(1,false))),allVariablesConfig().ops["var_retval"]))));
    ensures NextStep(b[2],b[3],evalInsStep((LOAD(allVariablesConfig().ops["var_26"],1,allVariablesConfig().ops["var_retval"]))));
    ensures NextStep(b[3],b[4],evalInsStep((RET(allVariablesConfig().ops["var_26"]))));
    ensures NextStep(b[4],b[5],Step.stutterStep());
    ensures NextStep(b[5],b[6],Step.stutterStep());

{
    var config := allVariablesConfig();

    b := [s] + evalCodeFn_Stutter(if_then19(),s);
    assert |b| == 7;
    assert NextStep(b[0],b[1],evalInsStep((CALL(D(Void),delete_connection()))));
    // assert  ValidState(b[1]);
    // assert ValidInstruction(b[1], (CALL(D(Void),delete_connection())));
    // assert if_then19().block[1].Ins?;
    // assert MemValid(b[2].m);
    // assert if_then19().block[1].ins == (STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]));
    // assert NextStep(b[1],b[2],Step.stutterStep());
    assert NextStep(b[1],b[2],evalInsStep((STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]))));
    // assert if_then19().block[2].Block?;
    // assert if_then19().block[2] == return_();
    // assert [b[0],b[1],b[2]] == b[..3];
    // assert NextStep(b[2],b[3],evalInsStep((LOAD(config.ops["var_26"],1,config.ops["var_retval"]))));
    // assert NextStep(b[3],b[4],evalInsStep((RET(config.ops["var_26"]))));
    // assert NextStep(b[4],b[5],Step.stutterStep());
    // assert NextStep(b[5],b[6],Step.stutterStep());
    var rB := returnBlock(b[2]);
    assert NextStep(b[5],b[6],Step.stutterStep());
}

/// VV OLD  VV /// 


// lemma


//     lemma vulnBehavorsTest(s:State,c:seq<Code>) returns (preB:Behavior)
//         requires ValidState(s);
//         requires validStartingState(s);
//         requires c == challenge_8_transport_handler_create_conn_vuln_test();
//         // decreases *;
//     {
//         reveal_ValidBehavior();
//         //    [ Block([CNil]), Block([CNil]), Block([CNil])]
//         var b:Behavior := evalCodeSeqFn_Stutter(c,s);
//         assert ValidSimpleBehavior([s] + b);
//         assert |b| >= 0;
//         assert c == [ Block([CNil]), Block([CNil]), Block([CNil])];

//         var step,remainder,subB := unwrapCodeWitness(b,c,s);
//         assert step == evalCodeFn_Stutter(Block([CNil]),s);
//         assert remainder == [Block([CNil]), Block([CNil])];
//         // lets dive into the block
//             var subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s);
//             assert subStep == [s];
//             assert subRemainder == [];
//             assert subSubB == [s];
//             // unwrapped entire subBlock
//         assert step == subStep+subSubB;
//         assert b[..|step|] == step;

//         var s' := last(step);
//         step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
//         assert step == evalCodeFn_Stutter(Block([CNil]),s');
//         assert remainder == [ Block([CNil])];
//             // lets dive into the block
//             subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s');
//             assert subStep == [s'];
//             assert subRemainder == [];
//             assert subSubB == [s'];

//          assert step == subStep+subSubB;
//         assert couldBeSubSeq(b,step);

//         s' := last(step);
//         step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
//         assert step == evalCodeFn_Stutter(Block([CNil]),s');
//         assert remainder == [];

//         assert subB == [s'];
//         assert ValidBehavior(b);
//         assert NextStep(b[0],b[1],Step.stutterStep());
//         assert StateNext(b[0],b[1]);
//         assert NextStep(b[1],b[2],Step.stutterStep());
//         assert StateNext(b[1],b[2]);
//         assert |b| == 7;
//         preB := b;
//     }



// lemma patchBehavorsTest(s:State,c:seq<Code>) returns (postB:Behavior)
//         requires ValidState(s);
//         requires validStartingState(s);
//         requires c == challenge_8_transport_handler_create_conn_patch();
//         // decreases *;
//     {
//         reveal_ValidBehavior();
//         //    [ Block([CNil]), Block([CNil]), Block([CNil])]
//         // var b:Behavior := evalCodeSeqFn_Stutter(c,s);
//         // assert ValidSimpleBehavior([s] + b);
//         // assert |b| >= 0;
        
//         // var step,remainder,subB := unwrapCodeWitness(b,c,s);
//         // assert step == evalCodeFn_Stutter(Block([CNil]),s);
//         // // assert remainder == [patch_block,postfixCode()];
//         // // lets dive into the block
//         //     var subStep,subRemainder,subSubB := unwrapCodeWitness(step,[CNil],s);
//         //     assert subStep == [s];
//         //     assert subRemainder == [];
//         //     assert subSubB == [s];
//         //     // unwrapped entire subBlock
//         // assert step == subStep+subSubB;
//         // assert b[..|step|] == step;

//         // var s' := last(step);
//         // var mainBlock := remainder;
//         // // assert re
//         // step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
//         // assert remainder == [ Block([CNil])];
//         //  // lets dive into the block
//         //     assert step == evalCodeFn_Stutter(first(mainBlock),s');
//         //     assert first(mainBlock).Block?;
//         //     assert step == evalCodeSeqFn_Stutter(first(mainBlock).block,s');

//         //     // assert step == evalCodeSeqFn_Stutter(first(mainBlock),s');
//         //     subStep,subRemainder,subSubB := unwrapCodeWitness(step,first(mainBlock).block,s');
//         //     assert |subStep| == 1;
//         //     assert s'.ok;
//         //     assert first(mainBlock).block[0].Ins?;
//         //     assert first(mainBlock).block[0].ins.SDIV?;
//         //     assert ValidOperand(s',first(mainBlock).block[0].ins.dst);
//         //     var testIns := first(mainBlock).block[0].ins;
                
//         //     assert ValidInstruction(s', first(mainBlock).block[0].ins);
//         //     assert NextStep(s',subStep[0],Step.evalInsStep(first(mainBlock).block[0].ins));
//         //     // assert subRemainder == [];
//         //     assert b[1] == s';
//         //     assert b[2] == subStep[0];  
//         //     s' := subStep[0];
//         //     var nextIns := subRemainder;
//         //     subStep,subRemainder,subSubB := unwrapCodeWitness(subSubB,subRemainder,s');
//         //     assert |subStep| == 1;
//         //     assert NextStep(s',subStep[0],Step.evalInsStep(first(nextIns).ins));
//         //     assert b[3] == subStep[0];
//         //     assert ValidInstruction(s', first(nextIns).ins);

//         //     s' := subStep[0];
//         //     nextIns := subRemainder;
//         //     assert first(subRemainder).IfElse?;
//         //     assert validIfCond(s',first(subRemainder).ifCond);
//         //         //unwrap branch
//         //     assert |subRemainder| > 0;
//         //     subStep,subRemainder,subSubB := unwrapCodeWitness(subSubB,subRemainder,s');
             
//         //         if dataToBool(OperandContents(s',first(nextIns).ifCond)){
//         //             assert subStep == evalCodeFn_Stutter(first(nextIns).ifTrue,s');
//         //             // new block that needs unwrapping 
//         //             patchBehavorsTestsubBlock(subStep,first(nextIns).ifTrue,s');
//         //             // var if_true_block := first(nextIns).ifTrue;
//         //             // var step_if_then19,remainder_if_then19,subB_if_then19 := unwrapCodeWitness(subStep,if_true_block.block,s');
//         //             // assert |step_if_then19| == 1;
//         //             // assert first(if_true_block.block).Ins?;
//         //             // assert first(if_true_block.block).ins.CALL?;
//         //             // assert NextStep(s',step_if_then19[0],Step.evalInsStep(first(if_true_block.block).ins));

//         //             // var if_true_next := first(remainder_if_then19);
//         //             // s' := first(step_if_then19); 
//         //             // step_if_then19,remainder_if_then19,subB_if_then19 := unwrapCodeWitness(subB_if_then19,remainder_if_then19,s');
//         //             // assert |step_if_then19| == 1;
//         //             // assert NextStep(s',step_if_then19[0],Step.evalInsStep((if_true_next).ins));
//         //             // assert |remainder_if_then19| == 1;


//         //         }else{
//         //             assert subStep == evalCodeFn_Stutter(first(nextIns).ifFalse,s');
//         //             assert subRemainder == [];
//         //             assert subSubB == [s']; 
//         //             assert b[4] == subStep[0]; 
//         //             assert b[5] == subStep[0];
//         //             assert |b| == 10;
//         //         }
        
//         // s' := last(step);
//         // step,remainder,subB := unwrapCodeWitness(subB,remainder,s');
//         // assert step == evalCodeFn_Stutter(Block([CNil]),s');
//         // assert remainder == [];

//         // assert subB == [s'];


//     }

//     lemma {:opaque} patchBehavorsTestsubBlock(b:Behavior,c:Code,s:State)
//         requires c == if_then19();
//         requires ValidState(s);
//         requires validConfig(s,allVariablesConfig());
//         requires b == evalCodeSeqFn_Stutter(c.block,s);
//         ensures  first(c.block).Ins?;
//         ensures first(c.block).ins.CALL?;
        
        
//     {
//         var Behavior := evalCodeSeqFn_Stutter(c.block,s);
//         var initalCode := c.block;
//         var step,remainder,subB := unwrapCodeWitness(b,c.block,s);
//         assert |step| == 1;
//         assert first(initalCode).Ins?;
//         assert first(initalCode).ins.CALL?;
//         assert StateNext(s,step[0]);
//         // assert step == [evalInsRe(first(initalCode).ins,s)];
//         // assert s.ok;
//         assert NextStep(s,step[0],Step.evalInsStep(first(initalCode).ins));
//         initalCode := remainder;
//         var s' := step[0];
//         assert ValidState(s');
//         step,remainder,subB := unwrapCodeWitness(subB,remainder,last(step));
//         assert |step| == 1;
//         assert first(initalCode).Ins?;
//         assert first(initalCode).ins.STORE?; 
//         // assert ensures first(c.block).ins.STORE?;
//         // assert s'.ok;
//         // assert ValidOperand(s',first(initalCode).ins.valueToStore);
//         // assert ValidOperand(s',first(initalCode).ins.ptr);
//         // assert ValidInstruction(s',first(initalCode).ins);
//         // assert NextStep(s',step[0],Step.evalInsStep(first(initalCode).ins));

//         // assert false;
//     }


    // lemma patchBehaviors(s:State,c:codeRe) returns (postB:Behavior)
    //     requires ValidState(s);
    //     requires validStartingState(s);
    //     requires c == challenge_8_transport_handler_create_conn_patch();
        
    //     ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),postB);
    // {
    //     reveal_BehaviorEvalsCode();
    //     assert |c.block| == 3;
    //     postB := [s] + evalBlockRE(c.block,s);

    //     assert first(c.block).Block?;
    //     assert c.Block?;
    //     var metaBehavior := evalCodeRE(first(c.block),s);
    //     // assert postB == [s] + metaBehavior + evalBlockRE(all_but_first(c.block),last(metaBehavior));
    //    ///
    //     assert first(c.block) == Block([CNil]);
    //     assert first(c.block).Block?;
    //     assert metaBehavior == [s] + evalBlockRE(first(c.block).block, s); 
    //     var tempMeta := evalCodeRE(CNil,s);
    //     assert tempMeta == [s];
    //     assert metaBehavior == [s] + [s] + evalBlockRE([],s);
    //     assert metaBehavior == [s,s,s];
    //     // assert postB == [s] + [s] + [s] + evalBlockRE([patchBlock(),postfixCode()],s);
    //     // assert metaBehavior == evalCodeRE(CNil,s) + evalBlockRE([],s);
    // ////
    //     var step,remainder,subBehavior := unwrapBlockWitness(postB,c.block,s);
    //     // assert subBehavior == metaBehavior;
    //     assert postB[0] == s; 
    //     assert first(remainder).CNil?;
    //     assert NextStep(postB[0],postB[1],Step.stutterStep());
    //     assert StateNext(postB[0],postB[1]);
    //     assert postB[1] == last(step);
    //     assert step == [s];
    //     assert remainder == [CNil] + all_but_first(c.block);
    //     assert all_but_first(c.block) == [patchBlock(),postfixCode()];
    //     // assert subBehavior == [s] + evalBlockRE(remainder,s);
    //     assert evalBlockRE(remainder,s) == [s] + evalBlockRE([patchBlock(),postfixCode()],s);
    //     // assert postB == [s] + [postB[1]] + evalCodeRE(Block(remainder) ,last(step));
    //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
    //     assert remainder == all_but_first(c.block);
    //     assert |remainder| == 2;
    //     assert remainder == [patchBlock(),postfixCode()];
    //     assert step == [s];
    //             // assert postB[2] == last(step);

    //     assert NextStep(postB[1],last(step),Step.stutterStep());
    //     assert last(step) == postB[1];
    //     // assert StateNext(postB[1],postB[2]);
        
    //     step,remainder,subBehavior := unwrapBlockWitness(subBehavior,remainder,last(step));
    //     // assert remainder == [patchBlock(),postfixCode()];


    //     // assert postB[2] == evalInsRe(CALL(D(Void),delete_connection()),postB[1]);
    //     // assert NextStep(postB[1],postB[2],Step.stutterStep());
    //     // assert StateNext(postB[1],postB[2]); 
    //     // assert |preB| == 5;
    //     // assert ValidBehaviorNonTrivial(postB); 
    // }

    //     // benignPatch: "The patch does not add any NEW behaviors"
    // predicate benignPatch(pre:set<Behavior>,post:set<Behavior>)
    // {
    //     var preOutput := allBehaviorOutputSet(pre);
    //     var postOutput := allBehaviorOutputSet(post);
    //     forall postB :: postB in postOutput ==> postB in preOutput
    // }

    // lemma equalPrefixBlocksEvalEquallyAndAreBenign(blockA:codeRe,blockB:codeRe)
    //     requires blockA == blockB
    //     ensures forall s :: ValidState(s) ==> evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    //     ensures forall s :: ValidState(s) ==> benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
    // {
    //     forall s | ValidState(s)
    //         ensures evalCodeRE(blockA,s) == evalCodeRE(blockB,s);
    //         ensures benignPatch({evalCodeRE(blockA,s)},{evalCodeRE(blockB,s)});
    //     {
    //         var b_a := evalCodeRE(blockA,s);
    //         var b_b := evalCodeRE(blockB,s);
    //         assert b_a == b_b;
    //         assert benignPatch({b_a},{b_b});
    //     }
    // }

    // // Proof
    // function vulnified(s:State) : (s_vuln:State)
    // {
    //     // assume exists vuln :: BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln) && |vuln| > 0;
    //     // var vuln :| BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),vuln);
    //     // assume exists s_vuln :: s_vuln in vuln;
    //     // var s_vuln :| s_vuln in vuln;
    //     // s_vuln
    //     s
    // }

    // function patchified(s:State) : State
    // {
    //     s
    // }

    // function mapPatchedToVuln(patchedBehavior:Behavior) : (mappedBehavior:Behavior)
    //     // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),patchedBehavior)
    //     ensures |patchedBehavior| == |mappedBehavior|
    //     ensures forall i :: (i >= 0 && i < |patchedBehavior|) ==> mappedBehavior[i] == vulnified(patchedBehavior[i])
    //     //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    // {
    //     //placeholder
    //     if(|patchedBehavior| == 0) then
    //         var mappedBehavior := [];
    //         mappedBehavior
    //     else 
    //         var rest := mapPatchedToVuln(all_but_first(patchedBehavior));
    //         var mappedBehavior := [vulnified(patchedBehavior[0])] + rest;
    //         mappedBehavior
        
    // }

    //  function mapVulnToPatched(vulnBehaviors:Behavior) : (mappedBehavior:Behavior)
    //     // requires BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),patchedBehavior)
    //     ensures |vulnBehaviors| == |mappedBehavior|
    //     ensures forall i :: (i >= 0 && i < |vulnBehaviors|) ==> mappedBehavior[i] == patchified(vulnBehaviors[i])
    //     //ensures BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patched(),mappedBehavior)
    // {
    //     //placeholder
    //     if(|vulnBehaviors| == 0) then
    //         var mappedBehavior := [];
    //         mappedBehavior
    //     else 
    //         var rest := mapVulnToPatched(all_but_first(vulnBehaviors));
    //         var mappedBehavior := [patchified(vulnBehaviors[0])] + rest;
    //         mappedBehavior
        
    // }

    // predicate canMapToVuln(patchedBehavior:Behavior)
    // {
    //     var mappedBehavior := mapPatchedToVuln(patchedBehavior);
    //     BehaviorEvalsCode(challenge_8_transport_handler_create_conn_vuln(),mappedBehavior)
    // }

    // predicate canMapToPatch(vulnBehavior:Behavior)
    // {
    //     var mappedBehavior := mapVulnToPatched(vulnBehavior);
    //     BehaviorEvalsCode(challenge_8_transport_handler_create_conn_patch(),mappedBehavior)
    // }

    // lemma patchIsBenign(vuln:codeRe,patch:codeRe)
    //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     //ensures forall b :: BehaviorEvalsCode(patch,b) ==> canMapToVuln(b)
    // {

    // }

    // predicate miniSpec(b:Behavior)
    // {
    //     true
    // }

    // lemma patchIsSuccesful(patch:codeRe)
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     // ensures forall b :: BehaviorEvalsCode(patch,b) ==> !miniSpec(b)
    // {

    // }
    
    // //     predicate completePatch(pre:set<System_s.Behavior>,post:set<System_s.Behavior>)
    // // {
    // //     // forall p :: (p in a && !MiniSpec(p)) ==> p in b

    // //     var preOutput := allBehaviorOutputSet(pre);
    // //     var postOutput := allBehaviorOutputSet(post);
    // //     forall preB :: (behaviorOutput(preB) in preOutput && !MiniSpec(preB)) ==> behaviorOutput(preB) in postOutput
    // // }

    // lemma patchIsComplete(vuln:codeRe,patch:codeRe)
    //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    //     requires patch == challenge_8_transport_handler_create_conn_patch();
    //     // ensures forall b :: BehaviorEvalsCode(vuln,b) && !miniSpec(b) ==> canMapToPatch(b);
    // {

    // }

    // // lemma patchIsBenign(s:State,vuln:codeRe,patch:codeRe)
    // //     requires ValidState(s)
    // //     requires vuln == challenge_8_transport_handler_create_conn_vuln();
    // //     requires patch == challenge_8_transport_handler_create_conn_patch();
    // //     // requires nonTrivialBehaviorPreconditions(s,vulnBehaviors,patchBehaviors)
    // //     // ensures benignPatch(vulnBehaviors,patchBehaviors)
    // // {
    // //     prefixAndPostfixAreEqual();
    // //     assert benignPatch({evalCodeRE(vuln.block[0],s)},{evalCodeRE(patch.block[0],s)});
    // //     assert |vuln.block| == |patch.block|;
    // //     var prefix_vuln_s := last(evalCodeRE(vuln.block[0],s));
    // //     var prefix_patch_s := last(evalCodeRE(patch.block[0],s));
    // //     assert prefix_vuln_s == prefix_patch_s;
    // //     var evalVuln := evalCodeRE(vuln,s);
    // //     // assert forall r :: r in evalVuln ==> r == s;
    // //     // assert forall i :: (&& i >= 0 
    // //     //                    && i < |vuln.block|
    // //     //                    && benignPatch({evalCodeRE(vuln.block[i],s)},{evalCodeRE(patch.block[i],s)}))
    // //     //                    ==> benignPatch({evalCodeRE(vuln,s)},{evalCodeRE(patch,s)});
        
    // // }

}

