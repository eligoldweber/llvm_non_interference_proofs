include "./ops.dfy"
include "./types.dfy"
include "./memory.i.dfy"
include "./Operations/conversionOperations.i.dfy"
include "./Operations/bitwiseBinaryOperations.i.dfy"
include "./Operations/binaryOperations.i.dfy"
include "./Operations/otherOperations.i.dfy"
include "../Libraries/SeqIsUniqueDef.i.dfy"
include "../Libraries/Seqs.s.dfy"


module LLVM_defRE {

    import opened types
    import opened ops
    import opened memory
    import opened Common__SeqIsUniqueDef_i
    import opened conversion_operations_i
    import opened bitwise_binary_operations_i
    import opened binary_operations_i
    import opened other_operations_i
    import opened Collections__Seqs_s



    type addr = int
    type LocalVar = string
    type GlobalVar = string

//-----------------------------------------------------------------------------
// Code Representation
//-----------------------------------------------------------------------------

    datatype state = State(
        lvs:map<LocalVar, Data>,
        gvs:map<GlobalVar, Data>,
        m:MemState,
        ok:bool)


///

    type codeSeq = seq<codeRe>

    datatype codeRe =
    | Ins(ins:ins)
    | Block(block:codeSeq)
    | IfElse(ifCond:bool, ifTrue:codeSeq, ifFalse:codeSeq)
    | CNil
            
    type behavior = seq<state>
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
        |b| >= 2 && b == [b[0]] + evalCodeRE(c,b[0])
    }
///

    function evalCodeRE(c:codeRe, s:state) : (b:behavior)
        ensures |b| > 0
        ensures (c.Ins?) ==> |b| == 1
        ensures c.Block? ==> |b| == |evalBlockRE(c.block, s)|
        ensures c.IfElse? ==> if c.ifCond then |b| == |evalBlockRE(c.ifTrue,s)| else |b| == |evalBlockRE(c.ifFalse,s)|
        
        ensures (c.Ins? && validEvalIns(c.ins,s,b[0]) && b[0].ok) ==> ValidBehavior([s] + b)
        
        decreases c, 0
    {
        match c
            case Ins(ins) => [evalInsRe(ins,s)]
            case Block(block) => evalBlockRE(block, s) 
            case IfElse(ifCond, ifT, ifF) => if ifCond then evalBlockRE(ifT, s) else evalBlockRE(ifF,s)
            case CNil => [s]
    }

//   function evalBlockRE(block:codeSeq, s:state): (b:behavior)
//         ensures |b| > 0
//         ensures (|block| == 0 || first(block).CNil?) ==> |b| == 1

//     {
//         if |block| == 0 || first(block).CNil? then
//             [s]
//         else
//             var metaBehavior := evalCodeRE(first(block),s);
//             var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
//             var fullBlock := metaBehavior + theRest;
//             assert |metaBehavior| == |evalCodeRE(first(block),s)|;
//             assert |theRest| == |evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)))|;
//             assert |fullBlock| == |metaBehavior| + |theRest|;

//             fullBlock
//     }
  function evalBlockRE(block:codeSeq, s:state): (b:behavior)
        ensures |b| > 0
        // ensures (first(block).CNil?) ==> |b| == 1

    {
        if |block| == 0 then
            [s]
        else
            assert |block| > 0;
            if first(block).CNil? then
                [s]
            else
                assert |block| > 0;
                var metaBehavior := evalCodeRE(first(block),s);
                assert |block| > 0;
                var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
                var fullBlock := metaBehavior + theRest;
                assert |metaBehavior| == |evalCodeRE(first(block),s)|;
                assert |theRest| == |evalBlockRE(all_but_first(block),last(evalCodeRE(first(block),s)))|;
                assert |fullBlock| == |metaBehavior| + |theRest|;

                fullBlock
    }

    function stateUpdateVar(s:state, dst:operand, d:Data): (s':state)
         requires dst.LV? || dst.GV?
         requires MemValid(s.m) 
         requires ValidData(s,d)
         ensures MemStateNext(s.m,s'.m,MemStep.stutterStep);
         ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
         ensures forall gv :: gv in s.gvs ==> gv in s'.gvs
         ensures dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
         ensures dst.GV? ==> forall gv :: (gv in s.gvs && gv != dst.g) ==> s'.gvs[gv] == s.gvs[gv]; 
         ensures ValidOperand(s',dst)

         {
             if dst.LV? then
                if (dst.l in s.lvs) then
                    var s' := s.(lvs := s.lvs[dst.l := d]);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    s'
                else
                    var s' := s.(lvs := s.lvs[dst.l := d]);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    s'
             else
                var s' := s.(gvs := s.gvs[dst.g := d]);
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    s'
         }

    function evalInsRe(ins:ins,s:state) : (s':state)
        // requires ValidInstruction(s, ins)
        // ensures ValidState(s) && ValidInstruction(s, ins) ==> StateNext(s,s')
        ensures s'.ok ==> NextStep(s,s',Step.evalInsStep(ins)) && StateNext(s,s');

    {
        if (!ValidState(s) || !ValidInstruction(s, ins)) then 
            var notOK := s.(ok := false);
            notOK
        else match ins
            case ADD(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalADD(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    // assert NextStep(s,s', Step.evalInsStep(ins));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    assert s'.ok;
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case SUB(dst,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    // assert NextStep(s,s', Step.evalInsStep(ins));
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    notOk
            case ICMP(dst,cond,t,src1,src2) => 
                var s' := stateUpdateVar(s,dst,evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)));
                if ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) then 
                    assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
                    assert validEvalIns(ins,s,s');
                    s'
                else
                    var notOk := s'.(ok := false);
                    assert NextStep(s,notOk, Step.errorStateStep());
                    notOk
    }
    
////

    datatype operand = D(d:Data) | LV(l:LocalVar) | GV(g:GlobalVar)
    
  
 datatype ins =
    | ADD(dst:operand, size:nat, src1ADD:operand, src2ADD:operand)
    | SUB(dst:operand, size:nat, src1SUB:operand, src2SUB:operand)
    | ICMP(dst:operand,cond:condition,size:nat,src1:operand,src2:operand)


    datatype behaviors = preBehavior(preB:behavior) | postBehavior(postB:behavior)

    function getBehavior(b:behaviors) : behavior
    {
        match b
            case preBehavior(preB) => preB
            case postBehavior(postB) => postB
    }

    predicate State_Init(s:state)
    {
        s.ok 
        && |s.lvs| == 0
        && |s.gvs| == 0
        && MemInit(s.m)    
    }

    predicate ValidData(s:state, d:Data)
    {    
        match d
            case Void => true
            case Int(val,itype) => IntFits(val,itype)
            case Bytes(bytes) => |bytes| > 0 && forall b :: b in bytes ==> 0 <= b < 0x100
            case Ptr(block,bid,offset,size) => && IsValidPtr(s.m,bid,offset,size) 
    }


    predicate ValidVarState(s:state,lvs:map<LocalVar, Data>,gvs:map<GlobalVar, Data>)
    {
        && (forall l:LocalVar :: l in lvs ==> ValidData(s,lvs[l]))
        && (forall g:GlobalVar :: g in gvs ==> ValidData(s,gvs[g]))
    }


    predicate ValidState(s:state)
    {
        && ValidVarState(s,s.lvs,s.gvs) 
        && MemValid(s.m) 
        && s.ok
    }

    datatype Step = 
    | evalInsStep(ins:ins)
    | stutterStep()
    | errorStateStep()

    predicate NextStep(s:state, s':state, step:Step)
    {
        match step  
            case evalInsStep(ins) => validEvalIns(ins,s,s') && s'.ok
            case stutterStep() => stutter(s,s')
            case errorStateStep() => errorStep(s,s')
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


    predicate ValidOperand(s:state,o:operand)
    {
        match o
            case D(d) => ValidData(s,d)
            case LV(l) => l in s.lvs && ValidData(s,s.lvs[l])
            case GV(g) => g in s.gvs && ValidData(s,s.gvs[g])
    }

    function method OperandContents(s:state, o:operand) : (out:Data)
        requires ValidOperand(s,o)
        requires ValidState(s)
    {

        
        match o
            case D(d) => d
            case LV(l) => s.lvs[l]
            case GV(g) => s.gvs[g]
           
    }

    predicate ValidInstruction(s:state, ins:ins)
    {
        ValidState(s) && match ins
            case ADD(dst,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case SUB(dst,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,dst) && ValidOperand(s,src1) && ValidOperand(s,src2) 
                                         && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                         && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
                                         && t == OperandContents(s,src1).itype.size
            case ICMP(dst,cond,t,src1,src2) => (dst.LV? || dst.GV?) && ValidOperand(s,src1) && ValidOperand(s,src2)
                                            && isInt(OperandContents(s,src1)) && isInt(OperandContents(s,src2))
                                            && t == OperandContents(s,src1).itype.size
                                            && typesMatch(OperandContents(s,src1),OperandContents(s,src2))
    }


    predicate evalUpdate(s:state, o:operand, data:Data, s':state)
        requires ValidState(s)
        requires ValidData(s',data)
        ensures evalUpdate(s, o, data, s') ==> ValidState(s')
    {
        
        
        match o
            case D(d) => data == d && s' == s 
            case GV(g) => s' == s.(gvs := s.gvs[g := data]) 
            case LV(l) => s' == s.(lvs := s.lvs[l := data]) 
            
    }


    predicate validEvalIns(ins:ins, s:state, s':state)
    {   
        && s.ok 
        && ValidInstruction(s, ins) 
        && match ins
            case ADD(dst,t,src1,src2) => ValidState(s')
                                && ValidData(s',evalADD(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalADD(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case SUB(dst,t,src1,src2) => ValidState(s') 
                                && ValidData(s',evalSUB(t,OperandContents(s,src1),OperandContents(s,src2))) 
                                && evalUpdate(s, dst, evalSUB(t,OperandContents(s,src1),OperandContents(s,src2)),s')
            case ICMP(dst,cond,t,src1,src2) => ValidState(s') 
                                && ValidData(s',evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)))
                                && evalUpdate(s, dst, evalICMP(cond,t,OperandContents(s,src1),OperandContents(s,src2)),s')
            
    }

    // Control flow 
        lemma unwrapBlock(b:behavior,block:codeSeq,s:state) 
            returns (step:behavior,remainder:codeSeq,subBehavior:behavior)
            requires b == [s] + evalBlockRE(block,s);
            // requires ValidState(s);
            ensures |step| > 0
            ensures (|block| > 0 && !first(block).CNil?) ==> (b == [s] + step + evalCodeRE(Block(remainder),last(step)));
            ensures (|block| > 0 && !first(block).CNil?) ==> subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
            ensures (|block| > 0 && !first(block).CNil?) ==> |remainder| == |block|-1
             ensures (|block| > 0 && !first(block).CNil?) ==> remainder == all_but_first(block);
            ensures |block| == 1 ==> |remainder| == 0;
            ensures (|block| > 0 && !first(block).CNil? && remainder == []) ==>  subBehavior == [last(step),last(step)];
            ensures (|block| > 0 && first(block).Ins?) ==> |step| == 1 
            // ensures 
            // requires |block| > 0;
            
        {
            if (|block| == 0 || first(block).CNil?) {
                assert b == [s,s];
                step := [s];
                remainder := [];

                subBehavior := b[|step|..];
                assert b == [s] + step + all_but_first(subBehavior);
                assert !ValidBehavior(step) ==> !ValidBehavior(b);
                assert NextStep(s,step[0], Step.stutterStep());
                assert ValidState(s) ==> ValidBehavior([s] + step);

            }else{
                assert !(|block| == 0 || first(block).CNil?);
                var metaBehavior := evalCodeRE(first(block),s);
                assert (first(block).Ins? && ValidInstruction(s,first(block).ins)) ==> ValidBehavior([s] + metaBehavior);
                var theRest := evalBlockRE(all_but_first(block),last(metaBehavior));
                assert evalBlockRE(block,s) == metaBehavior + theRest;
                assert b == [s] + evalBlockRE(block,s);
                assert b == [s] + metaBehavior + theRest;
                step := metaBehavior;
                // assert ValidBehavior(step);
                remainder := all_but_first(block);
                
                assert b[1..|step|+1] == step;
                subBehavior := b[|step|..];
                assert subBehavior == [last(step)] + evalBlockRE(remainder,last(step));
                assert evalBlockRE([],last(step)) == [last(step)];
                assert b == [s] + b[1..|step|] + b[|step|..];
                assert b == [s] + step + all_but_first(subBehavior);
            }
        }




    // ghost method testUpdateLV(s:state, o:operand, d:Data) returns (s':state)
    //     requires o.LV? 
    //     ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
    //     ensures forall lv :: (lv in s.lvs && lv != o.l) ==> s'.lvs[lv] == s.lvs[lv]; 
    //     // modifies o,d
    // {
    //     s' := s;
    //     if o.l in s.lvs {
    //         s' := s.(lvs := s.lvs[o.l := d]);
    //         assert forall lv :: (lv in s'.lvs && lv != o.l) ==> s'.lvs[lv] == s.lvs[lv];
    //         assert |s.lvs| ==  |s'.lvs|;
    //     }else{
    //         s' := s.(lvs := s.lvs[o.l := d]);
    //         assert |s.lvs| ==  |s'.lvs| - 1;
    //     }
    //     return s';
        
    // }

    // lemma a(s:state, o:operand)
    //      requires o.LV? 
    //      requires o.l in s.lvs
         
    // {
    //     var a := testUpdateLV(s,o,Int(16,IntType(4,false)));
    // }

    // function stateUpdateVar(s:state, dst:operand, d:Data): (s':state)
    //     //  requires dst.LV? || dst.GV?
    //      requires MemValid(s.m) 
    //      requires ValidData(s,d)
    //      ensures MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //      ensures forall lv :: lv in s.lvs ==> lv in s'.lvs
    //      ensures forall gv :: gv in s.gvs ==> gv in s'.gvs
    //      ensures dst.LV? ==> forall lv :: (lv in s.lvs && lv != dst.l) ==> s'.lvs[lv] == s.lvs[lv];
    //      ensures dst.GV? ==> forall gv :: (gv in s.gvs && gv != dst.g) ==> s'.gvs[gv] == s.gvs[gv]; 
    //      ensures ValidOperand(s',dst)

    //      {
    //          if dst.GV? then
    //             var s' := s.(gvs := s.gvs[dst.g := d]);
    //                 assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                 s'
    //          else 
    //             if dst.LV? then
    //                 if (dst.l in s.lvs) then
    //                     var s' := s.(lvs := s.lvs[dst.l := d]);
    //                     assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                     s'
    //                 else
    //                     var s' := s.(lvs := s.lvs[dst.l := d]);
    //                     assert MemStateNext(s.m,s'.m,MemStep.stutterStep);
    //                     s'
    //             else
    //                 assert dst.D?;
    //                 var s' := s;
    //                 assert ValidData(s',dst.d);
    //                 s'
    //      }

        // function evalBlockRE(block:codesRe, s:state): (b:behavior)
    //     ensures |b| > 0
    // {
    //     if block.CNil? || block.ForeignFunction? || (block.lvm_CodesRe? && |block.codeSeq| == 0) then
    //         [s]
    //     else
    //         var metaBehavior := evalCodeRE(first(block.codeSeq),s);
    //         assert |all_but_first(block.codeSeq)| < |block.codeSeq|;
    //         var theRest := evalCodeRE(Block(lvm_CodesRe(all_but_first(block.codeSeq))),last(metaBehavior));
    //         metaBehavior + theRest
    //         // evalBlockRE(lvm_CodesRe(all_but_first(block.codeSeq)),evalCodeRE(block.codeSeq[0],last(subBehavior)))
    //         // evalCodeRE(block.codeSeq[0],last(subBehavior)) + evalBlockRE(all_but_first(block.codeSeq))
    //         // exists r :: (evalCode(block.hd, s, r) && evalBlock(block.tl, r, s'))
    // }

    // predicate evalIfElseRE(cond:bool, ifT:codes, ifF:codes, s:state, s':state)
    //     decreases if ValidState(s) && cond then ifT else ifF
    // {
    //     if ValidState(s) && s.ok then
    //         exists r :: branchRelation(s, r, cond) && (if cond then evalBlock(ifT, r, s') else evalBlock(ifF, r, s'))
    //     else
    //         !s'.ok
    // }
    


}
