include "llvm.i.dfy"
include "types.s.dfy"
include "memory.i.dfy"

// Adapted from Vale
module control_flow {
    import opened LLVM_def
    import opened types
    import opened memory

predicate evalCodeOpaque(c:code, s0:state, sN:state) 
    { evalCode(c, s0, sN) }

predicate evalCode_lax(c:code, s0:state, sN:state) 
    { s0.ok ==> evalCodeOpaque(c, s0, sN) }

function method lvm_CNil():codes { CNil }
function method lvm_Block(block:codes):code { Block(block) }

function method void_Operand():operand {var o := Void; D(o)}


function lvm_update_ok(sM:lvm_state, sK:lvm_state):state { sK.(ok := sM.ok) }
function lvm_update_local(l:LocalVar, sM:lvm_state, sK:lvm_state):lvm_state
    requires l in sM.lvs
{ sK.(lvs := sK.lvs[l := sM.lvs[l]]) }
function lvm_update_global(g:GlobalVar, sM:lvm_state, sK:lvm_state):lvm_state
    requires g in sM.gvs
{ sK.(gvs := sK.gvs[g := sM.gvs[g]]) }
function lvm_update_mem(sM:lvm_state, sK:lvm_state):lvm_state {
    sK.(m := sK.m.(mem := sM.m.mem))
}
function lvm_update_all(sM:lvm_state, sK:lvm_state):lvm_state{
    sK.(m  := sK.m.(mem := sM.m.mem),
       ok  := sM.ok,
       gvs := sM.gvs,
       lvs := sM.lvs)
}

predicate eval_code(c:code, s:state, r:state)
{
    s.ok ==> evalCode(c, s, r)
}

lemma lvm_lemma_empty(s0:state, sN:state) returns(sM:state)
    // requires evalCode_lax(lvm_Block(lvm_CNil()), s0, sN, void_Operand())
    requires  eval_code(lvm_Block(lvm_CNil()), s0, sN)
    ensures  s0.ok ==> sN.ok
    ensures  sM == s0
    ensures  s0.ok ==> sN == s0
{
    sM := s0;
}

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil?  && !block.ForeignFunction?{
        var r' :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        lemma_FailurePreservedByCode(block.hd, s, r');
        lemma_FailurePreservedByBlock(block.tl, r', r);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r);
    }
}
lemma a(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires ValidState(s);
    requires c.Ins?;
    requires r.ok;
{
 assert ValidInstruction(s,c.ins) ==> ValidState(r);
}

lemma code_state_validity(c:code, s:state, r:state)
    requires evalCode(c, s, r);
    requires ValidState(s);
    decreases c, 0;
    ensures  r.ok ==> ValidState(r);
{
    if r.ok {
        assert s.ok;
        if c.Ins? {
            // assert !s.ok ==> !r.ok;
            assert evalIns(c.ins,s,r);
            assert s.ok;
            assert ValidInstruction(s,c.ins);
            assert r.ok;
            assert evalIns(c.ins,s,r);
            // assert c.ins.RET? ==> ValidState(r);

            assert MemValid(r.m);
            assert ValidState(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r);
        } else if c.IfElse? {
                var s' :| branchRelation(s, s', c.ifCond) &&
                    if c.ifCond then
                        evalBlock(c.ifTrue, s', r)
                    else
                        evalBlock(c.ifFalse, s', r);
                if c.ifCond {
                    block_state_validity(c.ifTrue, s', r);
                } else {
                    block_state_validity(c.ifFalse, s', r);
                }
            assert ValidState(r);
        } 
        // else if c.While? {
        //     var n:nat :| evalWhile(c.whileCond, c.whileBlock, n, s, r);
        //     evalWhile_validity(c.whileCond, c.whileBlock, n, s, r);
        //     assert ValidState(r);
        // }
    }
}

// lemma evalWhile_validity(b:bool, c:codes, n:nat, s:state, r:state)
//     requires evalWhile(b, c, n, s, r);
//     decreases c, 1, n;
//     ensures  ValidState(s) && r.ok ==> ValidState(r);
// {
//     if ValidState(s) && r.ok && n > 0 {
//         var s', r' :| b && branchRelation(s, s', true) && evalBlock(c, s', r') && evalWhile(b, c, n - 1, r', r);
//         block_state_validity(c, s', r');
//         evalWhile_validity(b, c, n - 1, r', r);
//         assert ValidState(r);
//     }
// }

lemma block_state_validity(block:codes, s:state, r:state)
    requires evalBlock(block, s, r);
    requires ValidState(s);
    decreases block, 0;
    ensures  r.ok ==> ValidState(r);
{
    if block.lvm_Codes? {
        var r':state :| evalCode(block.hd, s, r') && evalBlock(block.tl, r', r);
        code_state_validity(block.hd, s, r');
        if r'.ok {
            block_state_validity(block.tl, r', r);
        }
        else {
            lemma_FailurePreservedByBlock(block.tl, r', r);
        }
    }
}


    // function evalBlockBehavior(block:codes, s:state, s':state,b:behavior): (out:behavior)
    //     requires evalBlock(block,s,s');
    //     requires ValidState(s);
    //     requires |b| > 0 ==> bls(b) == s;
    //     requires s.ok ==> ValidBehavior(b);
    //     // ensures s.ok ==> ValidBehavior(out);
    // {
    //     // assert evalBlock(block,s,s');
    //     if block.CNil? || block.ForeignFunction? then
    //        assert s' == s;
    //        b
    //     else
    //         assert evalBlock(block,s,s');
    //         assert exists r :: (evalCode(block.hd, s, r) && evalBlock(block.tl, r, s'));
    //         var r :| (evalCode(block.hd, s, r) && evalBlock(block.tl, r, s'));
    //         code_state_validity(block.hd,s,r);
    //         assert r.ok ==> ValidState(r);
    //         if ValidState(r) then
    //             var b' := (evalCodeBehavior(block.hd, s, r, b) + evalBlockBehavior(block.tl,r,s',[r]));
    //             // assert ValidBehavior(evalCodeBehavior(block.hd, s, r, b));
    //             // assert bls((evalCodeBehavior(block.hd, s, r, b))) == r;
    //             // assert ValidBehavior(evalBlockBehavior(block.tl,r,s',[r]));
    //             // assert ValidBehavior(b');
    //             b'
    //         else 
    //             b
    //         // assert StateNext(s,r);
    //         // var b' := b + [r];
    //         // assert ValidState(r) ==> ValidBehavior(b');
            
            
    // }

                            //  assert (s.ok  && ValidInstruction(s,ins)) ==> evalIns(ins, s, s');
                            //  assert (s.ok  && ValidInstruction(s,ins)) ==> NextStep(s,s',evalInsStep(ins));
                            //     //  assert (s.ok  && ValidInstruction(s,ins)) ==> MemStateNext(s.m,s'.m,MemStep.stutterStep());
                            //  assert (s.ok  && ValidInstruction(s,ins)) ==>  StateNext(s,s');
    // function evalCodeBehavior(c:code,s:state, s':state, b:behavior): (out:behavior)
    //      requires evalCode(c,s,s')
    //      requires ValidBehavior(b)
    //      requires |b| > 0 ==> bls(b) == s;
    //      ensures s.ok ==> ValidBehavior(out);
    //      ensures (c.Ins? &&  s.ok  && ValidInstruction(s,c.ins)) ==> |out| > 0 && bls(out) == s';
    //      decreases c, 0
    // {
    //     match c
    //         case Ins(ins) => 
    //         // assert (s.ok  && ValidInstruction(s,ins)) ==> NextStep(s,s',evalInsStep(ins));
    //         // assert (s.ok  && ValidInstruction(s,ins)) ==> evalIns(ins, s, s');
    //         // assert (s.ok  && ValidInstruction(s,ins)) ==>  StateNext(s,s');
    //                          if (s.ok  && ValidInstruction(s,ins)) then
    //                             assert NextStep(s,s',evalInsStep(ins));
    //                             assert StateNext(s,s');
    //                             assert ValidState(s');
    //                             var b' := b + [s'];
    //                             assert ValidBehavior(b');
    //                             assert |b'| > 0;
    //                             b'
    //                         else
    //                             b
    //         case Block(block) => b //  evalCodeBlockImpliesEvalBlock(c, s, s');
    //                             //   assert evalBlock(block,s,s');
    //                             //   evalBlockBehavior(block,s,s',b)//evalBlockBehavior(block, s, s')
    //         case IfElse(ifCond, ifT, ifF) => b//evalIfElse(ifCond, ifT, ifF, s, s')
    // }




lemma lvm_lemma_block_lax(b0:lvm_codes, s0:state, sN:state) 
                returns(s1:state, c1:lvm_code, b1:lvm_codes)
    requires b0.lvm_Codes?
    requires evalCode_lax(lvm_Block(b0), s0, sN)
    ensures  b0 == lvm_Codes(c1, b1)
    ensures  evalCode_lax(c1, s0, s1)
    ensures  evalCode_lax(lvm_Block(b1), s1, sN)
    // ensures StateNext(s0,s1)
{
    c1 := b0.hd;
    b1 := b0.tl;
    if (s0.ok)
    {
        assert evalBlock(b0, s0, sN);
        var r':state :| evalCode(b0.hd, s0, r') && evalBlock(b0.tl, r', sN);
        s1 := r';
        if ValidState(s0) {
            code_state_validity(c1, s0, s1);
        }
        assert evalCode_lax(c1, s0, s1);
        // s1 :| evalCode(b0.hd, s0, s1,o) && (if s1.ok then evalBlock(b0.tl, s1, sN,o) else s1 == sN);
    }
    else
    {
        s1 := s0;
    }
}

lemma lvm_lemma_block(b:codes, s0:lvm_state, r:lvm_state) 
                returns(r1:lvm_state, c0:code, b1:codes)
    requires b.lvm_Codes?
    requires eval_code(Block(b), s0, r)
    ensures  b == lvm_Codes(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  eval_code(c0, s0, r1)
    ensures  eval_code(Block(b1), r1, r)
    ensures s0.ok ==> evalCode(b.hd, s0, r1) && evalBlock(b.tl, r1, r);
    // ensures s0.ok && b.hd.Block? ==> r1 == s0;
{
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r);
        var r':state :| evalCode(b.hd, s0, r') && evalBlock(b.tl, r', r) ;
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1);
        }
        // if(b.hd.Block?){
        //     assert r1 == s0;
        // }
        assert eval_code(c0, s0, r1);
    } else {
        r1 := s0;
    }
}

predicate lvm_require(block0:lvm_codes, c:lvm_code, s0:lvm_state, sN:lvm_state)
{
    block0.lvm_Codes?
 && block0.hd == c
 && evalCode_lax(lvm_Block(block0), s0, sN)
 && ValidState(s0)
}

predicate lvm_ensure(b0:lvm_codes, b1:lvm_codes, s0:lvm_state, s1:lvm_state, sN:lvm_state)
{
    b0.lvm_Codes?
 && b0.tl == b1
 && (s1.ok ==> evalCode_lax(b0.hd, s0, s1))
 && evalCode_lax(lvm_Block(b1), s1, sN)
 && ValidState(s1)
}

// -----------
// -----------
type lvm_code = code
type lvm_codes = codes
type lvm_state = state
type lvm_operand_opr = operand
type lvm_data = Data
type lvm_cond = condition

function lvm_data_operand(d:Data):operand {D(d)}
function lvm_get_ok(s:lvm_state):bool { ValidState(s) }
predicate lvm_is_src_opr(o:operand, s:lvm_state) { true }
predicate lvm_is_dst_opr(o:operand, s:lvm_state) { true }
function method lvm_get_block(c:code):codes requires c.Block? { c.block }
function lvm_get_ifTrue(c:code):codes requires c.IfElse? { c.ifTrue }
function lvm_get_ifFalse(c:code):codes requires c.IfElse? { c.ifFalse }

predicate lvm_state_eq(s0:lvm_state, s1:lvm_state)
{
    s0.ok == s1.ok
 && s0.lvs == s1.lvs
 && s0.gvs == s1.gvs
 && s0.m == s1.m
}

}   