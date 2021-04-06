include "llvm.i.dfy"

module test {
    import opened LLVM_def

predicate{:opaque} evalCodeOpaque(c:code, s0:state, sN:state,o:operand) 
    { evalCode(c, s0, sN,o) }

predicate evalCode_lax(c:code, s0:state, sN:state,o:operand) 
    { s0.ok ==> evalCodeOpaque(c, s0, sN,o) }

function method lvm_CNil():codes { CNil }
function method lvm_Block(block:codes):code { Block(block) }

function method void_Operand():operand {var o := Void; D(o)}


function lvm_update_ok(sM:lvm_state, sK:lvm_state):state { sK.(ok := sM.ok) }
function lvm_update_local(l:LocalVar, sM:lvm_state, sK:lvm_state):lvm_state
    requires l in sM.lvs
{ sK.(lvs := sK.lvs[l := sM.lvs[l]]) }
function lvm_update_mem(sM:lvm_state, sK:lvm_state):lvm_state {
    sK.(m := sK.m.(mem := sM.m.mem))
}

predicate {:opaque} eval_code(c:code, s:state, r:state, o:operand)
{
    s.ok ==> evalCode(c, s, r, o)
}


lemma lvm_lemma_empty(s0:state, sN:state) returns(sM:state)
    // requires evalCode_lax(lvm_Block(lvm_CNil()), s0, sN, void_Operand())
        requires exists o:operand :: evalCode_lax(lvm_Block(lvm_CNil()), s0, sN, o)

    ensures  s0 == sM
    ensures  s0.ok ==> s0 == sN
{
    reveal_evalCodeOpaque();
    sM := s0;
}

lemma lemma_FailurePreservedByBlock(block:codes, s:state, r:state, o:operand)
    requires evalBlock(block, s, r, o);
    ensures  !s.ok ==> !r.ok;
    decreases block;
{
    if !block.CNil? {
        var r' :| evalCode(block.hd, s, r', o) && evalBlock(block.tl, r', r, o);
        lemma_FailurePreservedByCode(block.hd, s, r', o);
        lemma_FailurePreservedByBlock(block.tl, r', r, o);
    }
}

lemma lemma_FailurePreservedByCode(c:code, s:state, r:state, o:operand)
    requires evalCode(c, s, r, o);
    ensures  !s.ok ==> !r.ok;
{
    if c.Block? {
        lemma_FailurePreservedByBlock(c.block, s, r, o);
    }
}

lemma block_state_validity(block:codes, s:state, r:state, o:operand)
    requires evalBlock(block, s, r, o);
    requires ValidState(s);
    decreases block, 0;
    ensures  r.ok ==> ValidState(r);
{
    if block.lvm_CCons? {
        var r':state :| evalCode(block.hd, s, r', o) && evalBlock(block.tl, r', r, o);
        code_state_validity(block.hd, s, r', o);
        if r'.ok {
            block_state_validity(block.tl, r', r, o);
        }
        else {
            lemma_FailurePreservedByBlock(block.tl, r', r, o);
        }
    }
}
lemma code_state_validity(c:code, s:state, r:state, o:operand)
    requires evalCode(c, s, r, o);
    requires ValidState(s);
    decreases c, 0;
    ensures  r.ok ==> ValidState(r);
{
    if r.ok {
        if c.Ins? {
            assert !s.ok ==> !r.ok;
            assert evalIns(c.ins,s,r,o);
            assert s.ok;
            assert ValidInstruction(s,c.ins);
            assert r.ok;
            assert evalIns(c.ins,s,r,o);
            assert c.ins.RET? ==> ValidState(r);

            // assert MemValid(r.m);
            assert ValidState(r);
        } else if c.Block? {
            block_state_validity(c.block, s, r, o);
        } else if c.IfElse? {
                var s' :| branchRelation(s, s', c.ifCond) &&
                    if c.ifCond then
                        evalCode(c.ifTrue, s', r, o)
                    else
                        evalCode(c.ifFalse, s', r, o);
                if c.ifCond {
                    code_state_validity(c.ifTrue, s', r, o);
                } else {
                    code_state_validity(c.ifFalse, s', r, o);
                }
            assert ValidState(r);
        } 
        // else if c.While? {
        //     var n:nat :| evalWhile(c.whileCond, c.whileBody, n, s, r);
        //     evalWhile_validity(c.whileCond, c.whileBody, n, s, r);
        //     assert valid_state(r);
        // }
    }
}

lemma lvm_lemma_block_lax(b0:lvm_codes, s0:state, sN:state,o:operand) returns(s1:state, c1:lvm_code, b1:lvm_codes)
    requires b0.lvm_CCons?
    requires evalCode_lax(lvm_Block(b0), s0, sN,o)
    ensures  b0 == lvm_CCons(c1, b1)
    ensures  evalCode_lax(c1, s0, s1,o)
    ensures  evalCode_lax(lvm_Block(b1), s1, sN,o)
{
    reveal_evalCodeOpaque();
    c1 := b0.hd;
    b1 := b0.tl;
    if (s0.ok)
    {
        assert evalBlock(b0, s0, sN,o);
        var r':state :| evalCode(b0.hd, s0, r',o) && evalBlock(b0.tl, r', sN,o);
        s1 := r';
        if ValidState(s0) {
            code_state_validity(c1, s0, s1,o);
        }
        assert evalCode_lax(c1, s0, s1,o);
        // s1 :| evalCode(b0.hd, s0, s1,o) && (if s1.ok then evalBlock(b0.tl, s1, sN,o) else s1 == sN);
    }
    else
    {
        s1 := s0;
    }
}

lemma lvm_lemma_block(b:codes, s0:lvm_state, r:lvm_state,o:operand) returns(r1:lvm_state, c0:code, b1:codes)
    requires b.lvm_CCons?
    requires eval_code(Block(b), s0, r,o)
    ensures  b == lvm_CCons(c0, b1)
    ensures  ValidState(s0) && r1.ok ==> ValidState(r1);
    ensures  eval_code(c0, s0, r1,o)
    ensures  eval_code(Block(b1), r1, r,o)
{
    reveal_eval_code();
    c0 := b.hd;
    b1 := b.tl;
    if s0.ok {
        assert evalBlock(b, s0, r,o);
        var r':state :| evalCode(b.hd, s0, r',o) && evalBlock(b.tl, r', r,o);
        r1 := r';
        if ValidState(s0) {
            code_state_validity(c0, s0, r1,o);
        }
        assert eval_code(c0, s0, r1,o);
    } else {
        r1 := s0;
    }
}

predicate lvm_require(block0:lvm_codes, c:lvm_code, s0:lvm_state, sN:lvm_state,o:operand)
{
    block0.lvm_CCons?
 && block0.hd == c
 && evalCode_lax(lvm_Block(block0), s0, sN,o)
 && ValidState(s0)
}

predicate lvm_ensure(b0:lvm_codes, b1:lvm_codes, s0:lvm_state, s1:lvm_state, sN:lvm_state,o:operand)
{
    b0.lvm_CCons?
 && b0.tl == b1
 && (s1.ok ==> evalCode_lax(b0.hd, s0, s1,o))
 && evalCode_lax(lvm_Block(b1), s1, sN,o)
 && ValidState(s1)
}

// -----------
// -----------
type lvm_code = code
type lvm_codes = codes
type lvm_state = state
type lvm_operand_opr = operand

function lvm_get_ok(s:lvm_state):bool { s.ok }
predicate lvm_is_src_opr(o:operand, s:lvm_state) { true }
predicate lvm_is_dst_opr(o:operand, s:lvm_state) { true }
function method lvm_get_block(c:code):codes requires c.Block? { c.block }

predicate lvm_state_eq(s0:lvm_state, s1:lvm_state)
{
    s0.ok == s1.ok
 && s0.lvs == s1.lvs
 && s0.gvs == s1.gvs
 && s0.m == s1.m
}

function method{:opaque} lvm_code_Empty_Test():lvm_code
{   
    lvm_Block(lvm_CNil())
}       

lemma lvm_lemma_Empty_Test(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, src:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Empty_Test(), lvm_s0, lvm_sN,o)
  requires lvm_is_src_opr(src, lvm_s0)
  requires lvm_get_ok(lvm_s0)
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,o)
  ensures  lvm_get_ok(lvm_sM)
  ensures  lvm_state_eq(lvm_sM, lvm_s0)
ensures lvm_state_eq(lvm_sM, lvm_update_mem( lvm_sM, lvm_update_ok(lvm_sM, lvm_sM)))
{
  reveal_lvm_code_Empty_Test();
  reveal_eval_code();
  var lvm_old_s:lvm_state := lvm_s0;

  assert lvm_s0.ok;
  assert lvm_code_Empty_Test() == Block(CNil);
  assert lvm_b0.hd == lvm_code_Empty_Test();
  assert !lvm_b0.CNil?;
  assert lvm_code_Empty_Test().block.CNil?;
  assert lvm_b0.hd.Block?;
  assert lvm_get_block(lvm_b0.hd).CNil?;
  assert evalBlock(lvm_get_block(lvm_b0.hd),lvm_s0, lvm_s0,o);
  assert forall r :: r == lvm_s0 ==> eval_code(lvm_b0.hd,lvm_s0,r,o);
  assert evalCode_lax(Block(lvm_b0), lvm_s0, lvm_sN, o);
//   assert exists r' :: evalBlock(lvm_b0.tl, lvm_s0, r',o);
// assert Block(CNil).CNil?;
assert evalBlock(lvm_b0, lvm_s0, lvm_sN,o) ==> exists r' :: evalCode(lvm_b0.hd, lvm_s0, r',o) && evalBlock(lvm_b0.tl, r', lvm_sN,o);
assert exists r' :: if evalCode(lvm_b0.hd, lvm_s0, r',o) then true else true;
// assert eval_code(Block(lvm_b0), lvm_s0, lvm_s0,o);
//   assert evalBlock(lvm_b0, lvm_s0, lvm_sN,o);
  
//   assert eval_code(Block(lvm_b0), lvm_s0, lvm_sN,o);
  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block_lax(lvm_b0, lvm_s0, lvm_sN,o);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  var lvm_b1:lvm_codes := lvm_get_block(lvm_cM);
  assert evalCode_lax(lvm_Block(lvm_CNil()), lvm_s0, lvm_sM, o);

  lvm_sM := lvm_lemma_empty(lvm_s0, lvm_sM);
}

function method{:opaque} lvm_code_Add(dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr):lvm_code
{
    reveal_IntFits();
    var val := D(Int(4,IntType(1,false)));
    assert val.d.Int?;
    var void := D(Void);
    lvm_Block(lvm_CCons(Ins(ADD(dst, size,src1,val)),lvm_CCons(Ins(RET(void)),lvm_CNil())))

}

lemma lvm_lemma_Add(lvm_b0:lvm_codes, lvm_s0:lvm_state, lvm_sN:lvm_state, 
            dst:lvm_operand_opr, size:nat, src1:lvm_operand_opr,src2:lvm_operand_opr,o:operand)
  returns (lvm_bM:lvm_codes, lvm_sM:lvm_state)
  requires lvm_require(lvm_b0, lvm_code_Add(dst, size,src1), lvm_s0, lvm_sN,dst)
  requires lvm_is_dst_opr(dst, lvm_s0)
  requires lvm_is_src_opr(src1, lvm_s0)
  requires lvm_get_ok(lvm_s0)

  requires ValidOperand(lvm_s0,src1);
  requires OperandContents(lvm_s0,src1).Int?;
  requires lvm_code_Add(dst, size,src1).Ins?;

//   requires dst.GV?;
  requires ValidOperand(lvm_s0,dst)
//   
  ensures  lvm_ensure(lvm_b0, lvm_bM, lvm_s0, lvm_sM, lvm_sN,dst)
  ensures  lvm_get_ok(lvm_sM)
  ensures ValidOperand(lvm_sM,dst)

  ensures OperandContents(lvm_sM,dst).Int?;
  ensures OperandContents(lvm_s0,dst).Int?;

  ensures  OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4
  ensures  lvm_state_eq(lvm_sM, lvm_update_ok(lvm_sM, lvm_update_mem( lvm_sM, lvm_s0)))
{
    // assert dst.g in lvm_s0.gvs;
  reveal_lvm_code_Add();
  assert lvm_code_Add(dst, size,src1).Ins?;
  var addIns := lvm_code_Add(dst, size,src1).ins;
  assert ValidInstruction(lvm_s0,addIns);
//   assert o == dst;
  assert  ValidRegOperand(lvm_s0, dst);
  assert ValidState(lvm_s0);
  assert lvm_b0.hd.Ins?;
  var lvm_old_s:lvm_state := lvm_s0;
//   lvm_ins_lemma(Ins(InsAdd(dst, src)), lvm_s0);
  ghost var lvm_ltmp1, lvm_cM:lvm_code, lvm_ltmp2 := lvm_lemma_block_lax(lvm_b0, lvm_s0, lvm_sN,dst);
  lvm_sM := lvm_ltmp1;
  lvm_bM := lvm_ltmp2;
  assert lvm_b0.tl == lvm_bM;
  assert lvm_bM.CNil?;
//   assert  OperandContents(lvm_sM, dst).Int?;

  assert evalCode_lax(lvm_cM, lvm_s0, lvm_sM,dst);
  assert OperandContents(lvm_sM, dst).val == OperandContents(lvm_s0, dst).val + 4;
//   assert ValidInstruction(lvm_s0,lvm_code_Add(dst, size,src1,src2).ins) ==> lvm_sM.ok;
//   assert evalUpdate(lvm_s0, o, evalADD(size,OperandContents(lvm_s0,src1),val), lvm_sM);

  reveal_evalCodeOpaque();
}
//   requires ValidInstruction(lvm_s0,lvm_code_Add(dst, size,src1).ins);
//   requires o == dst;
//   assert  OperandContents(lvm_s0,src1).Int?;
//   assert evalADD(size,OperandContents(lvm_s0,src1),OperandContents(lvm_s0,src2)).Int?;
// reveal_IntFits();
//     var val := Int(4,IntType(1,false));
//     assert val.Int?;
    //   assert dst.LV?;
    //   assert (lvm_sN == lvm_s0.(lvs := lvm_s0.lvs[o.l := evalADD(size,OperandContents(lvm_s0,src1),val)])) ==> evalUpdate(lvm_s0, dst, evalADD(size,OperandContents(lvm_s0,src1),val), lvm_sN); 
//   assert lvm_s0 == lvm_sN;
//   assert  evalIns(addIns, lvm_s0, lvm_sN,o);
}   