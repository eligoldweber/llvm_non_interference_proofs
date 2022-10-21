include "simpleTestPatchBenign.i.dfy"
include "simpleTestBenign.i.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"

module benignTestProperties{
    import opened simpleTestPatchBenign
    import opened simpleTestBenign
    import opened LLVM_def_NEW
    import opened types
    import opened Collections__Seqs_s


    lemma unwrapPatch(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validConfigPatch(s);
        ensures b == [s] + evalCodeFn(entryPatch(),s);
        ensures last(b).o.o.val == 0;
    {
        var config := allVariablesConfigPatch();
        b := [s] + evalCodeFn(entryPatch(),s);
        assert |b| == 2;
        assert last(b).o.o.val == 0;
    }

    lemma unwrapVuln(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validConfigVuln(s);
        ensures b == [s] + evalCodeFn(entryVuln(),s);
        ensures last([s] + evalCodeFn(entryVuln(),s)).o.Out?;
        ensures last([s] + evalCodeFn(entryVuln(),s)).o.o.Int?;
        // ensures unwrapVuln(s) == last([s] + evalCodeFn(entryVuln(),s))
    {
        var config := allVariablesConfigVuln();
        b := [s] + evalCodeFn(entryVuln(),s);
        assert NextStep(b[0],b[1],evalInsStep((ICMP(config.ops["var_cmp"],sle,1,config.ops["var_x"],D(Int(0,IntType(1,false)))))));
       
        if dataToBool(OperandContents(b[1],config.ops["var_cmp"])){
                        // assert ValidInstruction(b[1],(STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"])));

            assert NextStep(b[1],b[2],evalInsStep((STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]))));
            // assert NextStep(b[2],b[3],evalInsStep((LOAD(config.ops["var_3"],1,config.ops["var_retval"]))));
            // assert NextStep(b[3],b[4],evalInsStep((RET(config.ops["var_3"]))));

        }else{
            assert NextStep(b[1],b[2],evalInsStep((ICMP(config.ops["var_cmp1"],sgt,1,config.ops["var_x"],D(Int(2,IntType(1,false)))))));
             if dataToBool(OperandContents(b[2],config.ops["var_cmp1"])){
                    assert NextStep(b[2],b[3],evalInsStep((STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]))));
             }else{
                    assert NextStep(b[2],b[3],evalInsStep((STORE(config.ops["var_x"],config.ops["var_retval"]))));

             }
        }
        assert last(b).o.Out?;
        assert last(b).o.o.Int?;
        assert last(b).o.o.val == 0 ||  last(b).o.o.val == 1 || last(b).o.o.val == 2;
    }

    lemma allVulnHaveIntOutput(s:State)
        requires ValidState(s) 
        requires validConfigVuln(s) 
        // ensures last([s] + evalCodeFn(entryVuln(),s)).o.Out?;
        // ensures last([s] + evalCodeFn(entryVuln(),s)).o.o.Int?;
    {
        var b_vuln := unwrapVuln(s);
        // assert last([s] + evalCodeFn(entryVuln(),s)).o.Out?;
        // assert forall s :: ValidState(s) && validConfigVuln(s) ==> last([s] + evalCodeFn(entryVuln(),s)).o.Out?;
    }

    lemma valsTest()
        requires forall s :: (ValidState(s)  
                            && validConfigVuln(s) 
                            && (OperandContents(s,allVariablesConfigVuln().ops["var_x"]).val > 2
                                || OperandContents(s,allVariablesConfigVuln().ops["var_x"]).val < 0))
                            ==> (last([s] + evalCodeFn(entryVuln(),s)).o.Out?
                                && last([s] + evalCodeFn(entryVuln(),s)).o.o.Int?
                                && last([s] + evalCodeFn(entryPatch(),s)).o.Out?
                                && last([s] + evalCodeFn(entryPatch(),s)).o.o.Int?
                                && last([s] + evalCodeFn(entryVuln(),s)).o.o.val == last([s] + evalCodeFn(entryPatch(),s)).o.o.val)
    {
        reveal_ValidSimpleBehavior();
        reveal_evalCodeFn();
        forall s | ValidState(s) 
                   && validConfigVuln(s)
                   && OperandContents(s,allVariablesConfigVuln().ops["var_x"]).val <= 2
                   && OperandContents(s,allVariablesConfigVuln().ops["var_x"]).val >= 0
        {
            var b_vuln := unwrapVuln(s);
            var b_patch := unwrapPatch(s);

            
            assert exists s' :: last([s'] + evalCodeFn(entryVuln(),s')).o.o.val == 0;
            // assert last(b_vuln).o.o.val == last(b_patch).o.o.val;
            // assert last(b).o.o.val == 0 ||  last(b).o.o.val == 2 || last(b).o.o.val == 1;
        }

        // assert exists p,b :: ValidState(p) && validConfigVuln(p) && b == [p] + evalCodeFn(entryVuln(),p);
    }

}