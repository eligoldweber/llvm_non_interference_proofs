include "Challenge9CodeExample.i.dfy"
include "../../LLVM/llvmNEW.i.dfy"
include "../../LLVM/types.s.dfy"
include "../../Libraries/Seqs.s.dfy"

module challenge9PropertiesExample{
    import opened challenge9CodeExample
    import opened LLVM_def_NEW
    import opened types
    import opened Collections__Seqs_s


lemma isPatchIsSuccesful()
    ensures forall s,b :: && ValidState(s) 
                          && validConfig(s) 
                          && b == [s] + evalCodeFn(entrySimple(),s) ==> !miniSpec(s,b)
{
    forall s:State,b | && ValidState(s) && validConfig(s) && b == [s] + evalCodeFn(entrySimple(),s)
        ensures !miniSpec(s,b);
     {
        var b := unwrapPatch(s);
        assert !miniSpec(s,b);
     }
}


    lemma unwrapPatch(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validConfig(s);
        ensures b == [s] + evalCodeFn(entrySimple(),s);
        ensures !miniSpec(s,b);
    {
        var config := allVariablesConfig();
        b := [s] + evalCodeFn(entrySimple(),s);
        assert |b| == 7;
        assert NextStep(b[0],b[1],evalInsStep((LOAD(config.ops["var_0"],1,config.ops["var_num_connections"]))));
        assert NextStep(b[1],b[2],evalInsStep((ZEXT(config.ops["var_conv"],1,config.ops["var_0"],4))));
        assert NextStep(b[2],b[3],evalInsStep((ICMP(config.ops["var_cmp"],sge,4,config.ops["var_conv"],D(Int(255,IntType(4,false)))))));
        // assert OperandContents(b[3],config.ops["var_cmp"]) == evalICMP(sge,4,OperandContents(b[2],config.ops["var_conv"]),(Int(255,IntType(4,false))));
        // assert OperandContents(b[3],config.ops["var_conv"]).val < 255 ==> OperandContents(b[3],config.ops["var_cmp"]).val == 0;
        // assert (OperandContents(b[3],config.ops["var_conv"]).val >= 255  && OperandContents(b[3],config.ops["var_conv"]).val < 0x8000_0000) ==> OperandContents(b[3],config.ops["var_cmp"]).val == 1;
        if dataToBool(OperandContents(b[3],config.ops["var_cmp"])){
            assert NextStep(b[3],b[4],evalInsStep((STORE(D(Int(0,IntType(1,false))),config.ops["var_retval"]))));
        }else{
            assert NextStep(b[3],b[4],evalInsStep((STORE(D(Int(1,IntType(1,false))),config.ops["var_retval"]))));

        }
            assert NextStep(b[4],b[5],evalInsStep((LOAD(config.ops["var_28"],1,config.ops["var_retval"]))));
            assert NextStep(b[5],b[6],evalInsStep((RET(config.ops["var_28"]))));
            
            assert (OperandContents(last(b),config.ops["var_0"]).val >= 255 && OperandContents(last(b),config.ops["var_0"]).val < 0x8000_0000) ==> OperandContents(last(b),config.ops["var_28"]).val == 0;
            assert OperandContents(last(b),config.ops["var_0"]).val < 255 ==> OperandContents(last(b),config.ops["var_28"]).val == 1;
    }

    predicate miniSpec(s:State,b:Behavior)
    {
        reveal_ValidBehavior();
        var config := allVariablesConfig();
       && ValidState(s)
       && validConfig(s)
       && ValidBehavior(b)
       && |b| > 0
       && ValidOperand(last(b),allVariablesConfig().ops["var_28"])
       && OperandContents(last(b),allVariablesConfig().ops["var_28"]).Int?
       && ValidOperand(last(b),allVariablesConfig().ops["var_0"])
       && OperandContents(last(b),allVariablesConfig().ops["var_0"]).Int?
       //
       && OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1
       && (OperandContents(last(b),config.ops["var_0"]).val >= 255 && OperandContents(last(b),config.ops["var_0"]).val < 0x8000_0000)
    }


}