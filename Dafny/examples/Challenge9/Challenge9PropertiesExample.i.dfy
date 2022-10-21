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

    lemma  vulnAlwaysReturns1()
        ensures forall s:State,bVuln :: && ValidState(s) 
                                && validConfig(s) 
                                && bVuln == [s] + evalCodeFn(entrySimplVuln(),s) ==> OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 
    {
        forall s:State,bVuln | && ValidState(s) 
                         && validConfig(s) 
                                && bVuln == [s] + evalCodeFn(entrySimplVuln(),s)
            ensures OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 
        {
            var b :=  unwrapVuln(s);
            assert  bVuln == b;
            assert OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 
        }
    }

    // predicate testVal(b:Behavior)
    // {
    //     OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1
    // }

    // predicate badbehavior(s:State,b:Behavior)
    // {
    //      OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 ==> miniSpec(s,b)
    // }

    // lemma testValImpliesItself(s:State,b:Behavior)
    // requires ValidState(s) 
    //     requires validConfig(s) 
    //     requires b == [s] + evalCodeFn(entrySimplVuln(),s)
    //     ensures testVal(b) ==> OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1;
    // {
        
    // }

    lemma  vulnIs(s:State, b:Behavior)
        requires ValidState(s) 
        requires validConfig(s) 
        requires b == [s] + evalCodeFn(entrySimplVuln(),s)
               requires ValidOperand(last(b),allVariablesConfig().ops["var_28"])
       requires OperandContents(last(b),allVariablesConfig().ops["var_28"]).Int?
       requires ValidOperand(last(b),allVariablesConfig().ops["var_0"])
       requires OperandContents(last(b),allVariablesConfig().ops["var_0"]).Int?
        // ensures testVal(b)
        // ensures badbehavior(s,b)
        // ensures OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 ==> miniSpec(s,b);
    {
        // vulnAlwaysReturns1();
        var bVuln := unwrapVuln(s);
        assert b == bVuln;
        assert OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1;  
        assert OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 ==> miniSpec(s,b);
    }


    predicate latest(s:State,a:Behavior,b:Behavior)
        requires ValidState(s) 
        requires validConfig(s) 
    {
        (a == [s] + evalCodeFn(entrySimplVuln(),s)  
        && !miniSpec(s,a) 
        && b == [s] + evalCodeFn(entrySimple(),s)) ==>
        OperandContents(last(b),allVariablesConfig().ops["var_28"]).val ==OperandContents(last(b),allVariablesConfig().ops["var_28"]).val
}
    lemma isPatchIsComplete(s:State)
        requires ValidState(s) 
        requires validConfig(s) 
        ensures forall bVuln,pPAtch :: && bVuln == [s] + evalCodeFn(entrySimplVuln(),s)  
                                       && !miniSpec(s,bVuln) 
                                       && pPAtch == [s] + evalCodeFn(entrySimple(),s) ==>
                                       OperandContents(last(pPAtch),allVariablesConfig().ops["var_28"]).val == OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val
    {
        forall bVuln |&& bVuln == [s] + evalCodeFn(entrySimplVuln(),s) 
            ensures !miniSpec(s,bVuln) ==> (OperandContents(last(bVuln),allVariablesConfig().ops["var_0"]).val < 255);
            ensures OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 
        {
            // var b' := unwrapPatch(s);
            // var b := unwrapVuln(s);
            // vulnAlwaysReturns1();
            var b :=  unwrapVuln(s);
            assert  bVuln == b;
            // assert OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 
            // assert !miniSpec(s,b) ==> (OperandContents(last(b),allVariablesConfig().ops["var_0"]).val < 255);
           
        }
        forall bVuln,pPAtch |&& bVuln == [s] + evalCodeFn(entrySimplVuln(),s)  && !miniSpec(s,bVuln) 
        && pPAtch == [s] + evalCodeFn(entrySimple(),s) 
            ensures OperandContents(last(pPAtch),allVariablesConfig().ops["var_28"]).val ==OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val;
        {
            var b' := unwrapPatch(s);
            assert pPAtch == b';
            // assert OperandContents(last(b'),allVariablesConfig().ops["var_28"]).val == 1; 
            // assert OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val == 1; 

            // assert 
 
        }
         assert forall bVuln,pPAtch :: && bVuln == [s] + evalCodeFn(entrySimplVuln(),s)  
                                       && !miniSpec(s,bVuln) 
                                       && pPAtch == [s] + evalCodeFn(entrySimple(),s) ==>
                                       OperandContents(last(pPAtch),allVariablesConfig().ops["var_28"]).val ==OperandContents(last(bVuln),allVariablesConfig().ops["var_28"]).val;
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


    lemma unwrapVuln(s:State) returns (b:Behavior)
        requires ValidState(s);
        requires validConfig(s);
        ensures b == [s] + evalCodeFn(entrySimplVuln(),s);
        // ensures testVal(b)
        // ensures !miniSpec(s,b);
        ensures OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1;
        ensures miniSpec(s,b) ==> (OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 && OperandContents(last(b),allVariablesConfig().ops["var_0"]).val < 0x8000_0000);
        ensures !miniSpec(s,b) ==> OperandContents(last(b),allVariablesConfig().ops["var_0"]).val < 255;
        {
        var config := allVariablesConfig();
        b := [s] + evalCodeFn(entrySimplVuln(),s);
        // assert |b| == 7;
        assert NextStep(b[0],b[1],evalInsStep((LOAD(config.ops["var_0"],1,config.ops["var_num_connections"]))));
        assert NextStep(b[1],b[2],evalInsStep((ZEXT(config.ops["var_conv"],1,config.ops["var_0"],4))));
       
        assert NextStep(b[2],b[3],evalInsStep((STORE(D(Int(1,IntType(1,false))),config.ops["var_retval"]))));

        
        assert NextStep(b[3],b[4],evalInsStep((LOAD(config.ops["var_28"],1,config.ops["var_retval"]))));
        assert NextStep(b[4],b[5],evalInsStep((RET(config.ops["var_28"]))));
        assert OperandContents(last(b),allVariablesConfig().ops["var_28"]).val == 1;
                        assert miniSpec(s,b) ==> (OperandContents(last(b),allVariablesConfig().ops["var_0"]).val >= 255 && OperandContents(last(b),allVariablesConfig().ops["var_0"]).val < 0x8000_0000);
                        assert !miniSpec(s,b) ==> OperandContents(last(b),allVariablesConfig().ops["var_0"]).val < 255;

            // assert (OperandContents(last(b),config.ops["var_0"]).val >= 255 && OperandContents(last(b),config.ops["var_0"]).val < 0x8000_0000) ==> OperandContents(last(b),config.ops["var_28"]).val == 0;
            // assert OperandContents(last(b),config.ops["var_0"]).val < 255 ==> OperandContents(last(b),config.ops["var_28"]).val == 1;
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