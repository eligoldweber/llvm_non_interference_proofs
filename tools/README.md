# llvm to dafny parser

This is a [WIP] tool to help translate llvm assembly (.ll) into the corresponding llvm semantics in Dafny. 
This does not yet work for all examples, but can be used as a starting point.

---

Use the following command to run this script: `python convertToDafny.py -i [input_file] -o [output_file] -m [module_name]`

ex: `python convertToDafny.py -i ./examples/test.ll -o testOut.dfy -m testModule`

---

The output of this script is a collection of functions which make up body a simple `.dfy` file which is a start for the formal encoding of LLVM in dafny. 

The functions are generated wrapped in a dafny module with the appropriate imports. There is one piece still missing. It is necessary to still include the file paths for `llvmNEW.i.dy` and `types.s.dfy` at the top of the output file. This is the relative path for example:

`include "../../LLVM/llvmNEW.i.dfy"`

`include "../../LLVM/types.s.dfy"`

---

NOTE: All `.ll` files must end in a newline

NOTE: The formal semantics of LLVM in Dafny dont yet support `switch` or `phi`, so it is recommended to use the `-lowerswitch` and `reg2mem` LLVM passes.

