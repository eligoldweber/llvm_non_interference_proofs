# llvm to dafny parser

This is a [WIP] tool to help translate llvm assembly (.ll) into the corresponding llvm semantics in Dafny. 
This does not yet work for all examples, but can be used as a starting point.

---

Use the following command to run this script: `python convertToDafny.py -i [input_file] -o [output_file]`

ex: `python convertToDafny.py -i ./examples/test.ll -o testOut.txt`

---

The output of this script is the body of a function in Dafny. 

---

NOTE: All `.ll` files must end in a newline

NOTE: The formal semantics of LLVM in Dafny dont yet support `switch` or `phi`, so it is recommended to use the `-lowerswitch` and `reg2mem` LLVM passes.

