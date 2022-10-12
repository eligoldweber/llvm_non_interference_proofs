For this challenge problem, the following patch was added at the source code level. 

```
static uint8_t create_conn(uint16_t size){
  **if(num_connections >= 255){
    return 0;
  }**
  // Initialize new connection                                                                                                                                       
    if (connection_infos[src] == NULL){
        connection_infos[src] = (struct ConnectionInfo *)calloc(1, sizeof(struct ConnectionInfo));
        connection_infos[src]->state = IDLE;
        connection_infos[src]->data = NULL;
    }
    ...
```

To genereate the included `.ll` file the following commands were run starting from the source code:

* `clang  -O0 -emit-llvm transport.c -c -Xclang -disable-O0-optnone`

* `llvm-dis transport.bc`

* `opt -reg2mem -S transport.ll`

---

There is a very simplified version of the `.ll` patch in `tools/examples/challenge9.ll` that can be used with the `convertToDafny.py` script to get started.

the following was added to the predicate `validConfig` in the generated `.dfy` file 

```
 && s.lvs["var_28"].Int?
&& s.lvs["var_0"].Int?
&& s.lvs["var_num_connections"].Ptr?
&& s.lvs["var_retval"].Ptr?
&& s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].mb? 
&& s.m.mem[OperandContents(s,c.ops["var_retval"]).bid][OperandContents(s,c.ops["var_retval"]).offset].size == 1
&& s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].mb? 
&& s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].size == 1
&& s.m.mem[OperandContents(s,c.ops["var_num_connections"]).bid][OperandContents(s,c.ops["var_num_connections"]).offset].data >= 0

```