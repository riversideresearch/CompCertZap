
Location set is just the current contents of all machine locations (registers, stack slots, etc) or more simply its like regset in RTL. A mapping from every machine storage location (registers, stack slots, etc.) to the value currently stored there.

- so why not call it a register set? Because `args` don't always live in registers, sometimes they're passed n the stack.
so why is it returned as a function?

Machine state is represented as function... This makes proofs much easier.

```
Definition return_regs (caller calle: locset) : locset :=
	fun (l: loc) =>
		match l with
			(* if callee saved register, then take the caller's old value *)
			(* if caller saved register, then take the callee old value *)
		| R r => if is_callee_save r then caller (R r) else callee (R r)
		(* Any outgoing stack slot is init to undef *)
		| S Outgoing ofs ty => Vundef
		(* Any local and incoming stack slot of the caller remains the same *)
		| S sl ofs ty => caller (S sl ofs ty)
	end.
```
- `(loc -> val) -> (loc -> val) -> (loc -> val)` `return_regs` takes the caller's location set (before the call) and the callee's location set (at the return point), and constructs a new location set representing the caller's machine state after the call. Given a location `loc`, it returns the value the `loc` should contain after returning from the callee, according to the calling convention.
- Caller-saved vs callee-saved? Caller saved are temp registers that the called can overwrite, if the callee needs it then it must save beforehand. Calle saved are registers that the callee is allowed to overwrite but before returning must restore to it original value.
- Understanding the above is sufficient to understanding `call_regs`, and `undef_caller_save_reg`.

The state definition is still similar to RTL but differs with the addition of a new state called Block, and `locset` replaces `args` and `rs:regset`.
```
| Block:
	forall (stack: list stackframe) (**r call stack *)
			(f: function) (** r function currently executing *) 
			(sp: val) (** r stack pointer *)
			(bb: bblock) (** r current basic block *)
			(ls: locset) (**r location state *)
			(m: mem) (**r memory state *)
```
> LTL is close to RTL, but it uses machine registers and stack slots instead of pseudo-registers. Also the nodes of the CFG graph are basic blocks instead of single instructions.

- so how can analysis be done on instruction at the LTL level? I'm guessing the nodes will contain the instructions. YH i'm right!
		- `Definition bblock := list instruction`
	- So each basic block is just a list of instruction.
```
Inductive step: state -> trace -> state -> Prop :=
| exec_start_block: forall s f sp pc rs m bb,
	(fn_code f)!pc = Some bb ->
	step (State s f sp pc rs m)
	E0 (Block s f sp bb rs m)
```
- For all stack `s`, function `f`, stack pointer `sp`, program counter `pc`, location set `rs`, memory `m`, basic block `bb`: If the lookup of the current pc in the tree of blocks is a basic block, then the machine may step from st1 to a Block state ready to execute `bb`, with the same stack, function, stack pointer, location set and memory. The trace is E0.
```
| exec_Lop: forall s f sp op args res bb rs m v rs',
	eval_operation ge sp op (reglist rs args) m = Some v ->
	rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
	step (Block s f sp (Lop op args res :: b) rs m) E0
	(Block s f sp bb rs' m)
```
- For any stack `s`, function `f`, stack pointer `sp`, operation `op`, source registers `args`, result register `res`, basic block `bb`, location set `rs`, memory `m`, value `v`, new location set `rs`: If the evaluation of the operation `op` on the list of source registers `args` returns some value `v` and the new location set `rs'` is the previous location set with all the registers destroyed/clobbered by the operation marked as vundef and the result register set to `v`, then the machine may step from the block state which executes the first instruction from the front of the block to another block state with the new location set and a basic block `bb` with the first instruction removed.
```
| exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs',
	eval_addressing ge sp addr (reglist rs args) = Some a ->
	Mem.loadv chunk m a = Some v ->
	rs' = Locmap.set (R dst) v (undef_reg (destroyed_by_load chunk addr) rs) ->
	step (Block s f sp (Lload chunk addr args dst :: bb) rs m)
		E0 (Block s f sp bb rs' m)
```
- For all stack `s`, function `f`, stack pointer `sp`, memory chunk `chunk`, addressing mode `addr`, source registers `args`, destination reg `dst`, basic block `bb`, location set `rs`, memory `m`, address `a`, loaded value `v`, new location set `rs'`:
	- if evaluating the addressing mode `addr` using the value of registers `args` gives address `a` and the new location set `rs'` is the previous location set with all the registers destroyed by the load operation set to `vundef` and the result destination register set to `v`,  then the machine may step from a Block whose first instruction is `LLoad chunk addr args dst` to a block containing the rest of the instructions bb, with updated location set `rs'` and the same memory `m`.
```
| exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs',
	rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
	step (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs m) E0
		(Block s f sp bb rs' m)
```
- For any stack `s`, function `f`, stack pointer `sp`, stack slot `sl`, stack offset `ofs`, type `ty`,destination register `dst`, basic block `bb`, location set `rs`, memory `m`, new location set `rs`:
	- If `rs'` is obtained by fist marking the locations destroyed by this getstack operation as `vundef`, then setting register `dst` to the value currently stored at stack location `S sl ofs ty`, then the machine steps from a block whose first instruction is `Lgetstack sl ofs ty dst` to the rest of the block `bb`, with updated location se `rs'` and unchanged memory `m`.
```
| exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs',
  rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
  step (Block s f sp (Lsetstack src sl ofs ty :: bb) rs m)
	E0 (Block s f sp bb rs' m)
```
- For any stack `s`, function `f`, stack pointer `sp`, source register `src`, stack slot `sl`, stack offset `ofs`, type `ty`, basic block `bb`, location set `rs`, memory `m`, new location set `rs'`:
	- If `rs'` is obtained by first marking the locations destroyed by this set stack operation as `vundef`, then setting the stack offset to value currently stored at the source register `src`, then the machine steps from a block whose first instruction is `Lsetstack src sl ofs ty` to the rest of the block `bb`, with updated location set `rs'` and unchanged memory `m`.
```
| exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m',
  eval_addressing ge sp addr (reglist rs args) = Some a ->
  Mem.storev chunk m a (rs (R src)) = Some m' ->
  rs' = undef_regs (destroyed_by_store chunk addr) rs ->
  step (Block s f sp (Lstore chunk addr args src :: bb) rs m)
	E0 (Block s f sp bb rs' m')
```
- For any stack `s`, function `f`, stack pointer `sp`, memory chunk `chunk`, addressing mode `addr`, source register `src`, basic block `bb`, location set `rs`, memory `m`, address `a`, new location set `rs'`, new memory `m'`
	- If evaluating the addressing mode `addr` using the value of the registers `args` gives address `a`, and storing to memory chunk `chunk` at address `a` from source register `src` gives a modified memory state `m'`, then the machine may step from block whose first instruction is `Lstore chunk addre args src` to the rest of the block `bb`, with updated location set `rs'` and new memory `m'`.
```
| exec_Lcall: forall s f sp sig ros bb rs m fd,
  find_function ros rs = Some fd ->
  funsig fd = sig ->
  step (Block s f sp (Lcall sig ros :: bb) rs m)
	E0 (Callstate (Stackframe f sp rs bb :: s) fd rs m)
```
- For any stack `s`, function `f`, stack pointer `sp`, function signature `sig`, register or symbol call target `ros`, basic block `bb`, location set `rs`, memory `m`,function definition `fd`:
	- If `ros` resolved to a function definition `fd`, and `fd` has a signature `sig`, then the machine may step from block whose first instruction is `Lcall sig ros` to a callstate that will execute `fd` with the location set `rs` and memory `m`.
```
| exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m',
  rs' = return_regs (parent_locset s) rs ->
  find_function ros rs' = Some fd ->
  funsig fd = sig ->
  Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
  step (Block s f (Vptr sp Ptrofs.zero) (Ltailcall sig ros :: bb) rs m)
	E0 (Callstate s fd rs' m')
```
- For any stack `s`, function `f`, stack pointer `sp`, function signature `sig`, register-or-symbol call target `ros`, basic block `bb`, location set `rs`, memory `m`, function definition `fd`, new location set `rs'`, new memory `m'`:
	- If `rs'` is obtained by constructing the parent's/callers location set after the call and `ros` is resolved to a function definition `fd`, and freeing the current function's stack-frame returns a memory `m'`, then the machine may step from a block with a stack pointer at the beginning of the memory block and whose first instruction is `Ltailcall sig ros` to a call state that will execute `fd` with a new location set `rs'` and new memory `m'`.
```
| exec_Lbuiltin: forall s f sp ef args res bb rs m vargs t vres rs' m',
  eval_builtin_args ge rs sp m args vargs ->
  external_call ef ge vargs m t vres m' ->
  rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
  step (Block s f sp (Lbuiltin ef args res :: bb) rs m)
	 t (Block s f sp bb rs' m')
```
- For any stack `s`, function `f`, stack pointer `sp`, external function `ef`, builtin argument registers `args`, result register `res`, basic block `bb`, location set `rs`, memory `m`, evaluated argument values `vargs`, trace `t`, result values `vres`, new location set `pc`, new memory `m'`.
	- If evaluating the builtin arguments in the current environment/location set produces `vargs`, and executing the external builtin call with `vargs` and memory `m` produces a result `res`, new memory state `m'`, and trace `t`, and `rs'` is obtained by marking the locations destroyed by this operation as `vundef`, then setting the result register to value currently stored in `vres`, then the machine may step from block whose first instruction is `Lbuiltin ef args res`, to a block with new location set `rs` and new memory `m`. The trace is `t`.
```
| exec_Lbranch: forall s f sp pc bb rs m,
  step (Block s f sp (Lbranch pc :: bb) rs m)
	E0 (State s f sp pc rs m)
```
- For any stack `s`, function `f`, stack pointer `sp`, basic block `bb`, location set `rs`, memory `m`,
	- The machine may step from block whose first instruction is `Lbranch pc` to a state with the stack/function/stack-pointer/..etc unchanged.
```
| exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m,
  eval_condition cond (reglist rs args) m = Some b ->
  pc = (if b then pc1 else pc2) ->
  rs' = undef_regs (destroyed_by_cond cond) rs ->
  step (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m)
	E0 (State s f sp pc rs' m)
```
- For any stack `s`, function `f`, stack pointer `sp`, boolean condition `cond`, source registers `args`, program counter pc1, program pc2, location set `rs`, program counter pc, new location set `rs'`, memory `m`:
	- If `pc` is `pc1` if `b` is true or is `pc2` if `b` is false and `rs'` is obtained by marking the locations destroyed by this operation as `vundef`, then the machine may step from block whose first instruction is `Lcond cond args pc1 pc2` to a state where only the location set changes from `rs` to `rs'`.
```
| exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs',
  rs (R arg) = Vint n ->
  list_nth_z tbl (Int.unsigned n) = Some pc ->
  rs' = undef_regs (destroyed_by_jumptable) rs ->
  step (Block s f sp (Ljumptable arg tbl :: bb) rs m)
	E0 (State s f sp pc rs' m)
```
- For any stack `s`, function `f`, stack pointer `sp`, source register `arg`, table of branch nodes `tbl`, basic block `bb`, location set `rs`, memory `m`, value `n`, program counter `pc`, new location set `rs'`:
	- If register `arg` contains integer `n`, and indexing into the table `tbl` at index `n` returns the successor program counter `pc'` and `rs'` is obtained by marking the locations destroyed by this operation as `vundef`, then the machine may step from a block whose first instruction is `Ljumptable arg tbl`, to a state where only the location set changes from `rs` to `rs'`
```
| exec_Lreturn: forall s f sp bb rs m m',
  Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
  step (Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs m)
	E0 (Returnstate s (return_regs (parent_locset s) rs) m')
```
- For any stack `s`, function `f`, stack pointer `sp`, basic block `bb`, location set `rs`, memory `m` and new memory `m'`:
	- If freeing the current functions `f` stack frame returns a new memory `m'` then the machine may step from a block with a stack pointer at the beginning of the memory block and whose first instruction is `Lreturn` to a return state with the same call stack and where the location state represents the parents location set after the return state.
```
| exec_function_internal: forall s f rs m m' sp rs',
  Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
  rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
  step (Callstate s (Internal f) rs m)
	E0 (State s f (Vptr sp Ptrofs.zero) f.(fn_entrypoint) rs' m')
```
- For any stack `s`, function `f`, location set `rs`, memory `m`, new memory `m'`, stack block `sp`, new location set `rs'`:
	- If allocating `f`s stack frame succeeds and produces (`m', sp`), adn `rs'` is obtained by marking the locations destroyed by the operation as `vundef`, then the machine may step from a call-state to a state execut9ing `f` at `f.(fn_entrypoint)l,` with stack pointer `Vptr sp Ptrofs.zero`, location set `rs`, and memory `m'`.
```
| exec_function_external: forall s ef t args res rs m rs' m',
  args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
  external_call ef ge args m t res m' ->
  rs' = Locmap.setpair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
  step (Callstate s (External ef) rs m)
	 t (Returnstate s rs' m')
```
- For any stack `s`, external function `ef`, trace `t`, external-function argument values `args`, result value `res`, location set `rs`, memory `m`, new location set `rs'`, new memory `m'`:
	- If the list of outgoing argument registers `args` is computed, and the executing the external function call with `args` and memory `m` produces a result `res`, new memory state `m'` and trace `t`, and `rs'` is obtained by marking the locations destroyed by the operation as `vundef` then setting the external function's result location to res then the machine steps to a return state with the new location set `rs'` and new memory `m'`.
```
| exec_return: forall f sp rs1 bb s rs m,
  step (Returnstate (Stackframe f sp rs1 bb :: s) rs m)
	E0 (Block s f sp bb rs m).
```
- For any function `f`, stack pointer `sp`, location set `rs1`, basic block `bb`, stack `s`, location set `rs`, memory `m`:
	- the machine may step from a return state with a stack frame `Stackfraome f sp rs1 bb` on top of the call stack, to the next block `bb` of the function `f`, popping off the stack frame and restoring the saved pointer `sp` and location set `rs`.
