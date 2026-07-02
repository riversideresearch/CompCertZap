

```
Record function: Type := mkfunction {
	fn_sig: signature;
	fn_params: list reg;
	fn_stacksize: Z;
	fn_code: code;
	fn_entrypoint: node
}
```
In the above we define a function type with one constructor `mkfunction` -> which implies we only have one way to make a function. We say a function comprises of its signature, parameters, stack-size, code(body), and its entry-point.

`State cs f sp pc rs m` -> describes the execution point within a function.

	[f] is the current function
	[sp] stack pointer ~ rsp
	[pc] is the current point (CFG node) within the code [c] ~ rip
	[rs] gives the current values for the pseudo-registers > state of registers in the calling function 
	[m] current memory state
	
`Callstate cs f args m` -> intermediate state that appears during function calls.
`Returnstate cs v m` -> intermediate state that appears when function terminate.



- There are only 3 states at least wrt the semantics of RTL

In all 3 states, `cs` represents the call stack, which is a list of stack frame. Each stack frame represents a function call in progress.

Transition between states is represented as an inductive proposition.
\[step ge state1 t state2\], where ge is the global environment,
state1 the initial state, state2 the final state and t is the trace of sys calls performed during this transition.
```rocq
Inductive step: state -> trace -> state -> Prop :=
 | exec_Inop:
	 forall s f sp pc rs m pc',
	 (fn_code f)!pc = Some(Inop pc') ->
	 step (State s f sp pc rs m)
	 EO (State s f sp pc' rs m)
```
- for any call-stack s, function f, stack pointer p, program counter pc, register state rs, current memory state, and some other program counter.
	- `(fn_code f)!pc` -> PTree.get pc (fn_code f). code is a tree of instructions (CFG)
			"Get the value stored at key pc in the tree (fn_code f)"
	- if the lookup of the current pc in the tree of instruction(CFG) is an Inop instruction with successor pc'.
			then the machine may transition from st1 to st2, where only the pc changes from pc to pc' and no trace of sys calls performed during the transition
```
| exec_Iop:
	forall s f sp pc rs m op args res pc' v,
	(fn_code f)!pc = Some(Iop op args res pc') ->
	eval_operation ge sp addr rs##args = Some v ->
	step (State s f sp pc rs m) E0 (State s f sp pc' (rs#dst <- v) m)
```

- `rs##args` := (map (fun r => r => Regmap.get r a))
- `rs#res <- v` := (Regmap.set res v rs)
- for all call stack `s`, function `f`, stack pointer, program counter `pc`, registers state `rs`, current memory state, register operands of the current instruction `args`, return register operand of the current instruction `res`, successor program counter `pc`, and value `v`.
		- if the lookup of the current pc in the tree of instructions(CFG) is an arithmetic operation on the values of the registers `args` that stores it result in the res register and branches to pc' and the evaluation of that operation returns a value v.
			then the machine may step from st1 to st2, where the pc changes from pc to pc' and the result `v` of the operation is updated in the register `res`. No trace of sys calls performed during the transition.
```
| exec_Iload:
	forall s f sp pc rs m chunk addr args dst pc' a v,
	(fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
	eval_addressing ge sp addr rs##args = Some a ->
	Mem.loadv chunk m a = Some v ->
	step (State s f sp pc rs m)
	E0 (State s f sp pc' (rs#dst <- v) m)
```

- For any stack `s`, function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, memory `m`, memory chunk `chunk`, addressing mode `addr`, source registers `args`, destination register `dst`, successor program counter `pc'`, address `a`, and a loaded value `v`:
	- if looking up `pc` in the function code returns the load instruction `Iload chunk addr args dst pc'`, and evaluating the addressing mode `addr` using the values of registers `args` gives address `a`, and loading memory chunk `chunk` from memory `m` at address `a` gives value `v`, then the machine can step to a new state where `pc` become `pc'`, register `dst` is updated to `v`, and memory/stack/etc. stay unchanged. No trace of sys calls performed during the transition.
```
| exec_Istore:
	forall s f sp pc rs m chunk addr args src pc' a m',
	(fn_code f)!pc = Some(Istore chunk addr args src pc') ->
	eval_addressing ge sp addr rs##args = Some a ->
	Mem.storev chunk m a rs#src = Some m' ->
	step (State s f sp pc rs m) E0 (State s f sp pc' rs m')
```
- For any stack `s`, function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, memory `m`, memory chunk `chunk`, addressing mode `addr`, source registers `args`, source register `src`, successor program counter `pc`, address `a`, and successor memory state `m'`:
	- If looking up pc in the function code returns the store instruction `Isotre chunk addr args src pc` and evaluating the addressing mode `addr` using the values of registers `args` gives address `a`, and storing to memory chunk `chunk` at address `a` from source register `src` gives a modified memory state, then the machine can step to a new state where pc becomes `pc'`, memory state become `m'` and stack/function... remains unchanged. No trace of sys calls performed during the transition.

```
| exec_Icall
	forall s f sp pc rs m sig ros args res pc' fd,
	(fn_code f)!pc = Some(Icall sig ros args res pc') ->
	find_function ros rs = Some fd ->
	funsig fd = sig ->
	step (State s f sp pc rs m) E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
```
- For any stack `s`, current function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, memory `m`, signature `sig`, register-or-symbol call target `ros`, argument registers `args`, result register `res`, successor program counter `pc'`, and function definition `fd`: if looking up pc in the function codes gives `Icall sig ros args res pc'`, and `ros` resolves to a function definition `fd`, and `fd` has a signature `sig`, then the machine steps with trace E0 to call-state that will execute `fd` with argument values `rs##args` and memory `m`.
	- `Stackframe res f sp pc' rs::s` is the important part. This saves the callers continuation:
		- When the called function returns, puts it result in `res`, resume function `f` as `pc'`, restore stack pointer `sp`, restore registers `rs`, and continue with old stack `s`. So `pc` is not where the call immediately executes. It is where the caller resumes after the callee returns
```
| exec_Itailcall
	forall s f stk pc rs m sig ros args fd m',
	(fn_code f)!pc = Some(Itailcall sig ros args) ->
	find_function ros rs = Some fd ->
	funsig fd = sig ->
	Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
	step (State s f (Vptr stk Ptrofs.zero) pc rs m) E0 (Callstate s fd rs##args m')
```
- For any stack `s`, current function `f`, block of memory `stk`, program counter `pc`, register state `rs`, memory `m`, function signature `sig`, register or symbol `ros`, argument registers `args`, function definition `fd`, and successor memory state `m'`:
	- If looking up pc in the function codes gives `Itailcall sig ros args`, and `ros` resolves to a function definition `fd`, and `fd` has a signature `sig` and freeing the current function's stack-frame returns a memory `m'`, then machine may step with trace E0 from a state with a stack pointer at the beginning of the memory block to a call state with the original stack frame that will execute `fd` with argument values `rs##args` and memory m'.
```
| exec_Ibuiltin
	forall s f sp pc rs m ef args res pc' vargs t vres m',
	(fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
	eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
	external_call ef ge vargs m t vres m' ->
	step (State s f sp pc rs m) t (State s f sp pc' (regmap_setres res vres rs) m')
```
- Note: when a variable is defined in a section, any function in that section has to implicitly become a parameter if called outside of the scope of the section.
- For any stack `s`, current function `f`, stack pointer `sp`, register state `rs`, memory `m`, external function `ef`, builtin argument registers `args`, result register `res`, successor program counter `pc'`, evaluated argument values `vargs`, trace `t`, result value `vres`, and new memory `m'`:
	- IF looking up pc in the function code gives `Ibuiltin ef args res pc'` and evaluating the builtin arguments in the current environment/registers produces `vargs`, and executing the external builtin call with `vargs` and memory `m` produces a result `res`, new memory state `m`, and trace `t`, then the machine may step from st1 to st2 where `pc` become `pc'`, the result location is updates with `vres` in the register state, memory become `m'`, and the trace of the step is t. 
```
| exec_Icond
	forall s f sp pc rs m cond args ifso ifnot b pc',
	(fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
	eval_condition cond rs##args m = Some b->
	pc' = (if b then ifso else ifnot) ->
	step (State s f sp pc rs m) E0 (State s f pc' rs m)
```
- For any stack `s`, current function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, memory `m`, boolean condition `cond`, source registers `args`, cfg node `ifso`, cfg node `ifnot`, value `b` and successor program counter `pc'`:
	- If looking up pc in the function code gives `Icond cond args ifso ifnot` and evaluating the condition over the values of registers `args` gives the boolean value `b`, and the successor program counter `pc'` is `ifso` if `b` is true and `ifnot` if `b` is false, then the machine steps from st1 to st2 where only `pc` changes to `pc'` and the trace is E0.
```
| exec_Ijumptable
	forall s f sp pc rs m arg tbl n pc'
	(fn_code f)!pc = Some(Ijumptable arg tbl) ->
	rs#arg = Vint n ->
	list_nth_z tbl (Int.unsigned n) = Some pc' ->
	step (State s f sp pc rs m) E0 (State s sp pc' rs m)
```
- For any stack `s`, current function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, memory `m`, source register `arg`, table of branch nodes `tbl`, value `n`, successor program counter `pc'`:
	- If looking up `pc` in the function code gives `Ijumptable arg tbl` and register `arg` contains integer `n` and indexing into the table `tbl` at `n` returns the successor program counter `pc'`, then the machine may step from st1 to st2 where only `pc` changes to `pc'` and the trace is `E0`.
```
| exec_Ireturn
	forall s f stk pc rs m or m',
	(fn_code f)!pc = Some(Ireturn or) ->
	Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
	step (State s f (Vptr stk Ptrof.zero) pc rs m) E0 (Returnstate s (regmap_optget or Vundef rs) m')
```
- For any stack `s`, current function `f`, block of memory `stk`, program counter `pc`, register state `rs`, memory `m`, optional return register `or`, new memory `m'`:
	- If looking up `pc` in the function code gives `Ireturn or` and freeing the current functions `f` stack frame returns a new memory `m'`, then the machine may step with trace `E0` from state with a stack pointer at the beginning of the memory block to a return state with the same call stack where the value of the given register is returned or `vundef` is none is given, and the memory changes from `m` to `m'`
```
| exec_function_internal:
	forall s f args m m' stk,
	Val.has_argtype_list args f.(fn_sig).(sig_args) ->
	Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
	step (Callstate s (Internal f) args m) E0 
		(State s f (Vptr stk Ptrofs.zero) f.(fn_entrypoint) (init_regs args f.(fn_params)) m')
```
- For any stack `s`, current function `f`, argument values `args`, memory `m`, new memory `m'`, block of memory `stk`:
	- If the argument registers `args` has the same type as the type in the function signature `sig`, and allocating `f`s stack frame succeeds, then the machine may step with trace `E0` from a call state with an internal function to a (first executable state of the function) state with a stack pointer at the beginning of the memory block, `pc` at the start/entry-point of the function, registers updated with `args` from the function params, and a new memory `m'`.
	- `init_regs args f.(fn_params)` puts each argument value into the corresponding parameter register. So the call state carries values, and init_regs places them into the function's parameter registers.
```
| exec_function_external:
	forall s ef args res t m m',
	external_call ef ge args m t res m' ->
	step (Callstate s (External ef) args m) t (Returnstate s res m')
```
- For any stack `s`, external function `ef`, argument values `args`, result value `res`, trace `t`, memory `m`, new memory `m`:
	- If executing the external function call with `args` and memory `m` produces a result res, new memory state `m'` and trace `t`, then the machine may step from a call state of the external function `ef` to a return state where only the memory `m` changes to `m'`. Trace is `t`. 
```
| exec_return:
	forall res f sp pc rs s vres m,
	step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
		E0 (State s f sp pc (rs#rs <- vres) m).
```
- For any result register `res`, current function `f`, stack pointer `sp`, program counter `pc`, register state `rs`, stack `s`, return value `vres` and memory `m`: the machine may step from a return state whose top stack-frame state in the call stack to a state with the stack frame popped off, restoring the saved stack pointer `sp`, resuming execution in function `f` at program counter `pc` and register state `rs` and then writing the returned value `vres` into register `res`. Trace is `E0`.