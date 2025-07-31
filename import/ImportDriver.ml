(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Commandline
open Clflags
open CommonOptions
open Timing
open Driveraux
open Frontend
open Assembler
open Linker
open Diagnostics

(* Name used for version string etc. *)
let tool_name = "CompCert AST compiler"

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"

let nolink () =
  !option_c || !option_S

let object_filename sourcename =
  if nolink () then
    output_filename ~final: !option_c sourcename ~suffix:".o"
  else
    tmp_file ".o"

(* From Cminor AST to asm *)

let compile_to_asm sourcename ofile =
  (* Prepare to dump RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename sourcename ~suffix:ext)
      else None in
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  set_dest AsmToJSON.destination option_sdump !sdump_suffix;
  (* Convert to Asm *)
  let prog = ImportProgram.prog in
  let asm =
    match Compiler.apply_partial
               (Compiler.transf_cminor_program prog)
               Asmexpand.expand_program with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
      let loc = file_loc sourcename in
        fatal_error loc "%a"  print_error msg in
  (* Dump Asm in binary and JSON format *)
  AsmToJSON.print_if asm sourcename;
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

(* From Cminor AST to asm or object *)

let compile_to_obj sourcename =
  if !option_S then begin
    compile_to_asm sourcename
      (output_filename ~final:true sourcename ~suffix:".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ~suffix:".s"
      else tmp_file ".s" in
    compile_to_asm sourcename asmname;
    let objname = object_filename sourcename  in
    assemble asmname objname;
    objname
  end

(* Processing of .S and .s files *)

let process_s_file sourcename =
  ensure_inputfile_exists sourcename;
  let objname = object_filename sourcename in
  assemble sourcename objname;
  objname

let process_S_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = tmp_file ".s" in
    preprocess sourcename preproname;
    let objname = object_filename sourcename in
    assemble preproname objname;
    objname
  end

let target_help =
  if Configuration.arch = "arm" && Configuration.model <> "armv6" then
{|Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
|}
else
  ""

let toolchain_help =
  if not Configuration.gnu_toolchain then begin
{|Toolchain options:
  -t tof:env     Select target processor for the diab toolchain
|} end else
    ""

let usage_string =
  version_string tool_name ^
  {|Usage: vcomp [options]
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
|} ^
  prepro_help ^
  language_support_help ^
 DebugInit.debugging_help ^
{|Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -Obranchless   Optimize to generate fewer conditional branches; try to produce
                 branch-free instruction sequences as much as possible
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
  -finline-functions-called-once Integrate functions only required by their
                 single caller [on]
  -fif-conversion Perform if-conversion (generation of conditional moves) [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -fpic / -fPIC  Generate position-independent code [off]
  -fpie / -fPIE  Generate position-independent executables [on if supported]
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -fcommon       Put uninitialized globals in the common section [on].
|} ^
 target_help ^
 toolchain_help ^
 assembler_help ^
 linker_help ^
{|Tracing options:
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
|} ^
  general_help ^
  warning_help

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let dump_mnemonics destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  AsmToJSON.pp_mnemonics pp;
  Format.pp_print_flush pp ();
  close_out oc;
  exit 0

let optimization_options = [
  option_ftailcalls; option_fifconversion; option_fconstprop; option_fcse;
  option_fredundancy; option_finline; option_finline_functions_called_once;
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let num_input_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  let check_align n =
    if n <= 0 || ((n land (n - 1)) <> 0) then
      error no_loc "requested alignment %d is not a power of 2" n
    in
  let set_pic_mode () =
    if Configuration.pic_supported
    then option_fpic := true
    else warning no_loc Unnamed
         "option -fpic not supported on this platform, ignored" in
  let set_pie_mode () =
    if Configuration.pic_supported
    then option_fpie := true
    else warning no_loc Unnamed
         "option -fpie not supported on this platform, ignored" in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;]
(* Getting version info *)
  @ version_options tool_name @
(* Enforcing CompCert build numbers for QSKs and mnemonics dump *)
  (if Version.buildnr <> "" then
     [Exact "-dump-mnemonics", String  dump_mnemonics;]
   else []) @
(* Processing options *)
 [ Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
    @
  (* Language support options *)
    language_support_options
  (* Debugging options *)
    @ DebugInit.debugging_actions @
(* Code generation options -- more below *)
 [
  Exact "-dmr", Set option_dmr;
  Exact "-tmr", Set option_tmr;
  Exact "-O0", Unit (unset_all optimization_options);
  Exact "-O", Unit (set_all optimization_options);
  _Regexp "-O[123]$", Unit (set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-Obranchless", Set option_Obranchless;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n);
  Exact "-falign-functions", Integer(fun n -> check_align n; option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> check_align n; option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> check_align n; option_faligncondbranchs := n);
  Exact "-fpic", Unit set_pic_mode;
  Exact "-fPIC", Unit set_pic_mode;
  Exact "-fno-pic", Unset option_fpic;
  Exact "-fno-PIC", Unset option_fpic;
  Exact "-fpie", Unit set_pie_mode;
  Exact "-fPIE", Unit set_pie_mode;
  Exact "-fno-pie", Unset option_fpie;
  Exact "-fno-PIE", Unset option_fpie ] @
      f_opt "common" option_fcommon @
(* Target processor options *)
  (if Configuration.arch = "arm" then
    if Configuration.model = "armv6" then
      [ Exact "-marm", Ignore ] (* Thumb needs ARMv6T2 or ARMv7 *)
    else
      [ Exact "-mthumb", Set option_mthumb;
        Exact "-marm", Unset option_mthumb; ]
   else []) @
(* Toolchain options *)
    (if not Configuration.gnu_toolchain then
       [Exact "-t", String (fun arg -> push_linker_arg "-t"; push_linker_arg arg;
                             prepro_options := arg :: "-t" :: !prepro_options;
                             assembler_options := arg :: "-t" :: !assembler_options;)]
     else
       []) @
(* Assembling options *)
  assembler_actions @
(* Linking options *)
  linker_actions @
(* Tracing options *)
 [ Exact "-dprepro", Set option_dprepro;
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-dall", Self (fun _ ->
    option_dprepro := true;
    option_dparse := true;
    option_dcmedium := true;
    option_dclight := true;
    option_dcminor := true;
    option_drtl := true;
    option_dltl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);
  Exact "-sdump-folder", String (fun s -> AsmToJSON.sdump_folder := s);] @
(* General options *)
   general_options @
(* Diagnostic options *)
  warning_options @
[
]
(* Optimization options *)
(* -f options: come in -f and -fno- variants *)
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "if-conversion" option_fifconversion
  @ f_opt "const-prop" option_fconstprop
  @ f_opt "cse" option_fcse
  @ f_opt "redundancy" option_fredundancy
  @ f_opt "inline" option_finline
  @ f_opt "inline-functions-called-once" option_finline_functions_called_once
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      fatal_error no_loc "Unknown option `%s'" s);
(* File arguments *)
  Suffix ".s", Self (fun s ->
      push_action process_s_file s; incr num_source_files; incr num_input_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".sx", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  ]

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
           };
    Printexc.record_backtrace true;
    Frontend.init ();
    parse_cmdline cmdline_actions;
    DebugInit.init (); (* Initialize the debug functions *)
    if nolink () && !option_o <> None then
      fatal_error no_loc "ambiguous '-o' option";
    ignore (compile_to_obj "ImportProgram.v");
    let linker_args = time "Total compilation time" perform_actions () in
    if not (nolink ()) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
    check_errors ()
  with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> error_summary (); exit 2
  | e -> crash e
