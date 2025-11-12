(** * Extract: OCaml 代码提取

    本模块配置从 Coq 代码到 OCaml 的提取。
    提取编译器为可执行的OCaml代码。
*)

(* 导入所有需要提取的模块 *)
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Semantics.Operations.
Require Import STCompiler.Semantics.VM.
Require Import STCompiler.Semantics.VMSemantics.
Require Import STCompiler.Compiler.CompilerState.
Require Import STCompiler.Compiler.CodeGen.
Require Import STCompiler.Compiler.Compiler.

Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Coq.extraction.ExtrOcamlZInt.

(* ================================================================= *)
(** ** 提取配置 *)

(* 标准提取配置已通过上述Require Import自动处理：
   - ExtrOcamlBasic: 基本类型（bool, nat, option, list等）
   - ExtrOcamlString: 字符串类型
   - ExtrOcamlNatInt: nat映射到OCaml的int
   - ExtrOcamlZInt: Z映射到OCaml的big_int
*)

(* ================================================================= *)
(** ** 提取目标函数 *)

(* 提取编译器主要函数 *)
Extraction Language OCaml.

(* 设置输出目录 *)
Set Extraction AccessOpaque.

(* 提取到单独的文件 *)
Separate Extraction
  (* 类型系统 *)
  ty value has_type typeof
  
  (* AST *)
  expr stmt binop unop
  var_decl param_decl param_kind
  function_def program_def compilation_unit
  
  (* 字节码 *)
  instr code
  
  (* 环境 *)
  env empty update lookup
  
  (* 虚拟机 *)
  vm_state init_vm_state
  
  (* 语义操作 *)
  eval_add eval_sub eval_mul eval_div eval_mod
  eval_neg
  eval_eq eval_ne eval_lt eval_le eval_gt eval_ge
  eval_and eval_or
  vm_step vm_multi_step vm_step_exec
  
  (* 编译器 *)
  compiler_state init_compiler_state
  emit current_address emit_list
  gen_load_const quality_marker_of
  compile_expr compile_stmt
  compile_function compile_program
  
  (* 运行时函数 *)
  run_vm.
