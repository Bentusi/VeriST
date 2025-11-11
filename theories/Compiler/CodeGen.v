(** * CodeGen: 代码生成工具

    本模块提供用于生成字节码的辅助工具。
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Compiler.CompilerState.

Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(** ** 质量位辅助 **)

(** 为质量位常量生成唯一的标记值。
    这些标记会在运行时被解释为“下一个常量携带的质量信息”。
    我们选取负值区间，避免与用户程序中的普通整型常量冲突。 *)
Definition quality_marker_base : Z := (-1024)%Z.

(** 将质量位编码为整型标记。 *)
Definition quality_marker_of (q : quality) : Z :=
  match q with
  | QGood => quality_marker_base
  | QBad => quality_marker_base - 1
  | QUncertain => quality_marker_base - 2
  end.

(** 生成用于携带质量信息的指令前缀。
    运行时语义需要识别该前缀并与后续常量进行组合。 *)
Definition gen_quality_prefix (q : quality) : list instr :=
  [ILoadInt (quality_marker_of q)].

(** ** 代码生成辅助函数 **)

(** 生成加载常量的指令序列 *)
Definition gen_load_const (v : value) : list instr :=
  match v with
  | VBool b => [ILoadBool b]
  | VInt n => [ILoadInt n]
  | VReal r => [ILoadReal r]
  | VQBool b q => gen_quality_prefix q ++ [ILoadBool b]
  | VQInt n q => gen_quality_prefix q ++ [ILoadInt n]
  | VQReal r q => gen_quality_prefix q ++ [ILoadReal r]
  | VString s => [ILoadString s]
  | VVoid => []  (* 空值不生成指令 *)
  end.

(** 生成加载变量的指令 *)
Definition gen_load_var (name : string) : instr :=
  ILoadVar name.

(** 生成存储变量的指令 *)
Definition gen_store_var (name : string) : instr :=
  IStoreVar name.

(** 生成跳转指令 *)
Definition gen_jump (addr : address) : instr :=
  IJmp addr.

(** 生成条件跳转指令（零时跳转） *)
Definition gen_jump_if_zero (addr : address) : instr :=
  IJz addr.

(** 生成条件跳转指令（非零时跳转） *)
Definition gen_jump_if_nonzero (addr : address) : instr :=
  IJnz addr.

(** 生成函数调用指令 *)
Definition gen_call (addr : address) : instr :=
  ICall addr.

(** 生成返回指令 *)
Definition gen_return : instr :=
  IRet.

(** 生成停机指令 *)
Definition gen_halt : instr :=
  IHalt.

(** ** 优化相关（预留） *)

(** 窥孔优化：移除冗余的加载-存储序列 *)
Definition peephole_optimize (code : list instr) : list instr :=
  (* 简化实现：暂不优化，直接返回原代码 *)
  code.

(** 常量折叠检查 *)
Definition is_constant_expr (e : nat) : bool :=
  (* 简化实现：暂不实现 *)
  false.

(** 死代码消除标记 *)
Definition mark_dead_code (code : list instr) : list bool :=
  (* 简化实现：所有代码都是活跃的 *)
  map (fun _ => true) code.

(** ** 代码验证 *)

(** 检查跳转目标是否有效 *)
Fixpoint valid_jump_targets (code : list instr) (max_addr : nat) : bool :=
  match code with
  | nil => true
  | IJmp addr :: rest =>
      (addr <? max_addr) && valid_jump_targets rest max_addr
  | IJz addr :: rest =>
      (addr <? max_addr) && valid_jump_targets rest max_addr
  | IJnz addr :: rest =>
      (addr <? max_addr) && valid_jump_targets rest max_addr
  | ICall addr :: rest =>
      (addr <? max_addr) && valid_jump_targets rest max_addr
  | _ :: rest =>
      valid_jump_targets rest max_addr
  end.

(** 验证生成的代码 *)
Definition validate_code (code : list instr) : bool :=
  let max_addr := length code in
  valid_jump_targets code max_addr.

(** ** 代码打印（用于调试） *)

(** 将指令转换为可读字符串（简化版） *)
Definition instr_to_string (i : instr) : string :=
  match i with
  | ILoadInt _ => "LOAD_INT"
  | ILoadReal _ => "LOAD_REAL"
  | ILoadBool _ => "LOAD_BOOL"
  | ILoadString _ => "LOAD_STRING"
  | ILoadVar x => "LOAD_VAR " ++ x
  | IStoreVar x => "STORE_VAR " ++ x
  | IAdd => "ADD"
  | ISub => "SUB"
  | IMul => "MUL"
  | IDiv => "DIV"
  | IMod => "MOD"
  | INeg => "NEG"
  | IEq => "EQ"
  | INe => "NE"
  | ILt => "LT"
  | ILe => "LE"
  | IGt => "GT"
  | IGe => "GE"
  | IAnd => "AND"
  | IOr => "OR"
  | INot => "NOT"
  | IJmp _ => "JMP"
  | IJz _ => "JZ"
  | IJnz _ => "JNZ"
  | ICall _ => "CALL"
  | IRet => "RET"
  | ILoadParam _ => "LOAD_PARAM"
  | IStoreParam _ => "STORE_PARAM"
  | IPop => "POP"
  | IDup => "DUP"
  | IHalt => "HALT"
  | INop => "NOP"
  end.

(** 打印整个代码序列（简化版） *)
Fixpoint code_to_string_list (code : list instr) : list string :=
  map instr_to_string code.
