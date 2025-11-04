(** * VMSemantics: 虚拟机的操作语义

    本模块定义虚拟机中字节码执行的操作语义，
    包括单步执行和多步执行的归纳定义。
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Semantics.VM.
Require Import STCompiler.Semantics.Operations.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** 单步执行语义 *)

(** 虚拟机单步执行归纳定义
    vm_step st st' 表示虚拟机从状态 st 单步执行到状态 st' *)
Inductive vm_step : vm_state -> vm_state -> Prop :=

  (** 数据操作指令 *)
  
  | Step_LoadInt : forall c pc stk env frames funcs n,
      nth_error c pc = Some (ILoadInt n) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := VInt n :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_LoadReal : forall c pc stk env frames funcs r,
      nth_error c pc = Some (ILoadReal r) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := VReal r :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_LoadBool : forall c pc stk env frames funcs b,
      nth_error c pc = Some (ILoadBool b) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := VBool b :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_LoadString : forall c pc stk env frames funcs s,
      nth_error c pc = Some (ILoadString s) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := VString s :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_LoadVar : forall c pc stk env frames funcs x v,
      nth_error c pc = Some (ILoadVar x) ->
      lookup env x = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_StoreVar : forall c pc stk env frames funcs x v,
      nth_error c pc = Some (IStoreVar x) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := update env x v; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 算术指令 *)
  
  | Step_Add : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IAdd ->
      eval_add v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Sub : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some ISub ->
      eval_sub v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Mul : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IMul ->
      eval_mul v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Div : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IDiv ->
      eval_div v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Mod : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IMod ->
      eval_mod v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Neg : forall c pc stk env frames funcs v1 v,
      nth_error c pc = Some INeg ->
      eval_neg v1 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 比较指令 *)
  
  | Step_Eq : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IEq ->
      eval_eq v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Ne : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some INe ->
      eval_ne v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Lt : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some ILt ->
      eval_lt v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Le : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some ILe ->
      eval_le v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Gt : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IGt ->
      eval_gt v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Ge : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IGe ->
      eval_ge v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 逻辑指令 *)
  
  | Step_And : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IAnd ->
      eval_and v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Or : forall c pc stk env frames funcs v1 v2 v,
      nth_error c pc = Some IOr ->
      eval_or v1 v2 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Not : forall c pc stk env frames funcs v1 v,
      nth_error c pc = Some INot ->
      eval_not v1 = Some v ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v1 :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 控制流指令 *)
  
  | Step_Jmp : forall c pc stk env frames funcs target,
      nth_error c pc = Some (IJmp target) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := target; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Jz_True : forall c pc stk env frames funcs target,
      nth_error c pc = Some (IJz target) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := VBool false :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := target; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Jz_False : forall c pc stk env frames funcs target,
      nth_error c pc = Some (IJz target) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := VBool true :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Jnz_True : forall c pc stk env frames funcs target,
      nth_error c pc = Some (IJnz target) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := VBool true :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := target; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Jnz_False : forall c pc stk env frames funcs target,
      nth_error c pc = Some (IJnz target) ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := VBool false :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 函数调用指令 - 简化版本，完整实现在阶段3 *)
  
  | Step_Call : forall c pc stk env frames funcs target,
      nth_error c pc = Some (ICall target) ->
      (* 简化：暂不实现完整的调用帧管理 *)
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := target; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Ret : forall c pc stk env frames funcs,
      nth_error c pc = Some IRet ->
      (* 简化：暂不实现完整的返回处理 *)
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 栈操作指令 *)
  
  | Step_Pop : forall c pc stk env frames funcs v,
      nth_error c pc = Some IPop ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
                 
  | Step_Dup : forall c pc stk env frames funcs v,
      nth_error c pc = Some IDup ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := v :: v :: stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}

  (** 系统指令 *)
  
  | Step_Halt : forall c pc stk env frames funcs,
      nth_error c pc = Some IHalt ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := true |}
                 
  | Step_Nop : forall c pc stk env frames funcs,
      nth_error c pc = Some INop ->
      vm_step {| vm_code := c; vm_pc := pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}
              {| vm_code := c; vm_pc := S pc; vm_stack := stk;
                 vm_env := env; vm_frames := frames; vm_functions := funcs;
                 vm_halted := false |}.

(** ** 多步执行语义 *)

(** 虚拟机多步执行归纳定义
    vm_multi_step st st' 表示虚拟机从状态 st 经过零步或多步执行到状态 st' *)
Inductive vm_multi_step : vm_state -> vm_state -> Prop :=
  | Multi_refl : forall st,
      vm_multi_step st st
      
  | Multi_step : forall st1 st2 st3,
      vm_step st1 st2 ->
      vm_multi_step st2 st3 ->
      vm_multi_step st1 st3.

(** ** 基本示例 *)

(** 示例：加载整数常量 *)
Example ex_load_int :
  vm_step {| vm_code := [ILoadInt 42; IHalt];
             vm_pc := 0%nat;
             vm_stack := [];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := false |}
          {| vm_code := [ILoadInt 42; IHalt];
             vm_pc := 1%nat;
             vm_stack := [VInt 42];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := false |}.
Proof.
  apply Step_LoadInt. reflexivity.
Qed.

(** 示例：加法运算 *)
Example ex_add :
  vm_step {| vm_code := [IAdd];
             vm_pc := 0%nat;
             vm_stack := [VInt 5; VInt 3];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := false |}
          {| vm_code := [IAdd];
             vm_pc := 1%nat;
             vm_stack := [VInt 8];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := false |}.
Proof.
  apply Step_Add with (v1 := VInt 3) (v2 := VInt 5) (v := VInt 8).
  - reflexivity.
  - reflexivity.
Qed.

(** 示例：停机 *)
Example ex_halt :
  vm_step {| vm_code := [IHalt];
             vm_pc := 0%nat;
             vm_stack := [];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := false |}
          {| vm_code := [IHalt];
             vm_pc := 0%nat;
             vm_stack := [];
             vm_env := empty;
             vm_frames := [];
             vm_functions := [];
             vm_halted := true |}.
Proof.
  apply Step_Halt. reflexivity.
Qed.

(** 示例：多步执行 - 加载两个数并相加 *)
Example ex_multi_step_add :
  vm_multi_step 
    {| vm_code := [ILoadInt 3; ILoadInt 5; IAdd; IHalt];
       vm_pc := 0%nat;
       vm_stack := [];
       vm_env := empty;
       vm_frames := [];
       vm_functions := [];
       vm_halted := false |}
    {| vm_code := [ILoadInt 3; ILoadInt 5; IAdd; IHalt];
       vm_pc := 3%nat;
       vm_stack := [VInt 8];
       vm_env := empty;
       vm_frames := [];
       vm_functions := [];
       vm_halted := false |}.
Proof.
  eapply Multi_step. apply Step_LoadInt. reflexivity.
  eapply Multi_step. apply Step_LoadInt. reflexivity.
  eapply Multi_step. apply Step_Add with (v1 := VInt 3) (v2 := VInt 5) (v := VInt 8).
  reflexivity. reflexivity.
  apply Multi_refl.
Qed.
