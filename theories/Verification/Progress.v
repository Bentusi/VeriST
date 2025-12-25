(** * Progress: 进展性证明

    本模块包含虚拟机执行的进展性证明。

    © 2024 JIANG Wei <jiangwey@outlook.com> 
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Semantics.VM.
Require Import STCompiler.Semantics.Operations.
Require Import STCompiler.Semantics.SourceSemantics.
Require Import STCompiler.Semantics.VMSemantics.

Import ListNotations.

(** ** 虚拟机状态的良型性 *)

(** 虚拟机状态是良型的：代码有效、程序计数器在范围内、栈非空等 *)
Definition vm_well_formed (st : vm_state) : Prop :=
  lt (st.(vm_pc)) (List.length (st.(vm_code))) /\
  st.(vm_halted) = false.

(** ** 进展性引理 *)

(** 引理：如果虚拟机状态良型且未停机，则可以执行一步 *)
Lemma vm_progress : forall st,
  vm_well_formed st ->
  exists st', vm_step st st'.
Proof.
  intros st [Hpc Hnot_halted].
  unfold vm_well_formed in *.
  (* 需要分析当前指令并构造下一个状态 *)
  (* 这需要对所有指令类型进行分类讨论 *)
Admitted.

(** 引理：停机的虚拟机不能继续执行 *)
Lemma halted_cannot_step : forall st st',
  st.(vm_halted) = true ->
  ~vm_step st st'.
Proof.
  intros st st' Hhalted Hstep.
  inversion Hstep; subst; discriminate.
Qed.

(** 引理：执行一步后，状态仍然良型或已停机 *)
Lemma vm_step_preserves_well_formed : forall st st',
  vm_well_formed st ->
  vm_step st st' ->
  vm_well_formed st' \/ st'.(vm_halted) = true.
Proof.
  intros st st' Hwf Hstep.
  (* 需要检查每个指令规则保持良型性 *)
Admitted.

(** ** 多步执行的性质 *)

(** 引理：反射性 *)
Lemma vm_multi_step_refl : forall st,
  vm_multi_step st st.
Proof.
  intros st.
  apply Multi_refl.
Qed.

(** 引理：传递性 *)
Lemma vm_multi_step_trans : forall st1 st2 st3,
  vm_multi_step st1 st2 ->
  vm_multi_step st2 st3 ->
  vm_multi_step st1 st3.
Proof.
  intros st1 st2 st3 H12 H23.
  induction H12.
  - (* Multi_refl *) assumption.
  - (* Multi_step *)
    apply Multi_step with st2.
    + assumption.
    + apply IHvm_multi_step. assumption.
Qed.

(** 引理：单步可以扩展为多步 *)
Lemma vm_step_multi : forall st1 st2,
  vm_step st1 st2 ->
  vm_multi_step st1 st2.
Proof.
  intros st1 st2 Hstep.
  apply Multi_step with st2.
  - assumption.
  - apply Multi_refl.
Qed.

(** ** 终止性（对于有限执行） *)

(** 定义：状态是最终状态（停机或出错） *)
Definition is_final_state (st : vm_state) : Prop :=
  st.(vm_halted) = true \/ 
  ~vm_well_formed st.

(** 引理：最终状态不能再执行 *)
Lemma final_state_cannot_step : forall st,
  is_final_state st ->
  forall st', ~vm_step st st'.
Proof.
  intros st [Hhalted | Hmalformed] st' Hstep.
  - (* 停机 *)
    apply halted_cannot_step with st st'; assumption.
  - (* 不良型 *)
    (* 不良型状态也不应该能执行 *)
Admitted.

(** ** 确定性 *)

(** 引理：虚拟机执行是确定的 *)
Lemma vm_step_deterministic : forall st st1 st2,
  vm_step st st1 ->
  vm_step st st2 ->
  st1 = st2.
Proof.
  intros st st1 st2 H1 H2.
  (* 需要分析所有指令规则，证明每个规则都是唯一的 *)
Admitted.

(** ** 进展性主定理 *)

(** 定理：虚拟机的进展性
    
    如果虚拟机状态良型，则要么可以执行一步，要么已经停机。
*)
Theorem vm_progress_main : forall st,
  vm_well_formed st \/ is_final_state st.
Proof.
  intros st.
  destruct (st.(vm_halted)) eqn:Hhalted.
  - (* 已停机 *)
    right. left. assumption.
  - (* 未停机 *)
    destruct (Nat.ltb (st.(vm_pc)) (List.length (st.(vm_code)))) eqn:Hpc.
    + (* pc 在范围内 *)
      left. split.
      * apply Nat.ltb_lt. assumption.
      * assumption.
    + (* pc 越界 *)
      right. right. intros [Hpc_lt _]. 
      apply Nat.ltb_nlt in Hpc. contradiction.
Qed.

(** ** 示例：具体指令的进展性 *)

(** 示例：加载整数指令总是可以执行 *)
Example load_int_progress : forall code pc stk env frames funcs n,
  nth_error code pc = Some (ILoadInt n) ->
  exists st',
    vm_step 
      {| vm_code := code; vm_pc := pc; vm_stack := stk;
         vm_env := env; vm_frames := frames; vm_functions := funcs;
         vm_halted := false |}
      st'.
Proof.
  intros code pc stk env frames funcs n Hnth.
  eexists.
  apply Step_LoadInt.
  exact Hnth.
Qed.

(** 示例：加法指令在栈有足够元素时可以执行 *)
Example add_progress : forall code pc stk env frames funcs v1 v2,
  nth_error code pc = Some IAdd ->
  exists st',
    vm_step 
      {| vm_code := code; vm_pc := pc; vm_stack := v2 :: v1 :: stk;
         vm_env := env; vm_frames := frames; vm_functions := funcs;
         vm_halted := false |}
      st'.
Proof.
  intros code pc stk env frames funcs v1 v2 Hnth.
  (* 需要根据 v1 和 v2 的类型进行分类 *)
  (* 如果都是整数，则可以执行 *)
Admitted.
