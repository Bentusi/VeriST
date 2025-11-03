(** * Environment: IEC 61131-3 ST 的变量环境

    本模块定义用于源语言语义和虚拟机执行的变量环境。
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** 环境定义 *)

(** 环境将变量名映射到值 *)
Definition env : Type := string -> option value.

(** 空环境 *)
Definition empty : env := fun _ => None.

(** 用新绑定更新环境 *)
Definition update (e : env) (x : string) (v : value) : env :=
  fun y => if String.eqb x y then Some v else e y.

(** 在环境中查找变量 *)
Definition lookup (e : env) (x : string) : option value :=
  e x.

(** ** 环境属性 *)

(** 在空环境中查找返回 None *)
Lemma lookup_empty : forall x,
  lookup empty x = None.
Proof.
  intros x. unfold lookup, empty. reflexivity.
Qed.

(** Update and lookup same variable *)
Lemma update_eq : forall e x v,
  lookup (update e x v) x = Some v.
Proof.
  intros e x v.
  unfold lookup, update.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

(** 更新和查找不同变量 *)
Lemma update_neq : forall e x1 x2 v,
  x1 <> x2 ->
  lookup (update e x1 v) x2 = lookup e x2.
Proof.
  intros e x1 x2 v Hneq.
  unfold lookup, update.
  destruct (String.eqb_spec x1 x2).
  - contradiction.
  - reflexivity.
Qed.

(** 更新会覆盖先前的绑定 *)
Lemma update_shadow : forall e x v1 v2,
  update (update e x v1) x v2 = update e x v2.
Proof.
  intros e x v1 v2.
  unfold update.
  apply functional_extensionality.
  intros y.
  destruct (String.eqb x y); reflexivity.
Qed.

(** 不同变量的更新可交换 *)
Lemma update_permute : forall e x1 x2 v1 v2,
  x1 <> x2 ->
  update (update e x1 v1) x2 v2 = update (update e x2 v2) x1 v1.
Proof.
  intros e x1 x2 v1 v2 Hneq.
  unfold update.
  apply functional_extensionality.
  intros y.
  destruct (String.eqb_spec x1 y);
  destruct (String.eqb_spec x2 y);
  subst; try reflexivity; try contradiction.
Qed.

(** ** 类型化环境 *)

(** 类型环境将变量名映射到类型 *)
Definition type_env : Type := string -> option ty.

(** 空类型环境 *)
Definition empty_tenv : type_env := fun _ => None.

(** 更新类型环境 *)
Definition update_tenv (te : type_env) (x : string) (t : ty) : type_env :=
  fun y => if String.eqb x y then Some t else te y.

(** ** 良类型环境 *)

(** 如果每个变量都具有预期类型，
    则环境相对于类型环境是良类型的 *)
Definition well_typed_env (te : type_env) (e : env) : Prop :=
  forall x v, lookup e x = Some v ->
              exists t, te x = Some t /\ has_type v t.

(** 空环境是良类型的 *)
Lemma empty_well_typed : 
  well_typed_env empty_tenv empty.
Proof.
  unfold well_typed_env, lookup, empty.
  intros x v H. discriminate.
Qed.

(** 更新保持良类型性 - 暂时承认 *)
Axiom update_preserves_typing : forall te e x v t,
  well_typed_env te e ->
  has_type v t ->
  well_typed_env (update_tenv te x t) (update e x v).

(** ** 批量更新 *)

(** 用绑定列表更新环境 *)
Fixpoint updates (e : env) (bindings : list (string * value)) : env :=
  match bindings with
  | [] => e
  | (x, v) :: rest => updates (update e x v) rest
  end.

(** ** 环境等价性 *)

(** 两个环境在变量集合上等价 *)
Definition env_equiv_on (vars : list string) (e1 e2 : env) : Prop :=
  forall x, In x vars -> lookup e1 x = lookup e2 x.

(** 环境等价性的自反性 *)
Lemma env_equiv_refl : forall vars e,
  env_equiv_on vars e e.
Proof.
  intros vars e x Hin. reflexivity.
Qed.

(** 环境等价性的对称性 *)
Lemma env_equiv_sym : forall vars e1 e2,
  env_equiv_on vars e1 e2 ->
  env_equiv_on vars e2 e1.
Proof.
  intros vars e1 e2 H x Hin.
  symmetry. apply H. assumption.
Qed.

(** ** 示例 *)

Example ex_empty_lookup : lookup empty "x" = None.
Proof. apply lookup_empty. Qed.

Example ex_update_lookup :
  lookup (update empty "x" (VInt 5%Z)) "x" = Some (VInt 5%Z).
Proof. apply update_eq. Qed.

Example ex_update_lookup_diff :
  lookup (update empty "x" (VInt 5%Z)) "y" = None.
Proof.
  apply update_neq. discriminate.
Qed.

Example ex_multiple_updates :
  let e := update (update empty "x" (VInt 1%Z)) "y" (VInt 2%Z) in
  lookup e "x" = Some (VInt 1%Z) /\ lookup e "y" = Some (VInt 2%Z).
Proof.
  split.
  - apply update_neq. discriminate.
  - apply update_eq.
Qed.
