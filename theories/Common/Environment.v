(** * Environment: Variable Environments for IEC 61131-3 ST

    This module defines variable environments used in both
    source language semantics and virtual machine execution.
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

(** ** Environment Definition *)

(** Environment maps variable names to values *)
Definition env : Type := string -> option value.

(** Empty environment *)
Definition empty : env := fun _ => None.

(** Update environment with a new binding *)
Definition update (e : env) (x : string) (v : value) : env :=
  fun y => if String.eqb x y then Some v else e y.

(** Lookup a variable in the environment *)
Definition lookup (e : env) (x : string) : option value :=
  e x.

(** ** Environment Properties *)

(** Lookup in empty environment returns None *)
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

(** Update and lookup different variable *)
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

(** Update shadows previous binding *)
Lemma update_shadow : forall e x v1 v2,
  update (update e x v1) x v2 = update e x v2.
Proof.
  intros e x v1 v2.
  unfold update.
  apply functional_extensionality.
  intros y.
  destruct (String.eqb x y); reflexivity.
Qed.

(** Updates of different variables commute *)
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

(** ** Typed Environment *)

(** Type environment maps variable names to types *)
Definition type_env : Type := string -> option ty.

(** Empty type environment *)
Definition empty_tenv : type_env := fun _ => None.

(** Update type environment *)
Definition update_tenv (te : type_env) (x : string) (t : ty) : type_env :=
  fun y => if String.eqb x y then Some t else te y.

(** ** Well-Typed Environment *)

(** An environment is well-typed with respect to a type environment
    if every variable has the expected type *)
Definition well_typed_env (te : type_env) (e : env) : Prop :=
  forall x v, lookup e x = Some v ->
              exists t, te x = Some t /\ has_type v t.

(** Empty environment is well-typed *)
Lemma empty_well_typed : 
  well_typed_env empty_tenv empty.
Proof.
  unfold well_typed_env, lookup, empty.
  intros x v H. discriminate.
Qed.

(** Update preserves well-typedness - we admit for now *)
Axiom update_preserves_typing : forall te e x v t,
  well_typed_env te e ->
  has_type v t ->
  well_typed_env (update_tenv te x t) (update e x v).

(** ** Bulk Updates *)

(** Update environment with a list of bindings *)
Fixpoint updates (e : env) (bindings : list (string * value)) : env :=
  match bindings with
  | [] => e
  | (x, v) :: rest => updates (update e x v) rest
  end.

(** ** Environment Equivalence *)

(** Two environments are equivalent on a set of variables *)
Definition env_equiv_on (vars : list string) (e1 e2 : env) : Prop :=
  forall x, In x vars -> lookup e1 x = lookup e2 x.

(** Reflexivity of environment equivalence *)
Lemma env_equiv_refl : forall vars e,
  env_equiv_on vars e e.
Proof.
  intros vars e x Hin. reflexivity.
Qed.

(** Symmetry of environment equivalence *)
Lemma env_equiv_sym : forall vars e1 e2,
  env_equiv_on vars e1 e2 ->
  env_equiv_on vars e2 e1.
Proof.
  intros vars e1 e2 H x Hin.
  symmetry. apply H. assumption.
Qed.

(** ** Examples *)

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
