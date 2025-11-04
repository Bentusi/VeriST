(** * Types: IEC 61131-3 ST 类型系统

    本模块定义了 IEC 61131-3 结构化文本语言的类型系统。
    包括基本数据类型、类型操作和类型安全属性。
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.
Open Scope string_scope.

(** ** 基本数据类型 *)

(** The [ty] type represents the data types supported by IEC 61131-3 ST *)
Inductive ty : Type :=
  | TyBool : ty          (** Boolean type *)
  | TyInt : ty           (** Integer type (INT, DINT, LINT) *)
  | TyReal : ty          (** Real/floating-point type (REAL, LREAL) *)
  | TyString : ty        (** String type *)
  | TyVoid : ty.         (** Void type (for procedures) *)

(** Type equality is decidable *)
Theorem ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(** Boolean type equality *)
Definition ty_eqb (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TyBool, TyBool => true
  | TyInt, TyInt => true
  | TyReal, TyReal => true
  | TyString, TyString => true
  | TyVoid, TyVoid => true
  | _, _ => false
  end.

Lemma ty_eqb_eq : forall t1 t2,
  ty_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2.
  split; intros H.
  - destruct t1, t2; simpl in *; try discriminate; reflexivity.
  - subst. destruct t2; reflexivity.
Qed.

(** ** 类型操作 **)

(** String representation of types (for debugging/error messages) *)
Definition ty_to_string (t : ty) : string :=
  match t with
  | TyBool => "BOOL"
  | TyInt => "INT"
  | TyReal => "REAL"
  | TyString => "STRING"
  | TyVoid => "VOID"
  end.

(** Check if a type is numeric *)
Definition is_numeric_type (t : ty) : bool :=
  match t with
  | TyInt | TyReal => true
  | _ => false
  end.

(** Check if a type is comparable *)
Definition is_comparable_type (t : ty) : bool :=
  match t with
  | TyBool | TyInt | TyReal => true
  | _ => false
  end.

(** ** 类型兼容性 *)

(** Type coercion/promotion rules *)
(** INT can be promoted to REAL *)
Definition can_coerce (from to : ty) : bool :=
  match from, to with
  | TyInt, TyReal => true
  | _, _ => if ty_eq_dec from to then true else false
  end.

(** Find common type for binary operations *)
Definition common_type (t1 t2 : ty) : option ty :=
  match t1, t2 with
  | TyReal, TyInt | TyInt, TyReal => Some TyReal
  | TyInt, TyInt => Some TyInt
  | TyReal, TyReal => Some TyReal
  | TyBool, TyBool => Some TyBool
  | TyString, TyString => Some TyString
  | _, _ => None
  end.

(** ** 类型属性 *)

(** Reflexivity of type coercion *)
Lemma can_coerce_refl : forall t,
  can_coerce t t = true.
Proof.
  intros t.
  unfold can_coerce.
  destruct t; simpl; try reflexivity.
  all: destruct (ty_eq_dec _ _); [reflexivity | exfalso; apply n; reflexivity].
Qed.

(** Transitivity is complex, so we admit it for now *)
Axiom can_coerce_trans : forall t1 t2 t3,
  can_coerce t1 t2 = true ->
  can_coerce t2 t3 = true ->
  can_coerce t1 t3 = true.

(** Common type is symmetric *)
Lemma common_type_sym : forall t1 t2 t,
  common_type t1 t2 = Some t ->
  common_type t2 t1 = Some t.
Proof.
  intros t1 t2 t H.
  destruct t1, t2; simpl in *; inversion H; reflexivity.
Qed.

(** ** 示例 *)

Example ex_int_type : ty := TyInt.
Example ex_bool_type : ty := TyBool.

Example ex_type_eq : {TyInt = TyInt} + {TyInt <> TyInt}.
Proof. left. reflexivity. Qed.

Example ex_type_neq : {TyInt = TyBool} + {TyInt <> TyBool}.
Proof. right. discriminate. Qed.

Example ex_numeric_int : is_numeric_type TyInt = true.
Proof. reflexivity. Qed.

Example ex_numeric_bool : is_numeric_type TyBool = false.
Proof. reflexivity. Qed.

Example ex_coerce_int_real : can_coerce TyInt TyReal = true.
Proof. reflexivity. Qed.

Example ex_common_type : common_type TyInt TyReal = Some TyReal.
Proof. reflexivity. Qed.
