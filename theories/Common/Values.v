(** * Values: Runtime Values for IEC 61131-3 ST

    This module defines runtime values and their relationship with types.
    It includes value constructors, type checking, and value operations.
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Bool.Bool.
Require Import STCompiler.Common.Types.

Open Scope Z_scope.
Open Scope string_scope.

(** ** Value Definitions *)

(** Runtime values *)
Inductive value : Type :=
  | VBool : bool -> value        (** Boolean value *)
  | VInt : Z -> value            (** Integer value *)
  | VReal : Q -> value           (** Real number value *)
  | VString : string -> value    (** String value *)
  | VVoid : value.               (** Void value (unit) *)

(** ** Value Type Relation *)

(** Type of a value *)
Definition typeof (v : value) : ty :=
  match v with
  | VBool _ => TyBool
  | VInt _ => TyInt
  | VReal _ => TyReal
  | VString _ => TyString
  | VVoid => TyVoid
  end.

(** Value has a type *)
Inductive has_type : value -> ty -> Prop :=
  | T_Bool : forall b, has_type (VBool b) TyBool
  | T_Int : forall n, has_type (VInt n) TyInt
  | T_Real : forall r, has_type (VReal r) TyReal
  | T_String : forall s, has_type (VString s) TyString
  | T_Void : has_type VVoid TyVoid.

(** ** Value Properties *)

(** Type checking is consistent with has_type *)
Lemma typeof_has_type : forall v,
  has_type v (typeof v).
Proof.
  intros v.
  destruct v; constructor.
Qed.

(** has_type is deterministic *)
Lemma has_type_deterministic : forall v t1 t2,
  has_type v t1 ->
  has_type v t2 ->
  t1 = t2.
Proof.
  intros v t1 t2 H1 H2.
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** ** Value Equality *)

(** Value equality (for same types) *)
Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VInt n1, VInt n2 => Z.eqb n1 n2
  | VReal r1, VReal r2 => Qeq_bool r1 r2
  | VString s1, VString s2 => String.eqb s1 s2
  | VVoid, VVoid => true
  | _, _ => false
  end.

(** ** Default Values *)

(** Default value for each type *)
Definition default_value (t : ty) : value :=
  match t with
  | TyBool => VBool false
  | TyInt => VInt 0
  | TyReal => VReal 0
  | TyString => VString ""
  | TyVoid => VVoid
  end.

Lemma default_value_has_type : forall t,
  has_type (default_value t) t.
Proof.
  intros t.
  destruct t; constructor.
Qed.

(** ** Value Coercion *)

(** Coerce a value to a target type *)
Definition coerce_value (v : value) (target : ty) : option value :=
  match v, target with
  | VInt n, TyReal => Some (VReal (inject_Z n))
  | v', t => if ty_eq_dec (typeof v') t then Some v' else None
  end.

(** For now, we admit this lemma - will prove properly later *)
Axiom coerce_value_preserves_type : forall v t v',
  coerce_value v t = Some v' ->
  has_type v' t.

(** ** Value Operations Support *)

(** Check if a value is truthy (for conditions) *)
Definition is_truthy (v : value) : option bool :=
  match v with
  | VBool b => Some b
  | _ => None
  end.

(** Convert value to string (for display) *)
Fixpoint value_to_string (v : value) : string :=
  match v with
  | VBool true => "TRUE"
  | VBool false => "FALSE"
  | VInt n => ""  (* Would need Z to string conversion *)
  | VReal r => ""  (* Would need Q to string conversion *)
  | VString s => s
  | VVoid => "VOID"
  end.

(** ** Examples *)

Example ex_bool_value : value := VBool true.
Example ex_int_value : value := VInt 42.
Example ex_real_value : value := VReal (1#2).

Example ex_typeof_bool : typeof (VBool true) = TyBool.
Proof. reflexivity. Qed.

Example ex_typeof_int : typeof (VInt 42) = TyInt.
Proof. reflexivity. Qed.

Example ex_has_type_bool : has_type (VBool false) TyBool.
Proof. constructor. Qed.

Example ex_has_type_int : has_type (VInt 10) TyInt.
Proof. constructor. Qed.

Example ex_default_bool : default_value TyBool = VBool false.
Proof. reflexivity. Qed.

Example ex_coerce_int_real : 
  coerce_value (VInt 5) TyReal = Some (VReal (inject_Z 5)).
Proof. reflexivity. Qed.

Example ex_value_eq_true : value_eqb (VInt 5) (VInt 5) = true.
Proof. reflexivity. Qed.

Example ex_value_eq_false : value_eqb (VInt 5) (VInt 3) = false.
Proof. reflexivity. Qed.
