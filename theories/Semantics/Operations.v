(** * Operations: Semantic Operations for IEC 61131-3 ST

    本模块定义 the semantic operations for evaluating
    expressions and executing statements, 包括 arithmetic,
    comparison, and logical operations.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.

Open Scope Z_scope.

(** ** Binary Operations *)

(** Arithmetic operations on integers *)
Definition eval_int_binop (op : Z -> Z -> Z) (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 => Some (VInt (op n1 n2))
  | _, _ => None
  end.

(** Arithmetic operations on reals *)
Definition eval_real_binop (op : Q -> Q -> Q) (v1 v2 : value) : option value :=
  match v1, v2 with
  | VReal r1, VReal r2 => Some (VReal (op r1 r2))
  | VInt n1, VReal r2 => Some (VReal (op (inject_Z n1) r2))
  | VReal r1, VInt n2 => Some (VReal (op r1 (inject_Z n2)))
  | _, _ => None
  end.

(** Mixed arithmetic - promote to real *)
Definition eval_arith_binop (op_int : Z -> Z -> Z) (op_real : Q -> Q -> Q)
                            (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 => Some (VInt (op_int n1 n2))
  | VReal r1, VReal r2 => Some (VReal (op_real r1 r2))
  | VInt n1, VReal r2 => Some (VReal (op_real (inject_Z n1) r2))
  | VReal r1, VInt n2 => Some (VReal (op_real r1 (inject_Z n2)))
  | _, _ => None
  end.

(** Integer comparison *)
Definition eval_int_comp (op : Z -> Z -> bool) (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 => Some (VBool (op n1 n2))
  | _, _ => None
  end.

(** Real comparison *)
Definition eval_real_comp (op : Q -> Q -> bool) (v1 v2 : value) : option value :=
  match v1, v2 with
  | VReal r1, VReal r2 => Some (VBool (op r1 r2))
  | VInt n1, VReal r2 => Some (VBool (op (inject_Z n1) r2))
  | VReal r1, VInt n2 => Some (VBool (op r1 (inject_Z n2)))
  | _, _ => None
  end.

(** Mixed comparison *)
Definition eval_comp_binop (op_int : Z -> Z -> bool) (op_real : Q -> Q -> bool)
                           (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 => Some (VBool (op_int n1 n2))
  | VReal r1, VReal r2 => Some (VBool (op_real r1 r2))
  | VInt n1, VReal r2 => Some (VBool (op_real (inject_Z n1) r2))
  | VReal r1, VInt n2 => Some (VBool (op_real r1 (inject_Z n2)))
  | _, _ => None
  end.

(** Logical operations *)
Definition eval_bool_binop (op : bool -> bool -> bool) (v1 v2 : value) : option value :=
  match v1, v2 with
  | VBool b1, VBool b2 => Some (VBool (op b1 b2))
  | _, _ => None
  end.

(** ** Concrete Binary Operations *)

(** Addition *)
Definition eval_add (v1 v2 : value) : option value :=
  eval_arith_binop Z.add Qplus v1 v2.

(** Subtraction *)
Definition eval_sub (v1 v2 : value) : option value :=
  eval_arith_binop Z.sub Qminus v1 v2.

(** 乘法 *)
Definition eval_mul (v1 v2 : value) : option value :=
  eval_arith_binop Z.mul Qmult v1 v2.

(** Division *)
Definition eval_div (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 =>
      if Z.eqb n2 0 then None  (* Division by zero *)
      else Some (VInt (Z.div n1 n2))
  | VReal r1, VReal r2 =>
      if Qeq_bool r2 0 then None
      else Some (VReal (Qdiv r1 r2))
  | VInt n1, VReal r2 =>
      if Qeq_bool r2 0 then None
      else Some (VReal (Qdiv (inject_Z n1) r2))
  | VReal r1, VInt n2 =>
      if Z.eqb n2 0 then None
      else Some (VReal (Qdiv r1 (inject_Z n2)))
  | _, _ => None
  end.

(** Modulo *)
Definition eval_mod (v1 v2 : value) : option value :=
  match v1, v2 with
  | VInt n1, VInt n2 =>
      if Z.eqb n2 0 then None
      else Some (VInt (Z.modulo n1 n2))
  | _, _ => None
  end.

(** Equal *)
Definition eval_eq (v1 v2 : value) : option value :=
  eval_comp_binop Z.eqb Qeq_bool v1 v2.

(** Not equal *)
Definition eval_ne (v1 v2 : value) : option value :=
  match eval_eq v1 v2 with
  | Some (VBool b) => Some (VBool (negb b))
  | _ => None
  end.

(** Less than *)
Definition eval_lt (v1 v2 : value) : option value :=
  eval_comp_binop Z.ltb (fun r1 r2 => negb (Qle_bool r2 r1)) v1 v2.

(** Less or equal *)
Definition eval_le (v1 v2 : value) : option value :=
  eval_comp_binop Z.leb Qle_bool v1 v2.

(** Greater than *)
Definition eval_gt (v1 v2 : value) : option value :=
  eval_comp_binop Z.gtb (fun r1 r2 => negb (Qle_bool r1 r2)) v1 v2.

(** Greater or equal *)
Definition eval_ge (v1 v2 : value) : option value :=
  eval_comp_binop Z.geb (fun r1 r2 => negb (Qle_bool r2 r1)) v1 v2.

(** 逻辑与 AND *)
Definition eval_and (v1 v2 : value) : option value :=
  eval_bool_binop andb v1 v2.

(** 逻辑或 OR *)
Definition eval_or (v1 v2 : value) : option value :=
  eval_bool_binop orb v1 v2.

(** ** Unary Operations *)

(** Negation *)
Definition eval_neg (v : value) : option value :=
  match v with
  | VInt n => Some (VInt (Z.opp n))
  | VReal r => Some (VReal (Qopp r))
  | _ => None
  end.

(** 逻辑非 NOT *)
Definition eval_not (v : value) : option value :=
  match v with
  | VBool b => Some (VBool (negb b))
  | _ => None
  end.

(** ** Properties *)

(** 加法交换律 *)
Lemma eval_add_comm_int : forall n1 n2,
  eval_add (VInt n1) (VInt n2) = eval_add (VInt n2) (VInt n1).
Proof.
  intros n1 n2.
  unfold eval_add, eval_arith_binop.
  simpl.
  f_equal. f_equal.
  apply Z.add_comm.
Qed.

(** 取负的对合性 *)
Lemma eval_neg_involutive : forall n,
  eval_neg (VInt n) = Some (VInt (Z.opp n)) ->
  eval_neg (VInt (Z.opp n)) = Some (VInt n).
Proof.
  intros n H.
  unfold eval_neg in *.
  simpl in *.
  f_equal. f_equal.
  apply Z.opp_involutive.
Qed.

(** 逻辑非的对合性 *)
Lemma eval_not_involutive : forall b,
  eval_not (VBool b) = Some (VBool (negb b)) ->
  eval_not (VBool (negb b)) = Some (VBool b).
Proof.
  intros b H.
  unfold eval_not in *.
  simpl in *.
  f_equal. f_equal.
  apply negb_involutive.
Qed.

(** 除零检查 *)
Lemma eval_div_zero_int : forall n,
  eval_div (VInt n) (VInt 0) = None.
Proof.
  intros n.
  unfold eval_div.
  simpl.
  reflexivity.
Qed.

(** ** 额外的有用属性 *)

(** 这些额外属性在后续开发中将被证明 *)

(** 逻辑与的性质 *)
Lemma eval_and_true_l : forall b,
  eval_and (VBool true) (VBool b) = Some (VBool b).
Proof.
  intros b.
  unfold eval_and, eval_bool_binop.
  destruct b; reflexivity.
Qed.

Lemma eval_and_false_l : forall b,
  eval_and (VBool false) (VBool b) = Some (VBool false).
Proof.
  intros b.
  unfold eval_and, eval_bool_binop.
  destruct b; reflexivity.
Qed.

(** 逻辑或的性质 *)
Lemma eval_or_true_l : forall b,
  eval_or (VBool true) (VBool b) = Some (VBool true).
Proof.
  intros b.
  unfold eval_or, eval_bool_binop.
  destruct b; reflexivity.
Qed.

Lemma eval_or_false_l : forall b,
  eval_or (VBool false) (VBool b) = Some (VBool b).
Proof.
  intros b.
  unfold eval_or, eval_bool_binop.
  destruct b; reflexivity.
Qed.

(** ** 示例 *)

Example ex_add_int : eval_add (VInt 5) (VInt 3) = Some (VInt 8).
Proof. reflexivity. Qed.

Example ex_sub_int : eval_sub (VInt 10) (VInt 3) = Some (VInt 7).
Proof. reflexivity. Qed.

Example ex_mul_int : eval_mul (VInt 4) (VInt 5) = Some (VInt 20).
Proof. reflexivity. Qed.

Example ex_div_int : eval_div (VInt 10) (VInt 2) = Some (VInt 5).
Proof. reflexivity. Qed.

Example ex_div_zero : eval_div (VInt 10) (VInt 0) = None.
Proof. reflexivity. Qed.

Example ex_eq_true : eval_eq (VInt 5) (VInt 5) = Some (VBool true).
Proof. reflexivity. Qed.

Example ex_eq_false : eval_eq (VInt 5) (VInt 3) = Some (VBool false).
Proof. reflexivity. Qed.

Example ex_lt_true : eval_lt (VInt 3) (VInt 5) = Some (VBool true).
Proof. reflexivity. Qed.

Example ex_lt_false : eval_lt (VInt 5) (VInt 3) = Some (VBool false).
Proof. reflexivity. Qed.

Example ex_and_true : eval_and (VBool true) (VBool true) = Some (VBool true).
Proof. reflexivity. Qed.

Example ex_and_false : eval_and (VBool true) (VBool false) = Some (VBool false).
Proof. reflexivity. Qed.

Example ex_neg_int : eval_neg (VInt 5) = Some (VInt (-5)).
Proof. reflexivity. Qed.

Example ex_not_bool : eval_not (VBool true) = Some (VBool false).
Proof. reflexivity. Qed.
