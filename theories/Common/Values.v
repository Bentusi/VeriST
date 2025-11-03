(** * Values: IEC 61131-3 ST 的运行时值

    本模块定义运行时值及其与类型的关系。
    包括值构造器、类型检查和值操作。
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Bool.Bool.
Require Import STCompiler.Common.Types.

Open Scope Z_scope.
Open Scope string_scope.

(** ** 值定义 *)

(** 运行时值 *)
Inductive value : Type :=
  | VBool : bool -> value        (** 布尔值 *)
  | VInt : Z -> value            (** 整数值 *)
  | VReal : Q -> value           (** 实数值 *)
  | VString : string -> value    (** 字符串值 *)
  | VVoid : value.               (** 空值（单元） *)

(** ** 值类型关系 *)

(** 值的类型 *)
Definition typeof (v : value) : ty :=
  match v with
  | VBool _ => TyBool
  | VInt _ => TyInt
  | VReal _ => TyReal
  | VString _ => TyString
  | VVoid => TyVoid
  end.

(** 值具有类型 *)
Inductive has_type : value -> ty -> Prop :=
  | T_Bool : forall b, has_type (VBool b) TyBool
  | T_Int : forall n, has_type (VInt n) TyInt
  | T_Real : forall r, has_type (VReal r) TyReal
  | T_String : forall s, has_type (VString s) TyString
  | T_Void : has_type VVoid TyVoid.

(** ** 值属性 *)

(** 类型检查与 has_type 一致 *)
Lemma typeof_has_type : forall v,
  has_type v (typeof v).
Proof.
  intros v.
  destruct v; constructor.
Qed.

(** has_type 是确定性的 *)
Lemma has_type_deterministic : forall v t1 t2,
  has_type v t1 ->
  has_type v t2 ->
  t1 = t2.
Proof.
  intros v t1 t2 H1 H2.
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** ** 值相等性 *)

(** 值相等（对于相同类型） *)
Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VInt n1, VInt n2 => Z.eqb n1 n2
  | VReal r1, VReal r2 => Qeq_bool r1 r2
  | VString s1, VString s2 => String.eqb s1 s2
  | VVoid, VVoid => true
  | _, _ => false
  end.

(** ** 默认值 *)

(** 每种类型的默认值 *)
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

(** ** 值强制转换 *)

(** 将值强制转换为目标类型 *)
Definition coerce_value (v : value) (target : ty) : option value :=
  match v, target with
  | VInt n, TyReal => Some (VReal (inject_Z n))
  | v', t => if ty_eq_dec (typeof v') t then Some v' else None
  end.

(** 暂时承认此引理 - 后续会正确证明 *)
Axiom coerce_value_preserves_type : forall v t v',
  coerce_value v t = Some v' ->
  has_type v' t.

(** ** 值操作支持 *)

(** 检查值是否为真（用于条件） *)
Definition is_truthy (v : value) : option bool :=
  match v with
  | VBool b => Some b
  | _ => None
  end.

(** 将值转换为字符串（用于显示） *)
Definition value_to_string (v : value) : string :=
  match v with
  | VBool true => "TRUE"
  | VBool false => "FALSE"
  | VInt n => ""  (* 需要 Z 到字符串的转换 *)
  | VReal r => ""  (* 需要 Q 到字符串的转换 *)
  | VString s => s
  | VVoid => "VOID"
  end.

(** ** 示例 *)

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
