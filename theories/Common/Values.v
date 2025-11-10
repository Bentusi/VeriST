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

(** 质量位定义 ·*)
Inductive quality : Type :=
  | QGood : quality       (** 好质量 - 数据可信 *)
  | QBad : quality        (** 坏质量 - 数据不可信 *)
  | QUncertain : quality. (** 不确定质量 - 数据可疑 *)

(** 运行时值 *)
Inductive value : Type :=
  | VBool : bool -> value        (** 布尔值 *)
  | VInt : Z -> value            (** 整数值 *)
  | VReal : Q -> value           (** 实数值 *)
  | VQBool : bool -> quality -> value    (** 带质量位的布尔值 *)
  | VQInt : Z -> quality -> value        (** 带质量位的整数值 *)
  | VQReal : Q -> quality -> value       (** 带质量位的实数值 *)
  | VString : string -> value    (** 字符串值 *)
  | VVoid : value.               (** 空值（单元） *)

(** ** 值类型关系 *)

(** 值的类型 *)
Definition typeof (v : value) : ty :=
  match v with
  | VBool _ => TyBool
  | VInt _ => TyInt
  | VReal _ => TyReal
  | VQBool _ _ => TyQBool
  | VQInt _ _ => TyQInt
  | VQReal _ _ => TyQReal
  | VString _ => TyString
  | VVoid => TyVoid
  end.

(** 值具有类型 *)
Inductive has_type : value -> ty -> Prop :=
  | T_Bool : forall b, has_type (VBool b) TyBool
  | T_Int : forall n, has_type (VInt n) TyInt
  | T_Real : forall r, has_type (VReal r) TyReal
  | T_QBool : forall b q, has_type (VQBool b q) TyQBool
  | T_QInt : forall n q, has_type (VQInt n q) TyQInt
  | T_QReal : forall r q, has_type (VQReal r q) TyQReal
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

(** 质量位相等 *)
Definition quality_eqb (q1 q2 : quality) : bool :=
  match q1, q2 with
  | QGood, QGood => true
  | QBad, QBad => true
  | QUncertain, QUncertain => true
  | _, _ => false
  end.

(** 值相等（对于相同类型） *)
Definition value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VInt n1, VInt n2 => Z.eqb n1 n2
  | VReal r1, VReal r2 => Qeq_bool r1 r2
  | VQBool b1 q1, VQBool b2 q2 => andb (Bool.eqb b1 b2) (quality_eqb q1 q2)
  | VQInt n1 q1, VQInt n2 q2 => andb (Z.eqb n1 n2) (quality_eqb q1 q2)
  | VQReal r1 q1, VQReal r2 q2 => andb (Qeq_bool r1 r2) (quality_eqb q1 q2)
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
  | TyQBool => VQBool false QGood
  | TyQInt => VQInt 0 QGood
  | TyQReal => VQReal 0 QGood
  | TyString => VString ""
  | TyVoid => VVoid
  | TyArray _ _ _ => VVoid  (* 数组类型暂未实现默认值，返回占位符 *)
  end.

(** ** 值强制转换 *)

(** 将值强制转换为目标类型 *)
Definition coerce_value (v : value) (target : ty) : option value :=
  match v, target with
  (* 数值类型提升 *)
  | VInt n, TyReal => Some (VReal (inject_Z n))
  | VQInt n q, TyQReal => Some (VQReal (inject_Z n) q)
  
  (* 普通类型到带质量位类型 *)
  | VBool b, TyQBool => Some (VQBool b QGood)
  | VInt n, TyQInt => Some (VQInt n QGood)
  | VReal r, TyQReal => Some (VQReal r QGood)
  
  (* 组合转换：INT -> QREAL *)
  | VInt n, TyQReal => Some (VQReal (inject_Z n) QGood)
  
  (* 相同类型 *)
  | v', t => if ty_eq_dec (typeof v') t then Some v' else None
  end.

(** 暂时承认此引理 - 后续会正确证明 *)
Axiom coerce_value_preserves_type : forall v t v',
  coerce_value v t = Some v' ->
  has_type v' t.

(** ** 值操作支持 *)

(** 获取值的质量位 *)
Definition get_quality (v : value) : option quality :=
  match v with
  | VQBool _ q => Some q
  | VQInt _ q => Some q
  | VQReal _ q => Some q
  | _ => None  (* 普通值没有质量位 *)
  end.

(** 设置值的质量位 *)
Definition set_quality (v : value) (q : quality) : value :=
  match v with
  | VBool b => VQBool b q
  | VInt n => VQInt n q
  | VReal r => VQReal r q
  | VQBool b _ => VQBool b q
  | VQInt n _ => VQInt n q
  | VQReal r _ => VQReal r q
  | _ => v  (* 不支持质量位的类型保持不变 *)
  end.

(** 获取值的基础数据（去掉质量位） *)
Definition get_base_value (v : value) : value :=
  match v with
  | VQBool b _ => VBool b
  | VQInt n _ => VInt n
  | VQReal r _ => VReal r
  | _ => v
  end.

(** 检查值是否为真（用于条件） *)
Definition is_truthy (v : value) : option bool :=
  match v with
  | VBool b => Some b
  | VQBool b _ => Some b  (* 带质量位的布尔值也可用于条件 *)
  | _ => None
  end.

(** 将值转换为字符串（用于显示） *)
Definition value_to_string (v : value) : string :=
  match v with
  | VBool true => "TRUE"
  | VBool false => "FALSE"
  | VInt n => ""  (* 需要 Z 到字符串的转换 *)
  | VReal r => ""  (* 需要 Q 到字符串的转换 *)
  | VQBool true QGood => "TRUE(GOOD)"
  | VQBool false QGood => "FALSE(GOOD)"
  | VQBool true QBad => "TRUE(BAD)"
  | VQBool false QBad => "FALSE(BAD)"
  | VQBool true QUncertain => "TRUE(UNCERTAIN)"
  | VQBool false QUncertain => "FALSE(UNCERTAIN)"
  | VQInt n q => ""  (* 需要完整实现 *)
  | VQReal r q => ""  (* 需要完整实现 *)
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

(** ** 带质量位值的示例 *)

(** 带质量位的整数值 *)
Example ex_qint_value : value := VQInt 42 QGood.

(** 带质量位的布尔值 *)
Example ex_qbool_value : value := VQBool true QBad.

(** QINT 值的类型 *)
Example ex_typeof_qint : typeof (VQInt 42 QGood) = TyQInt.
Proof. reflexivity. Qed.

(** QINT 值具有 QINT 类型 *)
Example ex_has_type_qint : has_type (VQInt 10 QGood) TyQInt.
Proof. constructor. Qed.

(** 获取 QINT 值的质量位 *)
Example ex_get_quality : get_quality (VQInt 42 QBad) = Some QBad.
Proof. reflexivity. Qed.

(** 设置值的质量位 *)
Example ex_set_quality : set_quality (VInt 42) QBad = VQInt 42 QBad.
Proof. reflexivity. Qed.

(** 获取带质量位值的基础值 *)
Example ex_get_base_value : get_base_value (VQInt 42 QGood) = VInt 42.
Proof. reflexivity. Qed.

(** INT 可以强制转换为 QINT *)
Example ex_coerce_int_to_qint : 
  coerce_value (VInt 42) TyQInt = Some (VQInt 42 QGood).
Proof. reflexivity. Qed.

(** QINT 的默认值 *)
Example ex_default_qint : default_value TyQInt = VQInt 0 QGood.
Proof. reflexivity. Qed.

Example ex_coerce_int_real :
  coerce_value (VInt 5) TyReal = Some (VReal (inject_Z 5)).
Proof. reflexivity. Qed.

Example ex_value_eq_true : value_eqb (VInt 5) (VInt 5) = true.
Proof. reflexivity. Qed.

Example ex_value_eq_false : value_eqb (VInt 5) (VInt 3) = false.
Proof. reflexivity. Qed.
