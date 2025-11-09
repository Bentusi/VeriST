(** * Types: IEC 61131-3 ST 类型系统

  本模块定义了 IEC 61131-3 结构化文本语言的类型系统。
  包括基本数据类型、类型操作和类型安全属性。
  
  © 2024 JIANG Wei <jiangwey@outlook.com> 
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.
Open Scope string_scope.

(** ** 基本数据类型 *)
(** IEC 61131-3 ST 语言的类型 *)
Inductive ty : Type :=
  | TyBool : ty          (** 布尔类型 *)
  | TyInt : ty           (** 整数类型 64bit *)
  | TyReal : ty          (** 实数/浮点数类型 64bit *)
  | TyQBool : ty         (** 带质量位的布尔类型 *)
  | TyQInt : ty          (** 带质量位的整数类型 64bit *)
  | TyQReal : ty        (** 带质量位的实数/浮点数类型 64bit *)
  | TyString : ty        (** 字符串类型 *)
  | TyVoid : ty.         (** 空类型 (用于过程) *)

(** 类型相等性是可判定的 *)
(** 1. 类型检查需要判断两个类型是否相等
    2. 在类型强制转换 (can_coerce) 中使用了 ty_eq_dec
    3. 使得类型相等性判断可以在程序中直接使用
    4. 提供了构造性的判定算法,而不仅仅是逻辑上的存在性
*)
Theorem ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(** 布尔类型相等性判断 *)
Definition ty_eqb (t1 t2 : ty) : bool :=
  match t1, t2 with
  | TyBool, TyBool => true
  | TyInt, TyInt => true
  | TyReal, TyReal => true
  | TyQBool, TyQBool => true
  | TyQInt, TyQInt => true
  | TyQReal, TyQReal => true
  | TyString, TyString => true
  | TyVoid, TyVoid => true
  | _, _ => false
  end.

(** 布尔类型相等性与逻辑相等性等价 *)
Lemma ty_eqb_eq : forall t1 t2,
  ty_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2.
  split; intros H.
  - destruct t1, t2; simpl in *; try discriminate; reflexivity.
  - subst. destruct t2; reflexivity.
Qed.

(** ** 类型操作 **)

(** 类型的字符串表示 (用于调试/错误消息) *)
Definition ty_to_string (t : ty) : string :=
  match t with
  | TyBool => "BOOL"
  | TyInt => "INT"
  | TyReal => "REAL"
  | TyQBool => "QBOOL"
  | TyQInt => "QINT"
  | TyQReal => "QREAL"
  | TyString => "STRING"
  | TyVoid => "VOID"
  end.

(** 检查类型是否为数值类型 *)
Definition is_numeric_type (t : ty) : bool :=
  match t with
  | TyInt | TyReal | TyQInt | TyQReal => true
  | _ => false
  end.

(** 检查类型是否可比较 *)
Definition is_comparable_type (t : ty) : bool :=
  match t with
  | TyBool | TyInt | TyReal | TyQBool | TyQInt | TyQReal => true
  | _ => false
  end.

(** 检查类型是否带有质量位 *)
Definition has_quality (t : ty) : bool :=
  match t with
  | TyQBool | TyQInt | TyQReal => true
  | _ => false
  end.

(** 获取类型的基础类型（去掉质量位） *)
Definition base_type (t : ty) : ty :=
  match t with
  | TyQBool => TyBool
  | TyQInt => TyInt
  | TyQReal => TyReal
  | _ => t
  end.

(** 为类型添加质量位 *)
Definition add_quality (t : ty) : ty :=
  match t with
  | TyBool => TyQBool
  | TyInt => TyQInt
  | TyReal => TyQReal
  | _ => t  (* 已经有质量位或不支持质量位 *)
  end.

(** ** 类型兼容性 *)

(** 类型强制转换/提升规则 *)
(** INT 可以提升为 REAL，普通类型可以提升为带质量位类型 *)
Definition can_coerce (from to : ty) : bool :=
  match from, to with
  (* 数值类型提升 *)
  | TyInt, TyReal => true
  | TyQInt, TyQReal => true
  (* 普通类型到带质量位类型的提升 *)
  | TyBool, TyQBool => true
  | TyInt, TyQInt => true
  | TyReal, TyQReal => true
  (* 同时提升：普通类型 -> 带质量位的更高精度类型 *)
  | TyInt, TyQReal => true
  (* 相同类型 *)
  | _, _ => if ty_eq_dec from to then true else false
  end.

(** 为二元运算进行类型转换 *)
Definition common_type (t1 t2 : ty) : option ty :=
  match t1, t2 with
  (* 普通类型 *)
  | TyReal, TyInt | TyInt, TyReal => Some TyReal
  | TyInt, TyInt => Some TyInt
  | TyReal, TyReal => Some TyReal
  | TyBool, TyBool => Some TyBool
  | TyString, TyString => Some TyString
  
  (* 带质量位类型 *)
  | TyQReal, TyQInt | TyQInt, TyQReal => Some TyQReal
  | TyQInt, TyQInt => Some TyQInt
  | TyQReal, TyQReal => Some TyQReal
  | TyQBool, TyQBool => Some TyQBool
  
  (* 混合：普通类型与带质量位类型 -> 带质量位类型 *)
  | TyInt, TyQInt | TyQInt, TyInt => Some TyQInt
  | TyReal, TyQReal | TyQReal, TyReal => Some TyQReal
  | TyBool, TyQBool | TyQBool, TyBool => Some TyQBool
  | TyInt, TyQReal | TyQReal, TyInt => Some TyQReal
  | TyReal, TyQInt | TyQInt, TyReal => Some TyQReal
  
  | _, _ => None
  end.

(** ** 类型属性 *)

(** 类型强制转换的自反性，任何类型都可以转换为自己 *)
Lemma can_coerce_refl : forall t,
  can_coerce t t = true.
Proof.
  intros t.
  unfold can_coerce.
  destruct t; simpl; try reflexivity.
  all: destruct (ty_eq_dec _ _); [reflexivity | exfalso; apply n; reflexivity].
Qed.

(** 传递性证明，较为复杂 *)
Lemma can_coerce_trans : forall t1 t2 t3,
  can_coerce t1 t2 = true ->
  can_coerce t2 t3 = true ->
  can_coerce t1 t3 = true.
Proof.
  intros t1 t2 t3 H12 H23.
  destruct t1, t2, t3; simpl in *; try discriminate; try reflexivity.
  all: repeat (
    match goal with
    | H : (if ty_eq_dec ?x ?y then _ else _) = true |- _ =>
        destruct (ty_eq_dec x y); subst; simpl in *; try discriminate
    end).
  all: repeat (
    match goal with
    | |- context [ty_eq_dec ?x ?y] =>
        destruct (ty_eq_dec x y); subst; simpl; try reflexivity; try discriminate
    end).
  all: try reflexivity.
Qed.

(** 公共类型具有对称性 *)
Lemma common_type_sym : forall t1 t2 t,
  common_type t1 t2 = Some t ->
  common_type t2 t1 = Some t.
Proof.
  intros t1 t2 t H.
  destruct t1, t2; simpl in *; inversion H; reflexivity.
Qed.

(** 示例 *)
(** 整数类型示例 *)
Example ex_int_type : ty := TyInt.
(** 布尔类型示例 *)
Example ex_bool_type : ty := TyBool.

(** 类型相等示例 *)
Lemma ex_type_eq : {TyInt = TyInt} + {TyInt <> TyInt}.
Proof. left. reflexivity. Qed.

(** 类型不相等示例 *)
Lemma ex_type_neq : {TyInt = TyBool} + {TyInt <> TyBool}.
Proof. right. discriminate. Qed.

(** 整数是数值类型 *)
Lemma ex_numeric_int : is_numeric_type TyInt = true.
Proof. reflexivity. Qed.

(** 布尔不是数值类型 *)
Lemma ex_numeric_bool : is_numeric_type TyBool = false.
Proof. reflexivity. Qed.

(** 整数可强制转换为实数 *)
Lemma ex_coerce_int_real : can_coerce TyInt TyReal = true.
Proof. reflexivity. Qed.

(** 整数和实数的公共类型是实数 *)
Lemma ex_common_type : common_type TyInt TyReal = Some TyReal.
Proof. reflexivity. Qed.

(** ** 带质量位类型示例 *)

(** 带质量位的整数类型示例 *)
Example ex_qint_type : ty := TyQInt.

(** QINT 是数值类型 *)
Lemma ex_numeric_qint : is_numeric_type TyQInt = true.
Proof. reflexivity. Qed.

(** QINT 具有质量位 *)
Lemma ex_has_quality_qint : has_quality TyQInt = true.
Proof. reflexivity. Qed.

(** QINT 的基础类型是 INT *)
Lemma ex_base_type_qint : base_type TyQInt = TyInt.
Proof. reflexivity. Qed.

(** INT 可以强制转换为 QINT *)
Lemma ex_coerce_int_qint : can_coerce TyInt TyQInt = true.
Proof. reflexivity. Qed.

(** QINT 可以强制转换为 QREAL *)
Lemma ex_coerce_qint_qreal : can_coerce TyQInt TyQReal = true.
Proof. reflexivity. Qed.

(** INT 和 QINT 的公共类型是 QINT *)
Lemma ex_common_type_int_qint : common_type TyInt TyQInt = Some TyQInt.
Proof. reflexivity. Qed.

(** QINT 和 QREAL 的公共类型是 QREAL *)
Lemma ex_common_type_qint_qreal : common_type TyQInt TyQReal = Some TyQReal.
Proof. reflexivity. Qed.

(** 为 INT 添加质量位得到 QINT *)
Lemma ex_add_quality_int : add_quality TyInt = TyQInt.
Proof. reflexivity. Qed.
