(** * AST: IEC 61131-3 ST 的抽象语法树

    本模块定义 IEC 61131-3 结构化文本语言的抽象语法树，
    包括表达式、语句、函数和程序。

    © 2024 JIANG Wei <jiangwey@outlook.com> 
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** 运算符 *)

(** 二元运算符 *)
Inductive binop : Type :=
  (* 算术运算符 *)
  | OpAdd : binop      (** 加法 + *)
  | OpSub : binop      (** 减法 - *)
  | OpMul : binop      (** 乘法 * *)
  | OpDiv : binop      (** 除法 / *)
  | OpMod : binop      (** 取模 MOD *)
  (* 比较运算符 *)
  | OpEq : binop       (** 等于 = *)
  | OpNe : binop       (** 不等于 <> *)
  | OpLt : binop       (** 小于 < *)
  | OpLe : binop       (** 小于等于 <= *)
  | OpGt : binop       (** 大于 > *)
  | OpGe : binop       (** 大于等于 >= *)
  (* 逻辑运算符 *)
  | OpAnd : binop      (** 逻辑与 AND *)
  | OpOr : binop.      (** 逻辑或 OR *)

(** 一元运算符 *)
Inductive unop : Type :=
  | OpNeg : unop       (** 取负 - *)
  | OpNot : unop.      (** 逻辑非 NOT *)

(** ** 表达式 *)

(** 表达式 *)
Inductive expr : Type :=
  | EConst : value -> expr                      (** 常量 *)
  | EVar : string -> expr                       (** 变量引用 *)
  | EBinop : binop -> expr -> expr -> expr      (** 二元运算 *)
  | EUnop : unop -> expr -> expr                (** 一元运算 *)
  | ECall : string -> list expr -> expr.        (** 函数调用 *)

(** ** 语句 *)

(** 语句 *)
Inductive stmt : Type :=
  | SSkip : stmt                                (** 空语句 *)
  | SAssign : string -> expr -> stmt            (** 赋值 x := e *)
  | SSeq : stmt -> stmt -> stmt                 (** 顺序 s1; s2 *)
  | SIf : expr -> stmt -> stmt -> stmt          (** 条件语句 *)
  | SWhile : expr -> stmt -> stmt               (** While 循环 *)
  | SFor : string -> expr -> expr -> stmt -> stmt  (** For 循环 *)
  | SCase : expr -> list (expr * stmt) -> stmt -> stmt  (** Case 语句 *)
  | SReturn : option expr -> stmt               (** 返回语句 *)
  | SCall : string -> list expr -> stmt.        (** 过程调用 *)

(** ** 变量声明 *)

(** 变量声明 *)
Record var_decl : Type := mkVarDecl {
  vd_name : string;
  vd_type : ty;
  vd_init : option value
}.

(** ** 参数声明 *)

(** 参数类型 *)
Inductive param_kind : Type :=
  | PKInput : param_kind       (** 输入参数 VAR_INPUT *)
  | PKOutput : param_kind      (** 输出参数 VAR_OUTPUT *)
  | PKInOut : param_kind.      (** 输入输出参数 VAR_IN_OUT *)

(** 参数声明 *)
Record param_decl : Type := mkParamDecl {
  pd_kind : param_kind;
  pd_name : string;
  pd_type : ty
}.

(** ** 函数定义 *)

(** 函数定义 *)
Record function_def : Type := mkFunctionDef {
  fn_name : string;
  fn_params : list param_decl;
  fn_return_type : ty;
  fn_vars : list var_decl;
  fn_body : stmt
}.

(** ** 程序定义 *)

(** 程序定义 *)
Record program_def : Type := mkProgramDef {
  pg_name : string;
  pg_vars : list var_decl;
  pg_body : stmt
}.

(** ** 编译单元 *)

(** 完整编译单元 *)
Record compilation_unit : Type := mkCompilationUnit {
  cu_functions : list function_def;
  cu_program : program_def
}.

(** ** 辅助函数 *)

(** 从参数列表获取参数名 *)
Fixpoint param_names (params : list param_decl) : list string :=
  match params with
  | [] => []
  | p :: ps => pd_name p :: param_names ps
  end.

(** 从变量列表获取变量名 *)
Fixpoint var_names (vars : list var_decl) : list string :=
  match vars with
  | [] => []
  | v :: vs => vd_name v :: var_names vs
  end.

(** 计算参数数量 *)
Definition param_count (params : list param_decl) : nat :=
  length params.

(** ** 表达式属性 *)

(** 表达式大小（用于归纳） *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EConst _ => 1
  | EVar _ => 1
  | EBinop _ e1 e2 => S (expr_size e1 + expr_size e2)
  | EUnop _ e1 => S (expr_size e1)
  | ECall _ args => S (length args)  (* 暂时简化 *)
  end.

(** 语句大小（用于归纳） *)
Fixpoint stmt_size (s : stmt) : nat :=
  match s with
  | SSkip => 1
  | SAssign _ e => S (expr_size e)
  | SSeq s1 s2 => S (stmt_size s1 + stmt_size s2)
  | SIf e s1 s2 => S (expr_size e + stmt_size s1 + stmt_size s2)
  | SWhile e s => S (expr_size e + stmt_size s)
  | SFor _ e1 e2 s => S (expr_size e1 + expr_size e2 + stmt_size s)
  | SCase e cases default => S (expr_size e + length cases + stmt_size default)
  | SReturn None => 1
  | SReturn (Some e) => S (expr_size e)
  | SCall _ args => S (length args)  (* 暂时简化 *)
  end.

(** ** 示例 *)

(** 示例: 5 + 3 *)
Example ex_add_expr : expr :=
  EBinop OpAdd (EConst (VInt 5%Z)) (EConst (VInt 3%Z)).

(** 示例: x := 10 *)
Example ex_assign_stmt : stmt :=
  SAssign "x" (EConst (VInt 10%Z)).

(** 示例: IF x > 0 THEN y := 1 ELSE y := 0 END_IF *)
Example ex_if_stmt : stmt :=
  SIf (EBinop OpGt (EVar "x") (EConst (VInt 0%Z)))
      (SAssign "y" (EConst (VInt 1%Z)))
      (SAssign "y" (EConst (VInt 0%Z))).

(** 示例: WHILE x > 0 DO x := x - 1 END_WHILE *)
Example ex_while_stmt : stmt :=
  SWhile (EBinop OpGt (EVar "x") (EConst (VInt 0%Z)))
         (SAssign "x" (EBinop OpSub (EVar "x") (EConst (VInt 1%Z)))).

(** 示例: FOR i := 1 TO 10 DO sum := sum + i END_FOR *)
Example ex_for_stmt : stmt :=
  SFor "i" (EConst (VInt 1%Z)) (EConst (VInt 10%Z))
       (SAssign "sum" (EBinop OpAdd (EVar "sum") (EVar "i"))).

(** 示例变量声明 *)
Example ex_var_decl : var_decl :=
  mkVarDecl "counter" TyInt (Some (VInt 0%Z)).

(** 示例参数声明 *)
Example ex_param_decl : param_decl :=
  mkParamDecl PKInput "value" TyInt.

(** 示例函数: Add(a, b : INT) : INT *)
Example ex_function : function_def :=
  mkFunctionDef "Add"
    [mkParamDecl PKInput "a" TyInt; mkParamDecl PKInput "b" TyInt]
    TyInt
    []
    (SReturn (Some (EBinop OpAdd (EVar "a") (EVar "b")))).

(** 示例程序 *)
Example ex_program : program_def :=
  mkProgramDef "SimpleCalc"
    [mkVarDecl "x" TyInt (Some (VInt 0%Z));
     mkVarDecl "y" TyInt (Some (VInt 0%Z))]
    (SSeq (SAssign "x" (EConst (VInt 5%Z)))
          (SAssign "y" (EBinop OpAdd (EVar "x") (EConst (VInt 3%Z))))).
