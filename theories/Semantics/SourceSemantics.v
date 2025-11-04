(** * SourceSemantics: ST 源语言的操作语义

    本模块定义 IEC 61131-3 ST 源语言的操作语义，
    包括表达式求值和语句执行的归纳定义。
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Semantics.Operations.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** 二元运算符求值 *)

(** 根据运算符类型调用相应的运算函数 *)
Definition eval_binop (op : binop) (v1 v2 : value) : option value :=
  match op with
  | OpAdd => eval_add v1 v2
  | OpSub => eval_sub v1 v2
  | OpMul => eval_mul v1 v2
  | OpDiv => eval_div v1 v2
  | OpMod => eval_mod v1 v2
  | OpEq => eval_eq v1 v2
  | OpNe => eval_ne v1 v2
  | OpLt => eval_lt v1 v2
  | OpLe => eval_le v1 v2
  | OpGt => eval_gt v1 v2
  | OpGe => eval_ge v1 v2
  | OpAnd => eval_and v1 v2
  | OpOr => eval_or v1 v2
  end.

(** ** 一元运算符求值 *)

(** 根据运算符类型调用相应的运算函数 *)
Definition eval_unop (op : unop) (v : value) : option value :=
  match op with
  | OpNeg => eval_neg v
  | OpNot => eval_not v
  end.

(** ** 表达式求值 *)

(** 表达式求值归纳定义
    eval_expr env e v 表示在环境 env 中，表达式 e 求值为 v *)
Inductive eval_expr : env -> expr -> value -> Prop :=
  | E_Const : forall env v,
      eval_expr env (EConst v) v
      
  | E_Var : forall env x v,
      lookup env x = Some v ->
      eval_expr env (EVar x) v
      
  | E_Binop : forall env op e1 e2 v1 v2 v,
      eval_expr env e1 v1 ->
      eval_expr env e2 v2 ->
      eval_binop op v1 v2 = Some v ->
      eval_expr env (EBinop op e1 e2) v
      
  | E_Unop : forall env op e1 v1 v,
      eval_expr env e1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr env (EUnop op e1) v
      
  | E_Call : forall env fname args,
      (* 函数调用暂不实现，返回空值 *)
      (* 在阶段3实现完整的函数调用语义 *)
      eval_expr env (ECall fname args) VVoid.

(** ** 语句执行 *)

(** 语句执行归纳定义
    exec_stmt env s env' 表示在环境 env 中执行语句 s 后得到新环境 env' *)
Inductive exec_stmt : env -> stmt -> env -> Prop :=
  | X_Skip : forall env,
      exec_stmt env SSkip env
      
  | X_Assign : forall env x e v,
      eval_expr env e v ->
      exec_stmt env (SAssign x e) (update env x v)
      
  | X_Seq : forall env env' env'' s1 s2,
      exec_stmt env s1 env' ->
      exec_stmt env' s2 env'' ->
      exec_stmt env (SSeq s1 s2) env''
      
  | X_IfTrue : forall env env' cond then_s else_s,
      eval_expr env cond (VBool true) ->
      exec_stmt env then_s env' ->
      exec_stmt env (SIf cond then_s else_s) env'
      
  | X_IfFalse : forall env env' cond then_s else_s,
      eval_expr env cond (VBool false) ->
      exec_stmt env else_s env' ->
      exec_stmt env (SIf cond then_s else_s) env'
      
  | X_WhileFalse : forall env cond body,
      eval_expr env cond (VBool false) ->
      exec_stmt env (SWhile cond body) env
      
  | X_WhileTrue : forall env env' env'' cond body,
      eval_expr env cond (VBool true) ->
      exec_stmt env body env' ->
      exec_stmt env' (SWhile cond body) env'' ->
      exec_stmt env (SWhile cond body) env''
      
  | X_For : forall env env' var start_e end_e body start_v end_v,
      (* FOR 循环: FOR var := start_e TO end_e DO body END_FOR *)
      eval_expr env start_e start_v ->
      eval_expr env end_e end_v ->
      exec_for_loop (update env var start_v) var start_v end_v body env' ->
      exec_stmt env (SFor var start_e end_e body) env'
      
  | X_Case : forall env env' scrutinee cases default_stmt v,
      (* CASE 语句暂时简化实现 *)
      eval_expr env scrutinee v ->
      exec_case_branches env v cases default_stmt env' ->
      exec_stmt env (SCase scrutinee cases default_stmt) env'
      
  | X_Return : forall env e,
      (* RETURN 语句暂不完整实现，在阶段3完善 *)
      exec_stmt env (SReturn e) env
      
  | X_Call : forall env fname args,
      (* 过程调用暂不实现，在阶段3完善 *)
      exec_stmt env (SCall fname args) env

(** FOR 循环辅助定义 *)
with exec_for_loop : env -> string -> value -> value -> stmt -> env -> Prop :=
  | For_Done : forall env var current end_val body,
      (* 当前值大于结束值时，循环结束 *)
      eval_gt current end_val = Some (VBool true) ->
      exec_for_loop env var current end_val body env
      
  | For_Step : forall env env' env'' var current end_val body next,
      (* 当前值小于等于结束值时，执行循环体 *)
      eval_le current end_val = Some (VBool true) ->
      exec_stmt env body env' ->
      (* 递增循环变量 *)
      eval_add current (VInt 1%Z) = Some next ->
      exec_for_loop (update env' var next) var next end_val body env'' ->
      exec_for_loop env var current end_val body env''

(** CASE 分支匹配辅助定义 *)
with exec_case_branches : env -> value -> list (expr * stmt) -> stmt -> env -> Prop :=
  | Case_Default : forall env env' v default_stmt,
      (* 没有匹配的分支，执行默认语句 *)
      exec_stmt env default_stmt env' ->
      exec_case_branches env v [] default_stmt env'
      
  | Case_Match : forall env env' v case_e case_s rest default_stmt case_v,
      (* 找到匹配的分支 *)
      eval_expr env case_e case_v ->
      eval_eq v case_v = Some (VBool true) ->
      exec_stmt env case_s env' ->
      exec_case_branches env v ((case_e, case_s) :: rest) default_stmt env'
      
  | Case_NoMatch : forall env env' v case_e case_s rest default_stmt case_v,
      (* 当前分支不匹配，继续检查后续分支 *)
      eval_expr env case_e case_v ->
      eval_eq v case_v = Some (VBool false) ->
      exec_case_branches env v rest default_stmt env' ->
      exec_case_branches env v ((case_e, case_s) :: rest) default_stmt env'.

(** ** 基本示例 *)

(** 示例：常量表达式求值 *)
Example ex_eval_const :
  eval_expr empty (EConst (VInt 42)) (VInt 42).
Proof.
  apply E_Const.
Qed.

(** 示例：算术表达式求值 *)
Example ex_eval_add :
  eval_expr empty (EBinop OpAdd (EConst (VInt 3)) (EConst (VInt 5))) (VInt 8).
Proof.
  apply E_Binop with (v1 := VInt 3) (v2 := VInt 5).
  - apply E_Const.
  - apply E_Const.
  - reflexivity.
Qed.

(** 示例：变量赋值 *)
Example ex_exec_assign :
  exec_stmt empty 
            (SAssign "x" (EConst (VInt 10))) 
            (update empty "x" (VInt 10)).
Proof.
  apply X_Assign.
  apply E_Const.
Qed.

(** 示例：顺序语句 *)
Example ex_exec_seq :
  exec_stmt empty
            (SSeq (SAssign "x" (EConst (VInt 10)))
                  (SAssign "y" (EConst (VInt 20))))
            (update (update empty "x" (VInt 10)) "y" (VInt 20)).
Proof.
  apply X_Seq with (env' := update empty "x" (VInt 10)).
  - apply X_Assign. apply E_Const.
  - apply X_Assign. apply E_Const.
Qed.

(** 示例：条件语句（真分支）*)
Example ex_exec_if_true :
  exec_stmt empty
            (SIf (EConst (VBool true))
                 (SAssign "x" (EConst (VInt 1)))
                 (SAssign "x" (EConst (VInt 2))))
            (update empty "x" (VInt 1)).
Proof.
  apply X_IfTrue.
  - apply E_Const.
  - apply X_Assign. apply E_Const.
Qed.

(** 示例：条件语句（假分支）*)
Example ex_exec_if_false :
  exec_stmt empty
            (SIf (EConst (VBool false))
                 (SAssign "x" (EConst (VInt 1)))
                 (SAssign "x" (EConst (VInt 2))))
            (update empty "x" (VInt 2)).
Proof.
  apply X_IfFalse.
  - apply E_Const.
  - apply X_Assign. apply E_Const.
Qed.
