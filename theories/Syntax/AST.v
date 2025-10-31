(** * AST: Abstract Syntax Tree for IEC 61131-3 ST

    This module defines the abstract syntax tree for the
    IEC 61131-3 Structured Text language, including expressions,
    statements, functions, and programs.
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** Operators *)

(** Binary operators *)
Inductive binop : Type :=
  (* Arithmetic operators *)
  | OpAdd : binop      (** Addition + *)
  | OpSub : binop      (** Subtraction - *)
  | OpMul : binop      (** Multiplication * *)
  | OpDiv : binop      (** Division / *)
  | OpMod : binop      (** Modulo MOD *)
  (* Comparison operators *)
  | OpEq : binop       (** Equal = *)
  | OpNe : binop       (** Not equal <> *)
  | OpLt : binop       (** Less than < *)
  | OpLe : binop       (** Less or equal <= *)
  | OpGt : binop       (** Greater than > *)
  | OpGe : binop       (** Greater or equal >= *)
  (* Logical operators *)
  | OpAnd : binop      (** Logical AND *)
  | OpOr : binop.      (** Logical OR *)

(** Unary operators *)
Inductive unop : Type :=
  | OpNeg : unop       (** Negation - *)
  | OpNot : unop.      (** Logical NOT *)

(** ** Expressions *)

(** Expressions *)
Inductive expr : Type :=
  | EConst : value -> expr                      (** Constant *)
  | EVar : string -> expr                       (** Variable reference *)
  | EBinop : binop -> expr -> expr -> expr      (** Binary operation *)
  | EUnop : unop -> expr -> expr                (** Unary operation *)
  | ECall : string -> list expr -> expr.        (** Function call *)

(** ** Statements *)

(** Statements *)
Inductive stmt : Type :=
  | SSkip : stmt                                (** Empty statement *)
  | SAssign : string -> expr -> stmt            (** Assignment x := e *)
  | SSeq : stmt -> stmt -> stmt                 (** Sequence s1; s2 *)
  | SIf : expr -> stmt -> stmt -> stmt          (** If-then-else *)
  | SWhile : expr -> stmt -> stmt               (** While loop *)
  | SFor : string -> expr -> expr -> stmt -> stmt  (** For loop *)
  | SCase : expr -> list (expr * stmt) -> stmt -> stmt  (** Case statement *)
  | SReturn : option expr -> stmt               (** Return statement *)
  | SCall : string -> list expr -> stmt.        (** Procedure call *)

(** ** Variable Declarations *)

(** Variable declaration *)
Record var_decl : Type := mkVarDecl {
  vd_name : string;
  vd_type : ty;
  vd_init : option value
}.

(** ** Parameter Declarations *)

(** Parameter kind *)
Inductive param_kind : Type :=
  | PKInput : param_kind       (** VAR_INPUT *)
  | PKOutput : param_kind      (** VAR_OUTPUT *)
  | PKInOut : param_kind.      (** VAR_IN_OUT *)

(** Parameter declaration *)
Record param_decl : Type := mkParamDecl {
  pd_kind : param_kind;
  pd_name : string;
  pd_type : ty
}.

(** ** Function Definitions *)

(** Function definition *)
Record function_def : Type := mkFunctionDef {
  fn_name : string;
  fn_params : list param_decl;
  fn_return_type : ty;
  fn_vars : list var_decl;
  fn_body : stmt
}.

(** ** Program Definitions *)

(** Program definition *)
Record program_def : Type := mkProgramDef {
  pg_name : string;
  pg_vars : list var_decl;
  pg_body : stmt
}.

(** ** Compilation Unit *)

(** Complete compilation unit *)
Record compilation_unit : Type := mkCompilationUnit {
  cu_functions : list function_def;
  cu_program : program_def
}.

(** ** Helper Functions *)

(** Get parameter names from parameter list *)
Fixpoint param_names (params : list param_decl) : list string :=
  match params with
  | [] => []
  | p :: ps => pd_name p :: param_names ps
  end.

(** Get variable names from variable list *)
Fixpoint var_names (vars : list var_decl) : list string :=
  match vars with
  | [] => []
  | v :: vs => vd_name v :: var_names vs
  end.

(** Count parameters *)
Definition param_count (params : list param_decl) : nat :=
  length params.

(** ** Expression Properties *)

(** Size of an expression (for induction) *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EConst _ => 1
  | EVar _ => 1
  | EBinop _ e1 e2 => S (expr_size e1 + expr_size e2)
  | EUnop _ e1 => S (expr_size e1)
  | ECall _ args => S (length args)  (* Simplified for now *)
  end.

(** Size of a statement (for induction) *)
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
  | SCall _ args => S (length args)  (* Simplified for now *)
  end.

(** ** Examples *)

(** Example: 5 + 3 *)
Example ex_add_expr : expr :=
  EBinop OpAdd (EConst (VInt 5%Z)) (EConst (VInt 3%Z)).

(** Example: x := 10 *)
Example ex_assign_stmt : stmt :=
  SAssign "x" (EConst (VInt 10%Z)).

(** Example: IF x > 0 THEN y := 1 ELSE y := 0 END_IF *)
Example ex_if_stmt : stmt :=
  SIf (EBinop OpGt (EVar "x") (EConst (VInt 0%Z)))
      (SAssign "y" (EConst (VInt 1%Z)))
      (SAssign "y" (EConst (VInt 0%Z))).

(** Example: WHILE x > 0 DO x := x - 1 END_WHILE *)
Example ex_while_stmt : stmt :=
  SWhile (EBinop OpGt (EVar "x") (EConst (VInt 0%Z)))
         (SAssign "x" (EBinop OpSub (EVar "x") (EConst (VInt 1%Z)))).

(** Example: FOR i := 1 TO 10 DO sum := sum + i END_FOR *)
Example ex_for_stmt : stmt :=
  SFor "i" (EConst (VInt 1%Z)) (EConst (VInt 10%Z))
       (SAssign "sum" (EBinop OpAdd (EVar "sum") (EVar "i"))).

(** Example variable declaration *)
Example ex_var_decl : var_decl :=
  mkVarDecl "counter" TyInt (Some (VInt 0%Z)).

(** Example parameter declaration *)
Example ex_param_decl : param_decl :=
  mkParamDecl PKInput "value" TyInt.

(** Example function: Add(a, b : INT) : INT *)
Example ex_function : function_def :=
  mkFunctionDef "Add"
    [mkParamDecl PKInput "a" TyInt; mkParamDecl PKInput "b" TyInt]
    TyInt
    []
    (SReturn (Some (EBinop OpAdd (EVar "a") (EVar "b")))).

(** Example program *)
Example ex_program : program_def :=
  mkProgramDef "SimpleCalc"
    [mkVarDecl "x" TyInt (Some (VInt 0%Z));
     mkVarDecl "y" TyInt (Some (VInt 0%Z))]
    (SSeq (SAssign "x" (EConst (VInt 5%Z)))
          (SAssign "y" (EBinop OpAdd (EVar "x") (EConst (VInt 3%Z))))).
