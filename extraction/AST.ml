open Types
open Values

type binop =
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpMod
| OpEq
| OpNe
| OpLt
| OpLe
| OpGt
| OpGe
| OpAnd
| OpOr

type unop =
| OpNeg
| OpNot

type expr =
| EConst of value
| EVar of char list
| EBinop of binop * expr * expr
| EUnop of unop * expr
| ECall of char list * expr list

type stmt =
| SSkip
| SAssign of char list * expr
| SSeq of stmt * stmt
| SIf of expr * stmt * stmt
| SWhile of expr * stmt
| SFor of char list * expr * expr * stmt
| SCase of expr * (expr * stmt) list * stmt
| SReturn of expr option
| SCall of char list * expr list

type var_decl = { vd_name : char list; vd_type : ty; vd_init : value option }

type param_kind =
| PKInput
| PKOutput
| PKInOut

type param_decl = { pd_kind : param_kind; pd_name : char list; pd_type : ty }

type function_def = { fn_name : char list; fn_params : param_decl list;
                      fn_return_type : ty; fn_vars : var_decl list;
                      fn_body : stmt }

type program_def = { pg_name : char list; pg_vars : var_decl list;
                     pg_body : stmt }

type compilation_unit = { cu_functions : function_def list;
                          cu_program : program_def }
