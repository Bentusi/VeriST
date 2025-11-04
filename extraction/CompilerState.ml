open AST
open Bytecode
open Datatypes
open String

type label = int

type compiler_state = { cs_code : code; cs_next_label : label;
                        cs_function_table : (char list * address) list }

(** val init_compiler_state : compiler_state **)

let init_compiler_state =
  { cs_code = []; cs_next_label = 0; cs_function_table = [] }

(** val emit : compiler_state -> instr -> compiler_state **)

let emit cs i =
  { cs_code = (app cs.cs_code (i :: [])); cs_next_label = cs.cs_next_label;
    cs_function_table = cs.cs_function_table }

(** val current_address : compiler_state -> address **)

let current_address cs =
  length cs.cs_code

(** val alloc_label : compiler_state -> compiler_state * label **)

let alloc_label cs =
  let l = cs.cs_next_label in
  ({ cs_code = cs.cs_code; cs_next_label = (Stdlib.Int.succ l);
  cs_function_table = cs.cs_function_table }, l)

(** val add_function :
    compiler_state -> char list -> address -> compiler_state **)

let add_function cs name addr =
  { cs_code = cs.cs_code; cs_next_label = cs.cs_next_label;
    cs_function_table = ((name, addr) :: cs.cs_function_table) }

(** val lookup_function :
    (char list * address) list -> char list -> address option **)

let rec lookup_function table name =
  match table with
  | [] -> None
  | p :: rest ->
    let (n, addr) = p in
    if eqb n name then Some addr else lookup_function rest name

(** val binop_to_instr : binop -> instr **)

let binop_to_instr = function
| OpAdd -> IAdd
| OpSub -> ISub
| OpMul -> IMul
| OpDiv -> IDiv
| OpMod -> IMod
| OpEq -> IEq
| OpNe -> INe
| OpLt -> ILt
| OpLe -> ILe
| OpGt -> IGt
| OpGe -> IGe
| OpAnd -> IAnd
| OpOr -> IOr

(** val unop_to_instr : unop -> instr **)

let unop_to_instr = function
| OpNeg -> INeg
| OpNot -> INot
