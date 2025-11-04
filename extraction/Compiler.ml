open AST
open Bytecode
open CompilerState
open Datatypes
open List
open VM
open Values

(** val compile_expr : expr -> compiler_state -> compiler_state **)

let rec compile_expr e cs =
  match e with
  | EConst v ->
    (match v with
     | VBool b -> emit cs (ILoadBool b)
     | VInt n -> emit cs (ILoadInt n)
     | VReal r -> emit cs (ILoadReal r)
     | VString s -> emit cs (ILoadString s)
     | VVoid -> cs)
  | EVar x -> emit cs (ILoadVar x)
  | EBinop (op, e1, e2) ->
    let cs1 = compile_expr e1 cs in
    let cs2 = compile_expr e2 cs1 in emit cs2 (binop_to_instr op)
  | EUnop (op, e1) ->
    let cs1 = compile_expr e1 cs in emit cs1 (unop_to_instr op)
  | ECall (fname, args) ->
    let cs1 = fold_left (fun cs_acc arg -> compile_expr arg cs_acc) args cs in
    (match lookup_function cs1.cs_function_table fname with
     | Some addr -> emit cs1 (ICall addr)
     | None -> cs1)

(** val compile_stmt : stmt -> compiler_state -> compiler_state **)

let rec compile_stmt s cs =
  match s with
  | SSkip -> cs
  | SAssign (x, e) -> let cs1 = compile_expr e cs in emit cs1 (IStoreVar x)
  | SSeq (s1, s2) -> let cs1 = compile_stmt s1 cs in compile_stmt s2 cs1
  | SIf (cond, then_s, else_s) ->
    let cs1 = compile_expr cond cs in
    let (cs2, else_label) = alloc_label cs1 in
    let (cs3, end_label) = alloc_label cs2 in
    let cs4 = emit cs3 (IJz else_label) in
    let cs5 = compile_stmt then_s cs4 in
    let cs6 = emit cs5 (IJmp end_label) in compile_stmt else_s cs6
  | SWhile (cond, body) ->
    let loop_start = current_address cs in
    let cs1 = compile_expr cond cs in
    let (cs2, exit_label) = alloc_label cs1 in
    let cs3 = emit cs2 (IJz exit_label) in
    let cs4 = compile_stmt body cs3 in emit cs4 (IJmp loop_start)
  | SFor (var, start_e, end_e, body) ->
    let cs1 = compile_expr start_e cs in
    let cs2 = emit cs1 (IStoreVar var) in
    let loop_start = current_address cs2 in
    let cs3 = emit cs2 (ILoadVar var) in
    let cs4 = compile_expr end_e cs3 in
    let cs5 = emit cs4 ILe in
    let (cs6, exit_label) = alloc_label cs5 in
    let cs7 = emit cs6 (IJz exit_label) in
    let cs8 = compile_stmt body cs7 in
    let cs9 = emit cs8 (ILoadVar var) in
    let cs10 = emit cs9 (ILoadInt 1) in
    let cs11 = emit cs10 IAdd in
    let cs12 = emit cs11 (IStoreVar var) in emit cs12 (IJmp loop_start)
  | SCase (expr0, _, default_stmt) ->
    let cs1 = compile_expr expr0 cs in
    let cs2 = emit cs1 IPop in compile_stmt default_stmt cs2
  | SReturn o ->
    (match o with
     | Some e -> let cs1 = compile_expr e cs in emit cs1 IRet
     | None -> emit cs IRet)
  | SCall (fname, args) ->
    let cs1 = fold_left (fun cs_acc arg -> compile_expr arg cs_acc) args cs in
    (match lookup_function cs1.cs_function_table fname with
     | Some addr -> let cs2 = emit cs1 (ICall addr) in emit cs2 IPop
     | None -> cs1)

(** val compile_function :
    function_def -> compiler_state -> compiler_state **)

let compile_function fn cs =
  let fn_addr = current_address cs in
  let cs1 = add_function cs fn.fn_name fn_addr in
  let cs2 = compile_stmt fn.fn_body cs1 in emit cs2 IRet

(** val compile_program : compilation_unit -> code * function_info list **)

let compile_program cu =
  let cs1 =
    fold_left (fun cs fn -> compile_function fn cs) cu.cu_functions
      init_compiler_state
  in
  let cs2 = compile_stmt cu.cu_program.pg_body cs1 in
  let cs3 = emit cs2 IHalt in
  let func_infos =
    map (fun fn ->
      let addr =
        match lookup_function cs3.cs_function_table fn.fn_name with
        | Some a -> a
        | None -> 0
      in
      { fi_name = fn.fn_name; fi_address = addr; fi_param_count =
      (length fn.fn_params); fi_return_type = fn.fn_return_type })
      cu.cu_functions
  in
  (cs3.cs_code, func_infos)
