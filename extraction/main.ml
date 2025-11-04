(** * Main: ST编译器主程序

    本文件是提取的OCaml代码的主入口点。
    提供命令行接口来编译和执行ST程序。
*)

open Printf
open Types
open Values
open Environment
open AST
open Bytecode
open Operations
open VM
open VMSemantics
open CompilerState
open Compiler

(** 辅助函数：从Coq string (char list) 转换为OCaml string *)
let string_of_char_list chars =
  let buf = Buffer.create 16 in
  let rec add_chars = function
    | [] -> ()
    | c :: rest -> Buffer.add_char buf c; add_chars rest
  in
  add_chars chars;
  Buffer.contents buf

(** 辅助函数：从OCaml string 转换为Coq string (char list) *)
let char_list_of_string s =
  let len = Stdlib.String.length s in
  let rec explode i =
    if i >= len then []
    else Stdlib.String.get s i :: explode (i + 1)
  in explode 0

(** 辅助函数：打印值 *)
let rec string_of_value = function
  | VBool b -> if b then "TRUE" else "FALSE"
  | VInt n -> string_of_int n
  | VReal r -> 
      (* Q是有理数，表示为 num/den *)
      Printf.sprintf "%d/%d" r.QArith_base.coq_Qnum r.QArith_base.coq_Qden
  | VString s -> "\"" ^ Stdlib.String.escaped (string_of_char_list s) ^ "\""
  | VVoid -> "VOID"

(** 辅助函数：打印栈 *)
let string_of_stack stk =
  let rec map_values = function
    | [] -> []
    | v :: rest -> string_of_value v :: map_values rest
  in
  "[" ^ Stdlib.String.concat "; " (map_values stk) ^ "]"

(** 辅助函数：计算列表长度 *)
let rec list_length = function | [] -> 0 | _ :: t -> 1 + list_length t

(** 辅助函数：打印虚拟机状态 *)
let string_of_vm_state st =
  sprintf "VM State:\n  PC: %d\n  Halted: %b\n  Stack: %s\n"
    st.vm_pc st.vm_halted (string_of_stack st.vm_stack)

(** 测试用例1：简单赋值 x := 42 *)
let test_simple_assign () =
  printf "=== Test: Simple Assignment (x := 42) ===\n";
  
  (* 创建AST: x := 42 *)
  let x_name = char_list_of_string "x" in
  let assign_stmt = SAssign (x_name, EConst (VInt 42)) in
  
  (* 编译 *)
  let cs = compile_stmt assign_stmt init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated code: %d instructions\n" (list_length code);
  
  (* 运行 *)
  let init_state = init_vm_state code [] in
  let final_state = run_vm 100 init_state in
  
  printf "%s" (string_of_vm_state final_state);
  
  (* 检查环境 *)
  match lookup final_state.vm_env x_name with
  | Some v -> printf "Variable x = %s\n" (string_of_value v)
  | None -> printf "Variable x not found\n";
  printf "\n"

(** 测试用例2：算术表达式 (1 + 2) * 3 *)
let test_arithmetic () =
  printf "=== Test: Arithmetic Expression ((1 + 2) * 3) ===\n";
  
  (* 创建AST: (1 + 2) * 3 *)
  let one = EConst (VInt 1) in
  let two = EConst (VInt 2) in
  let three = EConst (VInt 3) in
  let add_expr = EBinop (OpAdd, one, two) in
  let mul_expr = EBinop (OpMul, add_expr, three) in
  
  (* 编译 *)
  let cs = compile_expr mul_expr init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated code: %d instructions\n" (list_length code);
  
  (* 运行 *)
  let init_state = init_vm_state code [] in
  let final_state = run_vm 100 init_state in
  
  printf "%s" (string_of_vm_state final_state);
  
  (* 结果应该在栈顶 *)
  match final_state.vm_stack with
  | v :: _ -> printf "Result = %s (expected: 9)\n" (string_of_value v)
  | [] -> printf "Error: Stack is empty\n";
  printf "\n"

(** 测试用例3：简单布尔表达式 *)
let test_boolean () =
  printf "=== Test: Boolean Expression (true AND false) ===\n";
  
  let true_val = EConst (VBool true) in
  let false_val = EConst (VBool false) in
  let and_expr = EBinop (OpAnd, true_val, false_val) in
  
  (* 编译 *)
  let cs = compile_expr and_expr init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated code: %d instructions\n" (list_length code);
  
  (* 运行 *)
  let init_state = init_vm_state code [] in
  let final_state = run_vm 100 init_state in
  
  printf "%s" (string_of_vm_state final_state);
  
  match final_state.vm_stack with
  | v :: _ -> printf "Result = %s (expected: FALSE)\n" (string_of_value v)
  | [] -> printf "Error: Stack is empty\n";
  printf "\n"

(** 主函数 *)
let () =
  printf "==================================================\n";
  printf "VeriST: Verified IEC 61131-3 ST Compiler\n";
  printf "==================================================\n\n";
  
  (* 运行所有测试 *)
  test_simple_assign ();
  test_arithmetic ();
  test_boolean ();
  
  printf "==================================================\n";
  printf "All tests completed!\n";
  printf "==================================================\n"
