(** ST到字节码编译器工具 
    
    由于完整的词法/语法分析器较复杂，这里提供手写AST的方式
    直接构造示例程序的AST并编译为字节码
*)

open Printf
open Types
open Values
open Environment
open AST
open Bytecode
open CompilerState
open Compiler

(** 辅助函数 *)
let char_list_of_string s =
  let len = Stdlib.String.length s in
  let rec explode i =
    if i >= len then []
    else Stdlib.String.get s i :: explode (i + 1)
  in explode 0

(** 保存字节码到文件（兼容STVM格式） *)
let save_bytecode filename code =
  let oc = open_out_bin filename in
  
  (* STVM格式：代码长度 + 指令序列 *)
  let code_len = Stdlib.List.length code in
  output_binary_int oc code_len;
  
  (* 写入每条指令 *)
  let rec write_instr = function
    | ILoadInt n -> 
        output_byte oc 0x01; 
        output_binary_int oc n
    | ILoadVar x -> 
        output_byte oc 0x05;
        let name = Stdlib.String.concat "" (Stdlib.List.map (Stdlib.String.make 1) x) in
        output_binary_int oc (Stdlib.String.length name);
        output_string oc name
    | IStoreVar x -> 
        output_byte oc 0x06;
        let name = Stdlib.String.concat "" (Stdlib.List.map (Stdlib.String.make 1) x) in
        output_binary_int oc (Stdlib.String.length name);
        output_string oc name
    | IAdd -> output_byte oc 0x10
    | ISub -> output_byte oc 0x11
    | IMul -> output_byte oc 0x12
    | IDiv -> output_byte oc 0x13
    | IMod -> output_byte oc 0x14
    | INeg -> output_byte oc 0x15
    | IEq -> output_byte oc 0x20
    | INe -> output_byte oc 0x21
    | ILt -> output_byte oc 0x22
    | ILe -> output_byte oc 0x23
    | IGt -> output_byte oc 0x24
    | IGe -> output_byte oc 0x25
    | IAnd -> output_byte oc 0x30
    | IOr -> output_byte oc 0x31
    | INot -> output_byte oc 0x32
    | IJmp addr -> output_byte oc 0x40; output_binary_int oc addr
    | IJz addr -> output_byte oc 0x41; output_binary_int oc addr
    | IJnz addr -> output_byte oc 0x42; output_binary_int oc addr
    | IPop -> output_byte oc 0x60
    | IHalt -> output_byte oc 0xFF
    | INop -> output_byte oc 0x00
    | _ -> output_byte oc 0x00  (* 其他指令暂不支持 *)
  in
  
  let rec write_code = function
    | [] -> ()
    | instr :: rest -> write_instr instr; write_code rest
  in
  
  write_code code;
  close_out oc;
  printf "✓ Bytecode saved: %s (%d instructions)\n" filename code_len

(** 编译阶乘程序 *)
let compile_factorial () =
  printf "\n=== Compiling: Factorial (5!) ===\n";
  
  let n = char_list_of_string "n" in
  let result = char_list_of_string "result" in
  let i = char_list_of_string "i" in
  
  (* 构造 AST *)
  let init_n = SAssign (n, EConst (VInt 5)) in
  let init_result = SAssign (result, EConst (VInt 1)) in
  let init_i = SAssign (i, EConst (VInt 1)) in
  
  let cond = EBinop (OpLe, EVar i, EVar n) in
  let update_result = SAssign (result, EBinop (OpMul, EVar result, EVar i)) in
  let update_i = SAssign (i, EBinop (OpAdd, EVar i, EConst (VInt 1))) in
  let loop_body = SSeq (update_result, update_i) in
  let while_loop = SWhile (cond, loop_body) in
  
  let program = SSeq (init_n, SSeq (init_result, SSeq (init_i, while_loop))) in
  
  (* 编译 *)
  let cs = compile_stmt program init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated %d instructions\n" (Stdlib.List.length code);
  save_bytecode "factorial.stbc" code;
  
  code

(** 编译斐波那契程序 *)
let compile_fibonacci () =
  printf "\n=== Compiling: Fibonacci (10th number) ===\n";
  
  let n = char_list_of_string "n" in
  let fib_prev = char_list_of_string "fib_prev" in
  let fib_curr = char_list_of_string "fib_curr" in
  let fib_next = char_list_of_string "fib_next" in
  let counter = char_list_of_string "counter" in
  
  let init_n = SAssign (n, EConst (VInt 10)) in
  let init_prev = SAssign (fib_prev, EConst (VInt 0)) in
  let init_curr = SAssign (fib_curr, EConst (VInt 1)) in
  let init_counter = SAssign (counter, EConst (VInt 2)) in
  
  let cond = EBinop (OpLe, EVar counter, EVar n) in
  let calc_next = SAssign (fib_next, EBinop (OpAdd, EVar fib_prev, EVar fib_curr)) in
  let update_prev = SAssign (fib_prev, EVar fib_curr) in
  let update_curr = SAssign (fib_curr, EVar fib_next) in
  let update_counter = SAssign (counter, EBinop (OpAdd, EVar counter, EConst (VInt 1))) in
  
  let loop_body = SSeq (calc_next, SSeq (update_prev, SSeq (update_curr, update_counter))) in
  let while_loop = SWhile (cond, loop_body) in
  
  let program = SSeq (init_n, SSeq (init_prev, SSeq (init_curr, SSeq (init_counter, while_loop)))) in
  
  let cs = compile_stmt program init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated %d instructions\n" (Stdlib.List.length code);
  save_bytecode "fibonacci.stbc" code;
  
  code

(** 编译GCD程序 *)
let compile_gcd () =
  printf "\n=== Compiling: GCD (48, 18) ===\n";
  
  let a = char_list_of_string "a" in
  let b = char_list_of_string "b" in
  let temp = char_list_of_string "temp" in
  
  let init_a = SAssign (a, EConst (VInt 48)) in
  let init_b = SAssign (b, EConst (VInt 18)) in
  
  let cond = EBinop (OpNe, EVar b, EConst (VInt 0)) in
  let save_b = SAssign (temp, EVar b) in
  let calc_mod = SAssign (b, EBinop (OpMod, EVar a, EVar b)) in
  let update_a = SAssign (a, EVar temp) in
  
  let loop_body = SSeq (save_b, SSeq (calc_mod, update_a)) in
  let while_loop = SWhile (cond, loop_body) in
  
  let program = SSeq (init_a, SSeq (init_b, while_loop)) in
  
  let cs = compile_stmt program init_compiler_state in
  let code = cs.cs_code in
  
  printf "Generated %d instructions\n" (Stdlib.List.length code);
  save_bytecode "gcd.stbc" code;
  
  code

(** 主程序 *)
let () =
  printf "======================================================\n";
  printf "VeriST Compiler - Generating Bytecode Files\n";
  printf "======================================================\n";
  
  (* 编译所有测试程序 *)
  let _ = compile_factorial () in
  let _ = compile_fibonacci () in
  let _ = compile_gcd () in
  
  printf "\n======================================================\n";
  printf "Compilation Complete!\n";
  printf "======================================================\n";
  printf "\nGenerated files:\n";
  printf "  • factorial.stbc  - Computes 5! = 120\n";
  printf "  • fibonacci.stbc  - Computes Fib(10) = 55\n";
  printf "  • gcd.stbc        - Computes GCD(48,18) = 6\n";
  printf "\nThese .stbc files can be executed in STVM\n";
  printf "======================================================\n"
