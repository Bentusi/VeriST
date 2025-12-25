(** * Compiler: 主编译器实现

    本模块实现从 ST AST 到字节码的编译器。

    © 2024 JIANG Wei <jiangwey@outlook.com> 
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Semantics.VM.
Require Import STCompiler.Compiler.CompilerState.
Require Import STCompiler.Compiler.CodeGen.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ** 表达式编译 *)

(** 编译表达式：将表达式编译为字节码，结果放在栈顶 *)
Fixpoint compile_expr (e : expr) (cs : compiler_state) : compiler_state :=
  match e with
  | EConst v => 
      (* 使用 CodeGen 模块生成常量加载指令（包括质量位处理） *)
      emit_list cs (gen_load_const v)
  | EVar x => 
      emit cs (ILoadVar x)
  | EBinop op e1 e2 =>
      (* 先计算 e1，再计算 e2，最后执行运算 *)
      let cs1 := compile_expr e1 cs in
      let cs2 := compile_expr e2 cs1 in
      emit cs2 (binop_to_instr op)
  | EUnop op e1 =>
      (* 先计算 e1，再执行运算 *)
      let cs1 := compile_expr e1 cs in
      emit cs1 (unop_to_instr op)
  | ECall fname args =>
      (* 编译所有参数（从左到右） *)
      let cs1 := fold_left (fun cs_acc arg => compile_expr arg cs_acc) args cs in
      (* 查找函数地址并调用 *)
      match lookup_function cs1.(cs_function_table) fname with
      | Some addr => emit cs1 (ICall addr)
      | None => cs1  (* 错误：函数未找到，暂时跳过 *)
      end
  end.

(** ** 语句编译 *)

(** 编译语句：将语句编译为字节码
    注意：由于与 compile_case_branches 相互递归，这里简化处理 CASE 语句 *)
Fixpoint compile_stmt (s : stmt) (cs : compiler_state) {struct s} : compiler_state :=
  match s with
  | SSkip => 
      cs  (* 空语句不生成代码 *)
      
  | SAssign x e =>
      (* 计算表达式，然后存储到变量 *)
      let cs1 := compile_expr e cs in
      emit cs1 (IStoreVar x)
      
  | SSeq s1 s2 =>
      (* 顺序执行：先编译 s1，再编译 s2 *)
      let cs1 := compile_stmt s1 cs in
      compile_stmt s2 cs1
      
  | SIf cond then_s else_s =>
      (* 编译条件表达式 *)
      let cs1 := compile_expr cond cs in
      (* 分配标签 *)
      let (cs2, else_label) := alloc_label cs1 in
      let (cs3, end_label) := alloc_label cs2 in
      (* 条件跳转到 else 分支 *)
      let cs4 := emit cs3 (IJz else_label) in
      (* 编译 then 分支 *)
      let cs5 := compile_stmt then_s cs4 in
      (* 跳过 else 分支 *)
      let cs6 := emit cs5 (IJmp end_label) in
      (* else 分支的位置 *)
      let else_addr := current_address cs6 in
      (* 编译 else 分支 *)
      let cs7 := compile_stmt else_s cs6 in
      (* end 标签的位置 *)
      let end_addr := current_address cs7 in
      (* 注意：这里简化处理，实际需要回填地址 *)
      cs7
      
  | SWhile cond body =>
      (* 循环开始位置 *)
      let loop_start := current_address cs in
      (* 编译条件 *)
      let cs1 := compile_expr cond cs in
      (* 分配退出标签 *)
      let (cs2, exit_label) := alloc_label cs1 in
      (* 条件为假时跳出循环 *)
      let cs3 := emit cs2 (IJz exit_label) in
      (* 编译循环体 *)
      let cs4 := compile_stmt body cs3 in
      (* 跳回循环开始 *)
      let cs5 := emit cs4 (IJmp loop_start) in
      (* 退出位置 *)
      let exit_addr := current_address cs5 in
      cs5
      
  | SFor var start_e end_e body =>
      (* FOR 循环直接展开编译：
         var := start_e;
         loop_start:
         temp := var <= end_e;
         if temp == 0 goto exit;
         body;
         var := var + 1;
         goto loop_start;
         exit:
      *)
      (* 编译初始化: var := start_e *)
      let cs1 := compile_expr start_e cs in
      let cs2 := emit cs1 (IStoreVar var) in
      (* 循环开始位置 *)
      let loop_start := current_address cs2 in
      (* 编译条件: var <= end_e *)
      let cs3 := emit cs2 (ILoadVar var) in
      let cs4 := compile_expr end_e cs3 in
      let cs5 := emit cs4 ILe in
      (* 分配退出标签 *)
      let (cs6, exit_label) := alloc_label cs5 in
      (* 条件为假时跳出循环 *)
      let cs7 := emit cs6 (IJz exit_label) in
      (* 编译循环体 *)
      let cs8 := compile_stmt body cs7 in
      (* 编译递增: var := var + 1 *)
      let cs9 := emit cs8 (ILoadVar var) in
      let cs10 := emit cs9 (ILoadInt 1%Z) in
      let cs11 := emit cs10 IAdd in
      let cs12 := emit cs11 (IStoreVar var) in
      (* 跳回循环开始 *)
      let cs13 := emit cs12 (IJmp loop_start) in
      (* 退出位置 *)
      let exit_addr := current_address cs13 in
      cs13
      
  | SCase expr cases default_stmt =>
      (* 简化实现：CASE 语句暂时编译为默认分支
         完整实现需要相互递归，将在后续优化 *)
      let cs1 := compile_expr expr cs in
      let cs2 := emit cs1 IPop in  (* 弹出表达式结果 *)
      compile_stmt default_stmt cs2
      
  | SReturn None =>
      emit cs IRet
      
  | SReturn (Some e) =>
      (* 计算返回值表达式 *)
      let cs1 := compile_expr e cs in
      emit cs1 IRet
      
  | SCall fname args =>
      (* 编译参数 *)
      let cs1 := fold_left (fun cs_acc arg => compile_expr arg cs_acc) args cs in
      (* 查找并调用函数 *)
      match lookup_function cs1.(cs_function_table) fname with
      | Some addr => 
          let cs2 := emit cs1 (ICall addr) in
          (* 丢弃返回值（过程调用） *)
          emit cs2 IPop
      | None => cs1
      end
  end.

(** ** 函数编译 *)

(** 编译函数定义 *)
Definition compile_function (fn : function_def) (cs : compiler_state) : compiler_state :=
  (* 记录函数起始地址 *)
  let fn_addr := current_address cs in
  (* 将函数添加到函数表 *)
  let cs1 := add_function cs fn.(fn_name) fn_addr in
  (* 编译函数体 *)
  let cs2 := compile_stmt fn.(fn_body) cs1 in
  (* 确保函数有返回指令 *)
  match fn.(fn_return_type) with
  | TyVoid => 
      (* void 函数：如果没有显式返回，添加返回指令 *)
      emit cs2 IRet
  | _ => 
      (* 有返回值的函数：应该有显式返回（类型检查保证） *)
      emit cs2 IRet
  end.

(** ** 程序编译 *)

(** 编译完整程序 *)
Definition compile_program (cu : compilation_unit) : code * list function_info :=
  (* 首先编译所有函数 *)
  let cs1 := fold_left (fun cs fn => compile_function fn cs) cu.(cu_functions) init_compiler_state in
  
  (* 记录主程序起始地址 *)
  let prog_addr := current_address cs1 in
  
  (* 编译主程序体 *)
  let cs2 := compile_stmt cu.(cu_program).(pg_body) cs1 in
  
  (* 添加停机指令 *)
  let cs3 := emit cs2 IHalt in
  
  (* 生成函数信息表 *)
  let func_infos := map (fun fn => 
    let addr := match lookup_function cs3.(cs_function_table) fn.(fn_name) with
                | Some a => a
                | None => 0%nat  (* 不应该发生 *)
                end in
    mkFunctionInfo fn.(fn_name) 
                   addr
                   (length fn.(fn_params))
                   fn.(fn_return_type)
  ) cu.(cu_functions) in
  
  (cs3.(cs_code), func_infos).

(** ** 示例 *)

(** 示例 1: 编译简单赋值 x := 42 *)
Example ex_compile_assign : 
  let e := EConst (VInt 42%Z) in
  let s := SAssign "x" e in
  let cs := compile_stmt s init_compiler_state in
  cs.(cs_code) = [ILoadInt 42%Z; IStoreVar "x"].
Proof.
  simpl. reflexivity.
Qed.

(** 示例 2: 编译算术表达式 (1 + 2) * 3 *)
Example ex_compile_arith :
  let e := EBinop OpMul (EBinop OpAdd (EConst (VInt 1%Z)) (EConst (VInt 2%Z))) 
                        (EConst (VInt 3%Z)) in
  let cs := compile_expr e init_compiler_state in
  cs.(cs_code) = [ILoadInt 1%Z; ILoadInt 2%Z; IAdd; ILoadInt 3%Z; IMul].
Proof.
  simpl. reflexivity.
Qed.

(** 示例 3: 编译条件语句（简化版，不考虑标签回填） *)
Example ex_compile_if_simple :
  let cond := EVar "x" in
  let then_s := SAssign "y" (EConst (VInt 1%Z)) in
  let else_s := SAssign "y" (EConst (VInt 0%Z)) in
  let s := SIf cond then_s else_s in
  let cs := compile_stmt s init_compiler_state in
  cs.(cs_code) <> nil.
Proof.
  simpl. discriminate.
Qed.
