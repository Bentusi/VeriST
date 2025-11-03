(** * 简单赋值示例

    本示例演示一个简单的赋值语句:
    x := 10
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Syntax.Bytecode.
Require Import STCompiler.Semantics.VM.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** ** 源程序 *)

(** AST: x := 10 *)
Definition simple_assign_ast : stmt :=
  SAssign "x" (EConst (VInt 10%Z)).

(** ** 预期的字节码 *)

(** 手动编译的字节码 *)
Definition simple_assign_code : code :=
  [ILoadInt 10;
   IStoreVar "x";
   IHalt].

(** ** 验证 *)

(** 验证字节码结构 *)
Example bytecode_length : 
  code_length simple_assign_code = 3%nat.
Proof. reflexivity. Qed.

Example bytecode_first_instr :
  get_instr simple_assign_code 0%nat = Some ((ILoadInt 10)%Z).
Proof. reflexivity. Qed.

Example bytecode_second_instr :
  get_instr simple_assign_code 1%nat = Some (IStoreVar "x").
Proof. reflexivity. Qed.

Example bytecode_third_instr :
  get_instr simple_assign_code 2%nat = Some IHalt.
Proof. reflexivity. Qed.

(** ** 初始虚拟机状态 *)

Definition simple_assign_vm : vm_state :=
  init_vm_state simple_assign_code [].

(** 验证初始状态 *)
Example init_pc_zero :
  vm_pc simple_assign_vm = 0%nat.
Proof. reflexivity. Qed.

Example init_stack_empty :
  vm_stack simple_assign_vm = [].
Proof. reflexivity. Qed.

Example init_not_halted :
  is_halted simple_assign_vm = false.
Proof. reflexivity. Qed.

Example init_current_instr :
  current_instr simple_assign_vm = Some ((ILoadInt 10)%Z).
Proof. reflexivity. Qed.

(** ** 逐步执行跟踪（手动）*)

(** 步骤 1: 加载 10 到栈后 *)
Definition simple_assign_vm_step1 : vm_state :=
  inc_pc (push_stack simple_assign_vm (VInt 10%Z)).

Example step1_pc :
  vm_pc simple_assign_vm_step1%nat = 1%nat.
Proof. reflexivity. Qed.

Example step1_stack :
  vm_stack simple_assign_vm_step1%nat = [VInt 10].
Proof. reflexivity. Qed.

Example step1_current_instr :
  current_instr simple_assign_vm_step1%nat = Some (IStoreVar "x").
Proof. reflexivity. Qed.

(** 步骤 2: 存储到变量 x 后 *)
Definition simple_assign_vm_step2_opt : option vm_state :=
  match pop_stack simple_assign_vm_step1 with
  | Some (v, vm') => Some (inc_pc (update_env_vm vm' "x" v))
  | None => None
  end.

Example step2_defined :
  simple_assign_vm_step2_opt <> None.
Proof. discriminate. Qed.

(** 提取状态 *)
Definition simple_assign_vm_step2 : vm_state :=
  match simple_assign_vm_step2_opt with
  | Some vm => vm
  | None => simple_assign_vm  (* Should never happen *)
  end.

Example step2_pc :
  vm_pc simple_assign_vm_step2%nat = 2%nat.
Proof. reflexivity. Qed.

Example step2_stack_empty :
  vm_stack simple_assign_vm_step2%nat = [].
Proof. reflexivity. Qed.

Example step2_var_x :
  lookup (vm_env simple_assign_vm_step2) "x" = Some (VInt 10%Z).
Proof. reflexivity. Qed.

Example step2_current_instr :
  current_instr simple_assign_vm_step2%nat = Some IHalt.
Proof. reflexivity. Qed.

(** 步骤 3: 停机后 *)
Definition simple_assign_vm_final : vm_state :=
  halt_vm simple_assign_vm_step2.

Example final_halted :
  is_halted simple_assign_vm_final = true.
Proof. reflexivity. Qed.

Example final_var_x_preserved :
  lookup (vm_env simple_assign_vm_final) "x" = Some (VInt 10%Z).
Proof. reflexivity. Qed.

(** ** 总结 *)

(** 本示例演示了:
    1. 我们可以将简单的 ST 赋值表示为 AST
    2. 我们可以手动将其编译为字节码
    3. 我们可以创建虚拟机状态来执行字节码
    4. 我们可以手动逐步跟踪执行过程
    5. 最终状态正确反映了赋值

    在后续阶段，我们将:
    - 自动化从 AST 到字节码的编译
    - 定义形式化的执行语义
    - 证明编译保持语义
*)
