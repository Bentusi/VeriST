(** * Simple Assignment Example

    This example demonstrates a simple assignment statement:
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

(** ** Source Program *)

(** AST: x := 10 *)
Definition simple_assign_ast : stmt :=
  SAssign "x" (EConst (VInt 10%Z)).

(** ** Expected Bytecode *)

(** Manually compiled bytecode *)
Definition simple_assign_code : code :=
  [ILoadInt 10;
   IStoreVar "x";
   IHalt].

(** ** Verification *)

(** Verify bytecode structure *)
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

(** ** Initial VM State *)

Definition simple_assign_vm : vm_state :=
  init_vm_state simple_assign_code [].

(** Verify initial state *)
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

(** ** Step-by-Step Execution Trace (manual) *)

(** Step 1: After loading 10 onto stack *)
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

(** Step 2: After storing to variable x *)
Definition simple_assign_vm_step2_opt : option vm_state :=
  match pop_stack simple_assign_vm_step1 with
  | Some (v, vm') => Some (inc_pc (update_env_vm vm' "x" v))
  | None => None
  end.

Example step2_defined :
  simple_assign_vm_step2_opt <> None.
Proof. discriminate. Qed.

(** Extract the state *)
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

(** Step 3: After halt *)
Definition simple_assign_vm_final : vm_state :=
  halt_vm simple_assign_vm_step2.

Example final_halted :
  is_halted simple_assign_vm_final = true.
Proof. reflexivity. Qed.

Example final_var_x_preserved :
  lookup (vm_env simple_assign_vm_final) "x" = Some (VInt 10%Z).
Proof. reflexivity. Qed.

(** ** Summary *)

(** This example demonstrates that:
    1. We can represent a simple ST assignment as an AST
    2. We can manually compile it to bytecode
    3. We can create a VM state to execute the bytecode
    4. We can manually trace the execution step by step
    5. The final state correctly reflects the assignment

    In later phases, we will:
    - Automate the compilation from AST to bytecode
    - Define formal execution semantics
    - Prove that compilation preserves semantics
*)
