(** * VM: Virtual Machine State and Operations

    本模块定义 the state of the virtual machine that executes
    bytecode generated from IEC 61131-3 ST programs.

    © 2024 JIANG Wei <jiangwey@outlook.com> 
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.
Require Import STCompiler.Common.Environment.
Require Import STCompiler.Syntax.Bytecode.

Import ListNotations.
Open Scope string_scope.

(** ** Stack *)

(** Operand stack *)
Definition stack := list value.

(** Stack operations *)
Definition stack_push (s : stack) (v : value) : stack :=
  v :: s.

Definition stack_pop (s : stack) : option (value * stack) :=
  match s with
  | [] => None
  | v :: s' => Some (v, s')
  end.

Definition stack_peek (s : stack) : option value :=
  match s with
  | [] => None
  | v :: _ => Some v
  end.

(** ** Call Frame *)

(** Call frame for function calls *)
Record call_frame : Type := mkCallFrame {
  cf_return_addr : address;      (** Return address *)
  cf_base_pointer : nat;         (** Base pointer for local variables *)
  cf_local_env : env             (** Local variable environment *)
}.

(** ** Function Information *)

(** Function metadata *)
Record function_info : Type := mkFunctionInfo {
  fi_name : string;              (** Function name *)
  fi_address : address;          (** Entry point address *)
  fi_param_count : nat;          (** Number of parameters *)
  fi_return_type : ty            (** Return type *)
}.

(** Function table *)
Definition function_table := list function_info.

(** Lookup function by name *)
Fixpoint lookup_function (ft : function_table) (name : string) : option function_info :=
  match ft with
  | [] => None
  | f :: fs => if String.eqb (fi_name f) name 
               then Some f 
               else lookup_function fs name
  end.

(** Lookup function by address *)
Fixpoint lookup_function_by_addr (ft : function_table) (addr : address) : option function_info :=
  match ft with
  | [] => None
  | f :: fs => if Nat.eqb (fi_address f) addr
               then Some f
               else lookup_function_by_addr fs addr
  end.

(** ** Virtual Machine State *)

(** Complete VM state *)
Record vm_state : Type := mkVMState {
  vm_code : code;                (** Bytecode program *)
  vm_pc : address;               (** Program counter *)
  vm_stack : stack;              (** Operand stack *)
  vm_env : env;                  (** Global variable environment *)
  vm_frames : list call_frame;   (** Call frame stack *)
  vm_functions : function_table; (** Function table *)
  vm_halted : bool               (** Halt flag *)
}.

(** ** Initial VM State *)

(** Create initial VM state *)
Definition init_vm_state (c : code) (funcs : function_table) : vm_state :=
  {| vm_code := c;
     vm_pc := 0%nat;
     vm_stack := [];
     vm_env := empty;
     vm_frames := [];
     vm_functions := funcs;
     vm_halted := false |}.

(** ** VM State Queries *)

(** Check if VM is halted *)
Definition is_halted (vm : vm_state) : bool :=
  vm.(vm_halted).

(** Get current instruction *)
Definition current_instr (vm : vm_state) : option instr :=
  get_instr vm.(vm_code) vm.(vm_pc).

(** Check if PC is valid *)
Definition valid_pc (vm : vm_state) : bool :=
  valid_address vm.(vm_code) vm.(vm_pc).

(** Stack size *)
Definition stack_size (vm : vm_state) : nat :=
  length vm.(vm_stack).

(** Frame depth *)
Definition frame_depth (vm : vm_state) : nat :=
  length vm.(vm_frames).

(** ** VM State Updates *)

(** Increment program counter *)
Definition inc_pc (vm : vm_state) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := S vm.(vm_pc);
     vm_stack := vm.(vm_stack);
     vm_env := vm.(vm_env);
     vm_frames := vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := vm.(vm_halted) |}.

(** Set program counter *)
Definition set_pc (vm : vm_state) (addr : address) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := addr;
     vm_stack := vm.(vm_stack);
     vm_env := vm.(vm_env);
     vm_frames := vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := vm.(vm_halted) |}.

(** Push value onto stack *)
Definition push_stack (vm : vm_state) (v : value) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := vm.(vm_pc);
     vm_stack := stack_push vm.(vm_stack) v;
     vm_env := vm.(vm_env);
     vm_frames := vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := vm.(vm_halted) |}.

(** Pop value from stack *)
Definition pop_stack (vm : vm_state) : option (value * vm_state) :=
  match stack_pop vm.(vm_stack) with
  | None => None
  | Some (v, s') => 
      Some (v, {| vm_code := vm.(vm_code);
                  vm_pc := vm.(vm_pc);
                  vm_stack := s';
                  vm_env := vm.(vm_env);
                  vm_frames := vm.(vm_frames);
                  vm_functions := vm.(vm_functions);
                  vm_halted := vm.(vm_halted) |})
  end.

(** Update environment *)
Definition update_env_vm (vm : vm_state) (x : string) (v : value) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := vm.(vm_pc);
     vm_stack := vm.(vm_stack);
     vm_env := update vm.(vm_env) x v;
     vm_frames := vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := vm.(vm_halted) |}.

(** Halt VM *)
Definition halt_vm (vm : vm_state) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := vm.(vm_pc);
     vm_stack := vm.(vm_stack);
     vm_env := vm.(vm_env);
     vm_frames := vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := true |}.

(** ** Frame Operations *)

(** Push call frame *)
Definition push_frame (vm : vm_state) (frame : call_frame) : vm_state :=
  {| vm_code := vm.(vm_code);
     vm_pc := vm.(vm_pc);
     vm_stack := vm.(vm_stack);
     vm_env := vm.(vm_env);
     vm_frames := frame :: vm.(vm_frames);
     vm_functions := vm.(vm_functions);
     vm_halted := vm.(vm_halted) |}.

(** Pop call frame *)
Definition pop_frame (vm : vm_state) : option (call_frame * vm_state) :=
  match vm.(vm_frames) with
  | [] => None
  | f :: fs => 
      Some (f, {| vm_code := vm.(vm_code);
                  vm_pc := vm.(vm_pc);
                  vm_stack := vm.(vm_stack);
                  vm_env := vm.(vm_env);
                  vm_frames := fs;
                  vm_functions := vm.(vm_functions);
                  vm_halted := vm.(vm_halted) |})
  end.

(** ** Properties *)

(** Halted VM stays halted *)
Lemma halted_stays_halted : forall vm,
  is_halted vm = true ->
  is_halted (inc_pc vm) = true.
Proof.
  intros vm H.
  unfold is_halted, inc_pc in *.
  simpl. assumption.
Qed.

(** Push-pop identity *)
(* Note: This axiom states that pushing then popping returns the original value
   and restores the VM stack to its original state *)
Axiom push_pop_identity : forall vm v,
  pop_stack (push_stack vm v) = Some (v, vm).

(** Stack size after push *)
Lemma stack_size_push : forall vm v,
  stack_size (push_stack vm v) = S (stack_size vm).
Proof.
  intros vm v.
  unfold stack_size, push_stack, stack_push.
  simpl. reflexivity.
Qed.

(** ** 示例 *)

Example ex_init_vm : vm_state :=
  init_vm_state [ILoadInt 5%Z; IHalt] [].

Example ex_init_halted : is_halted ex_init_vm = false.
Proof. reflexivity. Qed.

Example ex_init_pc : (vm_pc ex_init_vm) = 0%nat.
Proof. reflexivity. Qed.

Example ex_push_value : 
  vm_stack (push_stack ex_init_vm (VInt 42%Z)) = [VInt 42%Z].
Proof. reflexivity. Qed.

Example ex_pop_value :
  let vm' := push_stack ex_init_vm (VInt 42%Z) in
  pop_stack vm' = Some (VInt 42%Z, ex_init_vm).
Proof. reflexivity. Qed.

Example ex_inc_pc :
  vm_pc (inc_pc ex_init_vm) = 1%nat.
Proof. reflexivity. Qed.

Example ex_current_instr :
  current_instr ex_init_vm = Some (ILoadInt 5%Z).
Proof. reflexivity. Qed.
