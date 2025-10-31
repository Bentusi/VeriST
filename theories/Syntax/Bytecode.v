(** * Bytecode: Virtual Machine Instruction Set

    This module defines the bytecode instruction set for the
    IEC 61131-3 ST virtual machine, based on STVM design.
*)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Common.Values.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ** Instruction Set *)

(** Bytecode instructions *)
Inductive instr : Type :=
  (* Data manipulation instructions *)
  | ILoadInt : Z -> instr              (** Load integer constant *)
  | ILoadReal : Q -> instr             (** Load real constant *)
  | ILoadBool : bool -> instr          (** Load boolean constant *)
  | ILoadString : string -> instr      (** Load string constant *)
  | ILoadVar : string -> instr         (** Load variable value *)
  | IStoreVar : string -> instr        (** Store value to variable *)
  
  (* Arithmetic instructions *)
  | IAdd : instr                       (** Addition: pop b, pop a, push a+b *)
  | ISub : instr                       (** Subtraction: pop b, pop a, push a-b *)
  | IMul : instr                       (** Multiplication: pop b, pop a, push a*b *)
  | IDiv : instr                       (** Division: pop b, pop a, push a/b *)
  | IMod : instr                       (** Modulo: pop b, pop a, push a mod b *)
  | INeg : instr                       (** Negation: pop a, push -a *)
  
  (* Comparison instructions *)
  | IEq : instr                        (** Equal: pop b, pop a, push a=b *)
  | INe : instr                        (** Not equal: pop b, pop a, push a≠b *)
  | ILt : instr                        (** Less than: pop b, pop a, push a<b *)
  | ILe : instr                        (** Less or equal: pop b, pop a, push a≤b *)
  | IGt : instr                        (** Greater than: pop b, pop a, push a>b *)
  | IGe : instr                        (** Greater or equal: pop b, pop a, push a≥b *)
  
  (* Logical instructions *)
  | IAnd : instr                       (** Logical AND: pop b, pop a, push a∧b *)
  | IOr : instr                        (** Logical OR: pop b, pop a, push a∨b *)
  | INot : instr                       (** Logical NOT: pop a, push ¬a *)
  
  (* Control flow instructions *)
  | IJmp : nat -> instr                (** Unconditional jump to address *)
  | IJz : nat -> instr                 (** Jump if zero (false) *)
  | IJnz : nat -> instr                (** Jump if not zero (true) *)
  
  (* Function call instructions *)
  | ICall : nat -> instr               (** Call function at address *)
  | IRet : instr                       (** Return from function *)
  | ILoadParam : nat -> instr          (** Load parameter by index *)
  | IStoreParam : nat -> instr         (** Store to parameter by index *)
  
  (* Stack manipulation instructions *)
  | IPop : instr                       (** Pop and discard top of stack *)
  | IDup : instr                       (** Duplicate top of stack *)
  
  (* System instructions *)
  | IHalt : instr                      (** Halt execution *)
  | INop : instr.                      (** No operation *)

(** ** Code Representation *)

(** Bytecode program is a list of instructions *)
Definition code := list instr.

(** Address in code *)
Definition address := nat.

(** Label for jump targets (used during compilation) *)
Definition label := nat.

(** ** Instruction Properties *)

(** Check if an instruction is a jump *)
Definition is_jump (i : instr) : bool :=
  match i with
  | IJmp _ | IJz _ | IJnz _ => true
  | _ => false
  end.

(** Check if an instruction is a call *)
Definition is_call (i : instr) : bool :=
  match i with
  | ICall _ => true
  | _ => false
  end.

(** Check if an instruction is a return *)
Definition is_return (i : instr) : bool :=
  match i with
  | IRet => true
  | _ => false
  end.

(** Check if an instruction modifies control flow *)
Definition is_control_flow (i : instr) : bool :=
  is_jump i || is_call i || is_return i.

(** ** Code Access *)

(** Get instruction at address *)
Definition get_instr (c : code) (addr : address) : option instr :=
  nth_error c addr.

(** Code length *)
Definition code_length (c : code) : nat :=
  length c.

(** Check if address is valid *)
Definition valid_address (c : code) (addr : address) : bool :=
  Nat.ltb addr (code_length c).

(** ** Instruction String Representation *)

(** Convert instruction to string (for debugging) *)
Definition instr_to_string (i : instr) : string :=
  match i with
  | ILoadInt n => "LOAD_INT " (* ++ Z.to_string n *)
  | ILoadReal r => "LOAD_REAL"
  | ILoadBool b => if b then "LOAD_BOOL TRUE" else "LOAD_BOOL FALSE"
  | ILoadString s => "LOAD_STRING " ++ s
  | ILoadVar x => "LOAD_VAR " ++ x
  | IStoreVar x => "STORE_VAR " ++ x
  | IAdd => "ADD"
  | ISub => "SUB"
  | IMul => "MUL"
  | IDiv => "DIV"
  | IMod => "MOD"
  | INeg => "NEG"
  | IEq => "EQ"
  | INe => "NE"
  | ILt => "LT"
  | ILe => "LE"
  | IGt => "GT"
  | IGe => "GE"
  | IAnd => "AND"
  | IOr => "OR"
  | INot => "NOT"
  | IJmp addr => "JMP " (* ++ nat_to_string addr *)
  | IJz addr => "JZ " (* ++ nat_to_string addr *)
  | IJnz addr => "JNZ " (* ++ nat_to_string addr *)
  | ICall addr => "CALL " (* ++ nat_to_string addr *)
  | IRet => "RET"
  | ILoadParam n => "LOAD_PARAM " (* ++ nat_to_string n *)
  | IStoreParam n => "STORE_PARAM " (* ++ nat_to_string n *)
  | IPop => "POP"
  | IDup => "DUP"
  | IHalt => "HALT"
  | INop => "NOP"
  end.

(** ** Examples *)

(** Example: Load and add two integers *)
Example ex_add_code : code :=
  [ILoadInt 5;
   ILoadInt 3;
   IAdd;
   IHalt].

(** Example: Simple variable assignment *)
Example ex_assign_code : code :=
  [ILoadInt 10;
   IStoreVar "x";
   IHalt].

(** Example: Conditional jump *)
Example ex_conditional : code :=
  [ILoadVar "x";
   ILoadInt 0;
   IGt;
   IJz 6;        (* Jump to address 6 if false *)
   ILoadInt 1;
   IStoreVar "y";
   IJmp 8;       (* Jump to address 8 *)
   ILoadInt 0;
   IStoreVar "y";
   IHalt].

(** Example: Function call *)
Example ex_function_call : code :=
  [ILoadInt 5;        (* Argument 1 *)
   ILoadInt 3;        (* Argument 2 *)
   ICall 10;          (* Call function at address 10 *)
   IStoreVar "result";
   IHalt;
   (* Function starts at address 10 *)
   INop; INop; INop; INop; INop;
   ILoadParam 0;
   ILoadParam 1;
   IAdd;
   IRet].

(** Properties of example code *)

Example ex_add_code_length : code_length ex_add_code = 4%nat.
Proof. reflexivity. Qed.

Example ex_add_code_first : get_instr ex_add_code 0%nat = Some (ILoadInt 5%Z).
Proof. reflexivity. Qed.

Example ex_add_code_last : get_instr ex_add_code 3%nat = Some IHalt.
Proof. reflexivity. Qed.

Example ex_is_jump_true : is_jump (IJmp 10) = true.
Proof. reflexivity. Qed.

Example ex_is_jump_false : is_jump IAdd = false.
Proof. reflexivity. Qed.

Example ex_valid_addr : valid_address ex_add_code 2%nat = true.
Proof. reflexivity. Qed.

Example ex_invalid_addr : valid_address ex_add_code 10%nat = false.
Proof. reflexivity. Qed.
