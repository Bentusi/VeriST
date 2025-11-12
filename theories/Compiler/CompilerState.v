(** * CompilerState: 编译器状态管理

    本模块定义编译器的状态单子和工具函数。
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import STCompiler.Common.Types.
Require Import STCompiler.Syntax.AST.
Require Import STCompiler.Syntax.Bytecode.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** ** 编译器状态 *)

(** 标签类型 *)
Definition label := nat.

(** 编译器状态：跟踪代码生成过程 *)
Record compiler_state : Type := mkCompilerState {
  cs_code : code;                              (** 生成的字节码 *)
  cs_next_label : label;                       (** 下一个可用标签 *)
  cs_function_table : list (string * address)  (** 函数名到地址映射 *)
}.

(** 初始编译器状态 *)
Definition init_compiler_state : compiler_state :=
  {| cs_code := nil;
     cs_next_label := 0%nat;
     cs_function_table := nil |}.

(** ** 基本操作 *)

(** 发出一条指令 *)
Definition emit (cs : compiler_state) (i : instr) : compiler_state :=
  {| cs_code := cs.(cs_code) ++ [i];
     cs_next_label := cs.(cs_next_label);
     cs_function_table := cs.(cs_function_table) |}.

(** 获取当前代码地址 *)
Definition current_address (cs : compiler_state) : address :=
  length cs.(cs_code).

(** 分配新标签 *)
Definition alloc_label (cs : compiler_state) : compiler_state * label :=
  let l := cs.(cs_next_label) in
  ({| cs_code := cs.(cs_code);
      cs_next_label := S l;
      cs_function_table := cs.(cs_function_table) |}, l).

(** 添加函数到函数表 *)
Definition add_function (cs : compiler_state) (name : string) (addr : address) : compiler_state :=
  {| cs_code := cs.(cs_code);
     cs_next_label := cs.(cs_next_label);
     cs_function_table := (name, addr) :: cs.(cs_function_table) |}.

(** 查找函数地址 *)
Fixpoint lookup_function (table : list (string * address)) (name : string) : option address :=
  match table with
  | nil => None
  | (n, addr) :: rest =>
      if String.eqb n name then Some addr
      else lookup_function rest name
  end.

(** 批量发出指令 *)
Fixpoint emit_list (cs : compiler_state) (instrs : list instr) : compiler_state :=
  match instrs with
  | nil => cs
  | i :: rest => emit_list (emit cs i) rest
  end.

(** emit_list 将指令列表追加到代码末尾 *)
Lemma emit_list_code : forall instrs cs,
  cs_code (emit_list cs instrs) = (cs_code cs ++ instrs)%list.
Proof.
  induction instrs as [|i rest IH]; intros cs; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. unfold emit. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.

(** ** 标签和跳转处理 *)

(** 临时指令类型：用于处理向前跳转 *)
Inductive temp_instr : Type :=
  | TIInstr : instr -> temp_instr           (** 普通指令 *)
  | TILabel : label -> temp_instr           (** 标签占位符 *)
  | TIJumpLabel : label -> temp_instr       (** 跳转到标签 *)
  | TIJzLabel : label -> temp_instr         (** 条件跳转（零时）到标签 *)
  | TIJnzLabel : label -> temp_instr.       (** 条件跳转（非零时）到标签 *)

(** 临时代码 *)
Definition temp_code := list temp_instr.

(** 解析标签：将临时代码转换为实际字节码 *)
Fixpoint resolve_labels_helper (tc : temp_code) (addr : nat) 
                                (label_map : list (label * address)) : list (label * address) :=
  match tc with
  | nil => label_map
  | TILabel l :: rest => 
      resolve_labels_helper rest addr ((l, addr) :: label_map)
  | _ :: rest => 
      resolve_labels_helper rest (S addr) label_map
  end.

(** 查找标签对应的地址 *)
Fixpoint find_label_addr (label_map : list (label * address)) (l : label) : option address :=
  match label_map with
  | nil => None
  | (lbl, addr) :: rest =>
      if Nat.eqb lbl l then Some addr
      else find_label_addr rest l
  end.

(** 将临时指令转换为实际指令 *)
Definition temp_to_instr (ti : temp_instr) (label_map : list (label * address)) : option instr :=
  match ti with
  | TIInstr i => Some i
  | TILabel _ => None  (* 标签不生成指令 *)
  | TIJumpLabel l =>
      match find_label_addr label_map l with
      | Some addr => Some (IJmp addr)
      | None => None
      end
  | TIJzLabel l =>
      match find_label_addr label_map l with
      | Some addr => Some (IJz addr)
      | None => None
      end
  | TIJnzLabel l =>
      match find_label_addr label_map l with
      | Some addr => Some (IJnz addr)
      | None => None
      end
  end.

(** 过滤并转换临时代码 *)
Fixpoint convert_temp_code (tc : temp_code) (label_map : list (label * address)) : code :=
  match tc with
  | nil => nil
  | ti :: rest =>
      match temp_to_instr ti label_map with
      | Some i => i :: convert_temp_code rest label_map
      | None => convert_temp_code rest label_map
      end
  end.

(** 解析标签：主函数 *)
Definition resolve_labels (tc : temp_code) : code :=
  let label_map := resolve_labels_helper tc 0 nil in
  convert_temp_code tc label_map.

(** ** 辅助函数 *)

(** 将 binop 转换为指令 *)
Definition binop_to_instr (op : binop) : instr :=
  match op with
  | OpAdd => IAdd
  | OpSub => ISub
  | OpMul => IMul
  | OpDiv => IDiv
  | OpMod => IMod
  | OpEq => IEq
  | OpNe => INe
  | OpLt => ILt
  | OpLe => ILe
  | OpGt => IGt
  | OpGe => IGe
  | OpAnd => IAnd
  | OpOr => IOr
  end.

(** 将 unop 转换为指令 *)
Definition unop_to_instr (op : unop) : instr :=
  match op with
  | OpNeg => INeg
  | OpNot => INot
  end.
