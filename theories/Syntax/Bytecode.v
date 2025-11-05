(** * Bytecode: 虚拟机指令集

    本模块定义 IEC 61131-3 ST 虚拟机的字节码指令集，
    基于 STVM 设计。
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

(** ** 指令集 *)

(** 字节码指令 *)
Inductive instr : Type :=
  (* 数据操作指令 *)
  | ILoadInt : Z -> instr              (** 加载整数常量 *)
  | ILoadReal : Q -> instr             (** 加载实数常量 *)
  | ILoadBool : bool -> instr          (** 加载布尔常量 *)
  | ILoadString : string -> instr      (** 加载字符串常量 *)
  | ILoadVar : string -> instr         (** 加载变量值 *)
  | IStoreVar : string -> instr        (** 存储值到变量 *)
  
  (* 算术指令 *)
  | IAdd : instr                       (** 加法: 弹出 b, 弹出 a, 压入 a+b *)
  | ISub : instr                       (** 减法: 弹出 b, 弹出 a, 压入 a-b *)
  | IMul : instr                       (** 乘法: 弹出 b, 弹出 a, 压入 a*b *)
  | IDiv : instr                       (** 除法: 弹出 b, 弹出 a, 压入 a/b *)
  | IMod : instr                       (** 取模: 弹出 b, 弹出 a, 压入 a mod b *)
  | INeg : instr                       (** 取负: 弹出 a, 压入 -a *)
  
  (* 比较指令 *)
  | IEq : instr                        (** 等于: 弹出 b, 弹出 a, 压入 a=b *)
  | INe : instr                        (** 不等于: 弹出 b, 弹出 a, 压入 a≠b *)
  | ILt : instr                        (** 小于: 弹出 b, 弹出 a, 压入 a<b *)
  | ILe : instr                        (** 小于等于: 弹出 b, 弹出 a, 压入 a≤b *)
  | IGt : instr                        (** 大于: 弹出 b, 弹出 a, 压入 a>b *)
  | IGe : instr                        (** 大于等于: 弹出 b, 弹出 a, 压入 a≥b *)
  
  (* 逻辑指令 *)
  | IAnd : instr                       (** 逻辑与: 弹出 b, 弹出 a, 压入 a∧b *)
  | IOr : instr                        (** 逻辑或: 弹出 b, 弹出 a, 压入 a∨b *)
  | INot : instr                       (** 逻辑非: 弹出 a, 压入 ¬a *)
  
  (* 控制流指令 *)
  | IJmp : nat -> instr                (** 无条件跳转到地址 *)
  | IJz : nat -> instr                 (** 如果为零（假）则跳转 *)
  | IJnz : nat -> instr                (** 如果非零（真）则跳转 *)
  
  (* 函数调用指令 *)
  | ICall : nat -> instr               (** 调用地址处的函数 *)
  | IRet : instr                       (** 从函数返回 *)
  | ILoadParam : nat -> instr          (** 按索引加载参数 *)
  | IStoreParam : nat -> instr         (** 按索引存储到参数 *)
  
  (* 栈操作指令 *)
  | IPop : instr                       (** 弹出并丢弃栈顶 *)
  | IDup : instr                       (** 复制栈顶 *)
  
  (* 系统指令 *)
  | IHalt : instr                      (** 停止执行 *)
  | INop : instr.                      (** 空操作 *)

(** ** 代码表示 *)

(** 字节码程序是指令列表 *)
Definition code := list instr.

(** 代码中的地址 *)
Definition address := nat.

(** 跳转目标标签（编译时使用） *)
Definition label := nat.

(** 指令属性 *)

(** 检查指令是否为跳转 *)
Definition is_jump (i : instr) : bool :=
  match i with
  | IJmp _ | IJz _ | IJnz _ => true
  | _ => false
  end.

(** 检查指令是否为调用 *)
Definition is_call (i : instr) : bool :=
  match i with
  | ICall _ => true
  | _ => false
  end.

(** 检查指令是否为返回 *)
Definition is_return (i : instr) : bool :=
  match i with
  | IRet => true
  | _ => false
  end.

(** 检查指令是否修改控制流 *)
Definition is_control_flow (i : instr) : bool :=
  is_jump i || is_call i || is_return i.

(** ** 代码访问 *)

(** 获取地址处的指令 *)
Definition get_instr (c : code) (addr : address) : option instr :=
  nth_error c addr.

(** 代码长度 *)
Definition code_length (c : code) : nat :=
  length c.

(** 检查地址是否有效 *)
Definition valid_address (c : code) (addr : address) : bool :=
  Nat.ltb addr (code_length c).

(** ** 指令字符串表示 *)

(** 将指令转换为字符串（用于调试） *)
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

(** ** 示例 *)

(** 示例：加载并相加两个整数 *)
Example ex_add_code : code :=
  [ILoadInt 5;
   ILoadInt 3;
   IAdd;
   IHalt].

(** 示例：简单变量赋值 *)
Example ex_assign_code : code :=
  [ILoadInt 10;
   IStoreVar "x";
   IHalt].

(** 示例：条件跳转 *)
Example ex_conditional : code :=
  [ILoadVar "x";
   ILoadInt 0;
   IGt;
   IJz 6;        (* 如果为假则跳转到地址 6 *)
   ILoadInt 1;
   IStoreVar "y";
   IJmp 8;       (* 跳转到地址 8 *)
   ILoadInt 0;
   IStoreVar "y";
   IHalt].

(** 示例：函数调用 *)
Example ex_function_call : code :=
  [ILoadInt 5;        (* 参数 1 *)
   ILoadInt 3;        (* 参数 2 *)
   ICall 10;          (* 调用地址 10 处的函数 *)
   IStoreVar "result";
   IHalt;
   (* 函数从地址 10 开始 *)
   INop; INop; INop; INop; INop;
   ILoadParam 0;
   ILoadParam 1;
   IAdd;
   IRet].

(** 示例代码的属性 *)

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
