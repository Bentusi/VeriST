(* Bytecode Builder - STVM Compatible Bytecode Generation *)

open Printf

(* Constant types *)
type constant =
  | CInt of int
  | CBool of bool
  | CReal of float
  | CString of string

(* Variable entry *)
type var_entry = {
  var_name: string;
  var_type: int;  (* 1=INT, 2=BOOL, 3=REAL, 4=STRING *)
  var_init: constant option;
}

(* STVM instruction representation *)
type stvm_instruction = {
  opcode: int;
  flags: int;
  operand: int;
}

(* Bytecode builder state *)
type bytecode_builder = {
  mutable constants: constant list;
  mutable const_map: (constant * int) list;  (* map constant to index *)
  mutable variables: var_entry list;
  mutable var_map: (string * int) list;  (* map var name to index *)
  mutable instructions: stvm_instruction list;
  mutable entry_point: int;
}

(* Create a new bytecode builder *)
let create_builder () = {
  constants = [];
  const_map = [];
  variables = [];
  var_map = [];
  instructions = [];
  entry_point = 0;
}

(* Add constant to pool, return its index *)
let add_constant builder const =
  try
    Stdlib.List.assoc const builder.const_map
  with Not_found ->
    let idx = Stdlib.List.length builder.constants in
    builder.constants <- builder.constants @ [const];
    builder.const_map <- (const, idx) :: builder.const_map;
    idx

(* Add variable to table, return its index *)
let add_variable builder name var_type init_val =
  try
    Stdlib.List.assoc name builder.var_map
  with Not_found ->
    let idx = Stdlib.List.length builder.variables in
    let entry = {
      var_name = name;
      var_type = var_type;
      var_init = init_val;
    } in
    builder.variables <- builder.variables @ [entry];
    builder.var_map <- (name, idx) :: builder.var_map;
    idx

(* Get variable index by name *)
let get_var_index builder name =
  try
    Some (Stdlib.List.assoc name builder.var_map)
  with Not_found -> None

(* Add instruction *)
let add_instruction builder instr =
  builder.instructions <- builder.instructions @ [instr]

(* Convert Bytecode instruction to STVM opcode and operand *)
let translate_instruction builder instr =
  match instr with
  | Bytecode.ILoadInt n ->
      let const_idx = add_constant builder (CInt n) in
      let stvm_instr = { opcode = 0x00; flags = 0x00; operand = const_idx } in
      add_instruction builder stvm_instr;
      stvm_instr  (* OP_PUSH *)
      
  | Bytecode.ILoadBool b ->
      let const_idx = add_constant builder (CBool b) in
      let stvm_instr = { opcode = 0x00; flags = 0x00; operand = const_idx } in
      add_instruction builder stvm_instr;
      stvm_instr  (* OP_PUSH *)
      
  | Bytecode.ILoadVar v ->
      let var_name = Stdlib.String.concat "" (Stdlib.List.map (Stdlib.String.make 1) v) in
      let idx = (match get_var_index builder var_name with
       | Some i -> i
       | None -> add_variable builder var_name 1 None) in
      let stvm_instr = { opcode = 0x03; flags = 0x01; operand = idx } in
      add_instruction builder stvm_instr;
      stvm_instr  (* OP_LOAD, FLAG_GLOBAL *)
      
  | Bytecode.IStoreVar v ->
      let var_name = Stdlib.String.concat "" (Stdlib.List.map (Stdlib.String.make 1) v) in
      let idx = (match get_var_index builder var_name with
       | Some i -> i
       | None -> add_variable builder var_name 1 None) in
      let stvm_instr = { opcode = 0x04; flags = 0x01; operand = idx } in
      add_instruction builder stvm_instr;
      stvm_instr  (* OP_STORE, FLAG_GLOBAL *)
      
  | Bytecode.IAdd -> 
      let stvm_instr = { opcode = 0x05; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.ISub -> 
      let stvm_instr = { opcode = 0x06; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IMul -> 
      let stvm_instr = { opcode = 0x07; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IDiv -> 
      let stvm_instr = { opcode = 0x08; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IMod -> 
      let stvm_instr = { opcode = 0x09; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.INeg -> 
      let stvm_instr = { opcode = 0x0A; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  
  | Bytecode.IEq -> 
      let stvm_instr = { opcode = 0x0B; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.INe -> 
      let stvm_instr = { opcode = 0x0C; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.ILt -> 
      let stvm_instr = { opcode = 0x0D; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.ILe -> 
      let stvm_instr = { opcode = 0x0E; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IGt -> 
      let stvm_instr = { opcode = 0x0F; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IGe -> 
      let stvm_instr = { opcode = 0x10; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  
  | Bytecode.IAnd -> 
      let stvm_instr = { opcode = 0x11; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IOr -> 
      let stvm_instr = { opcode = 0x12; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.INot -> 
      let stvm_instr = { opcode = 0x13; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  
  | Bytecode.IJmp addr -> 
      let stvm_instr = { opcode = 0x18; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IJz addr -> 
      let stvm_instr = { opcode = 0x19; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IJnz addr -> 
      let stvm_instr = { opcode = 0x1A; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  
  | Bytecode.IPop -> 
      let stvm_instr = { opcode = 0x01; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IHalt -> 
      let stvm_instr = { opcode = 0x1D; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  
  | _ -> 
      let stvm_instr = { opcode = 0x1F; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr  (* OP_NOP *)

(* Get constant pool data - in original order *)
let get_constants builder = builder.constants

(* Get variable table data - in original order *)
let get_variables builder = builder.variables

(* Get instruction count *)
let get_instruction_count builder = Stdlib.List.length builder.instructions

(* Get all instructions - in original order *)
let get_instructions builder = builder.instructions
