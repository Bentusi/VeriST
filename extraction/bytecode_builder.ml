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
      let stvm_instr = { opcode = 0x1B; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IJz addr -> 
      let stvm_instr = { opcode = 0x1C; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IJnz addr -> 
      let stvm_instr = { opcode = 0x1D; flags = 0x00; operand = addr } in
      add_instruction builder stvm_instr; stvm_instr
  
  | Bytecode.IPop -> 
      let stvm_instr = { opcode = 0x01; flags = 0x00; operand = 0 } in
      add_instruction builder stvm_instr; stvm_instr
  | Bytecode.IHalt -> 
      let stvm_instr = { opcode = 0x20; flags = 0x00; operand = 0 } in
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

(* Pre-initialize constants for all variables *)
(* This ensures initialization constants get lower indices *)
let pre_initialize_constants builder =
  Stdlib.List.iter (fun var ->
    let init_const = match var.var_init with
      | Some c -> c
      | None -> 
          (match var.var_type with
           | 1 -> CInt 0
           | 2 -> CBool false
           | 3 -> CReal 0.0
           | 4 -> CString ""
           | _ -> CInt 0)
    in
    ignore (add_constant builder init_const)
  ) builder.variables

(* Generate variable initialization code *)
let generate_var_init_code builder =
  Stdlib.List.map (fun var ->
    (* Get or create default constant *)
    let init_const = match var.var_init with
      | Some c -> c
      | None -> 
          (* Default values: 0 for INT, false for BOOL, 0.0 for REAL, "" for STRING *)
          (match var.var_type with
           | 1 -> CInt 0
           | 2 -> CBool false
           | 3 -> CReal 0.0
           | 4 -> CString ""
           | _ -> CInt 0)
    in
    let const_idx = add_constant builder init_const in
    (* Find variable index *)
    let var_idx = Stdlib.List.assoc var.var_name builder.var_map in
    (* Return PUSH + STORE pair *)
    [
      { opcode = 0x00; flags = 0x00; operand = const_idx };  (* PUSH #const *)
      { opcode = 0x04; flags = 0x01; operand = var_idx }     (* STORE global var *)
    ]
  ) builder.variables
  |> Stdlib.List.flatten

(* Finalize bytecode: add initialization, JMP, and HALT *)
let finalize_bytecode builder =
  (* Step 0: Reorganize constant pool - initialization constants first *)
  (* Collect initialization constants *)
  let init_constants = Stdlib.List.map (fun var ->
    match var.var_init with
      | Some c -> c
      | None -> 
          (match var.var_type with
           | 1 -> CInt 0
           | 2 -> CBool false
           | 3 -> CReal 0.0
           | 4 -> CString ""
           | _ -> CInt 0)
  ) builder.variables in
  
  (* Build new constant pool: init constants + other constants *)
  let other_constants = Stdlib.List.filter (fun c ->
    not (Stdlib.List.mem c init_constants)
  ) builder.constants in
  let new_constants = init_constants @ other_constants in
  
  (* Build new constant index mapping *)
  let new_const_map = Stdlib.List.mapi (fun i c -> (c, i)) new_constants in
  
  (* Update user instructions with new indices *)
  let remap_operand opcode old_operand =
    if opcode = 0x00 then  (* PUSH - operand is constant index *)
      let old_const = Stdlib.List.nth builder.constants old_operand in
      Stdlib.List.assoc old_const new_const_map
    else
      old_operand
  in
  
  let user_code_remapped = Stdlib.List.map (fun instr ->
    { instr with operand = remap_operand instr.opcode instr.operand }
  ) builder.instructions in
  
  (* Update builder *)
  builder.constants <- new_constants;
  builder.const_map <- new_const_map;
  
  (* Step 1: Save remapped user program instructions *)
  let user_code = user_code_remapped in
  
  (* Step 2: Clear instructions to rebuild *)
  builder.instructions <- [];
  
  (* Step 3: Generate initialization code for all variables *)
  let init_code = generate_var_init_code builder in
  let init_count = Stdlib.List.length init_code in
  
  (* Step 4: Create JMP instruction to skip initialization *)
  let jmp_target = init_count + 1 in  (* +1 for the JMP instruction itself *)
  let jmp_instr = { opcode = 0x1B; flags = 0x00; operand = jmp_target } in
  
  (* Step 5: Add HALT at the end *)
  let halt_instr = { opcode = 0x20; flags = 0x00; operand = 0 } in
  
  (* Step 6: Assemble complete instruction sequence *)
  (* Order: [init_code] [JMP] [user_code] [HALT] *)
  builder.instructions <- init_code @ [jmp_instr] @ user_code @ [halt_instr];
  
  (* Step 7: Set entry point to 0 (start from beginning) *)
  builder.entry_point <- 0;
  
  ()

(* Get entry point *)
let get_entry_point builder = builder.entry_point
