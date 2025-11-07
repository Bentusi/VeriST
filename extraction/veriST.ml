(* VeriST Compiler - Command Line Interface *)

open Printf

(* Command line options *)
type options = {
  input_file: string option;
  output_file: string option;
  verbose: bool;
}

let default_options = {
  input_file = None;
  output_file = None;
  verbose = false;
}

(* Print usage message *)
let print_usage () =
  printf "VeriST Compiler - Verified Structured Text Compiler\n\n";
  printf "Usage: veriST [options]\n\n";
  printf "Options:\n";
  printf "  -c <file>     Input ST source file\n";
  printf "  -o <file>     Output bytecode file (.stbc)\n";
  printf "  -v, --verbose Enable verbose output\n";
  printf "  -h, --help    Show this help message\n\n";
  printf "Example:\n";
  printf "  veriST -c test.st -o test.stbc\n"

(* Parse command line arguments *)
let parse_args () =
  let opts = ref default_options in
  let args = Sys.argv in
  let rec parse i =
    if i >= Array.length args then ()
    else match args.(i) with
      | "-c" when i + 1 < Array.length args ->
          opts := { !opts with input_file = Some args.(i+1) };
          parse (i + 2)
      | "-o" when i + 1 < Array.length args ->
          opts := { !opts with output_file = Some args.(i+1) };
          parse (i + 2)
      | "-v" | "--verbose" ->
          opts := { !opts with verbose = true };
          parse (i + 1)
      | "-h" | "--help" ->
          print_usage ();
          exit 0
      | arg ->
          eprintf "Unknown argument: %s\n" arg;
          print_usage ();
          exit 1
  in
  parse 1;
  !opts

(* Read entire file into string *)
let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* Write a 32-bit integer in little-endian format *)
let write_uint32 oc n =
  output_byte oc (n land 0xFF);
  output_byte oc ((n lsr 8) land 0xFF);
  output_byte oc ((n lsr 16) land 0xFF);
  output_byte oc ((n lsr 24) land 0xFF)

(* Write a 16-bit integer in little-endian format *)
let write_uint16 oc n =
  output_byte oc (n land 0xFF);
  output_byte oc ((n lsr 8) land 0xFF)

(* Write a 64-bit float in little-endian format *)
let write_float64 oc f =
  let bits = Int64.bits_of_float f in
  output_byte oc (Int64.to_int (Int64.logand bits 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 8) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 16) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 24) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 32) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 40) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 48) 0xFFL));
  output_byte oc (Int64.to_int (Int64.logand (Int64.shift_right bits 56) 0xFFL))

(* Write string with length prefix *)
let write_string oc s =
  let len = Stdlib.String.length s in
  write_uint32 oc len;
  Stdlib.String.iter (fun c -> output_byte oc (Char.code c)) s

(* Save constant pool - STVM format: just the values, no type tags *)
let write_constants oc constants =
  Stdlib.List.iter (fun const ->
    match const with
    | Bytecode_builder.CInt n ->
        write_uint32 oc n
    | Bytecode_builder.CBool b ->
        write_uint32 oc (if b then 1 else 0)
    | Bytecode_builder.CReal f ->
        write_float64 oc f
    | Bytecode_builder.CString s ->
        write_string oc s
  ) constants

(* STVM doesn't need variable table in bytecode - variables are referenced by index only *)
let write_variables oc variables =
  (* STVM doesn't serialize variable names/metadata, just count them *)
  ()

(* Save instructions *)
let write_instructions oc instructions =
  Stdlib.List.iter (fun instr ->
    output_byte oc instr.Bytecode_builder.opcode;
    output_byte oc instr.Bytecode_builder.flags;
    write_uint16 oc instr.Bytecode_builder.operand
  ) instructions

(* Save bytecode to file in STVM format *)
let save_bytecode filename code =
  (* Build STVM-compatible bytecode *)
  let builder = Bytecode_builder.create_builder () in
  
  (* Translate all instructions *)
  Stdlib.List.iter (fun instr ->
    ignore (Bytecode_builder.translate_instruction builder instr)
  ) code;
  
  (* Finalize: reorganize constants, add initialization, JMP, and HALT *)
  Bytecode_builder.finalize_bytecode builder;
  
  let constants = Bytecode_builder.get_constants builder in
  let variables = Bytecode_builder.get_variables builder in
  let instructions = Bytecode_builder.get_instructions builder in
  let entry_point = Bytecode_builder.get_entry_point builder in
  
  let oc = open_out_bin filename in
  
  (* STBC File Header *)
  (* Magic number: "STBC" = 0x43425453 in little-endian *)
  write_uint32 oc 0x43425453;
  
  (* Version: 1.0 *)
  write_uint16 oc 1;  (* major *)
  write_uint16 oc 0;  (* minor *)
  
  (* Entry point *)
  write_uint32 oc entry_point;
  
  (* Global variable count *)
  write_uint32 oc (Stdlib.List.length variables);
  
  (* Constant count *)
  write_uint32 oc (Stdlib.List.length constants);
  
  (* Function count *)
  write_uint32 oc 0;  (* No functions yet *)
  
  (* Instruction count *)
  write_uint32 oc (Stdlib.List.length instructions);
  
  (* Library dependency count *)
  write_uint32 oc 0;  (* no dependencies *)
  
  (* Checksum (optional, set to 0 for now) *)
  write_uint32 oc 0;
  
  (* Write constant pool *)
  write_constants oc constants;
  
  (* Write variable table *)
  write_variables oc variables;
  
  (* Write instructions *)
  write_instructions oc instructions;
  
  close_out oc

(* Main compilation function *)
let compile input_file output_file verbose =
  (* Read source file *)
  let source =
    try
      if verbose then printf "Reading source file: %s\n" input_file;
      read_file input_file
    with Sys_error msg ->
      eprintf "Error reading file: %s\n" msg;
      exit 1
  in
  
  (* Lex *)
  if verbose then printf "Lexical analysis...\n";
  let lexbuf = Lexing.from_string source in
  lexbuf.Lexing.lex_curr_p <- {
    lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = input_file
  };
  
  try
    (* Parse *)
    if verbose then printf "Syntax analysis...\n";
    let ast = Parser.program Lexer.token lexbuf in
    
    (* Compile *)
    if verbose then printf "Compiling to bytecode...\n";
    let init_state = CompilerState.init_compiler_state in
    let result_state = Compiler.compile_stmt ast init_state in
    let code = result_state.CompilerState.cs_code in
    
    (* Debug: print first few instructions *)
    if verbose then begin
      printf "Generated %d Coq bytecode instructions:\n" (Stdlib.List.length code);
      let rec print_first n lst =
        match n, lst with
        | 0, _ | _, [] -> ()
        | n, instr::rest ->
            (match instr with
             | Bytecode.ILoadInt v -> printf "  ILoadInt %d\n" v
             | Bytecode.ILoadBool b -> printf "  ILoadBool %b\n" b
             | Bytecode.ILoadVar v -> printf "  ILoadVar ...\n"
             | Bytecode.IStoreVar v -> printf "  IStoreVar ...\n"
             | Bytecode.IAdd -> printf "  IAdd\n"
             | Bytecode.IJmp a -> printf "  IJmp %d\n" a
             | Bytecode.IHalt -> printf "  IHalt\n"
             | _ -> printf "  <other>\n");
            print_first (n-1) rest
      in
      print_first 5 code
    end;
    
    (* Save bytecode *)
    if verbose then printf "Writing bytecode to: %s\n" output_file;
    save_bytecode output_file code;
    
    (* Success *)
    let instr_count = Stdlib.List.length code in
    printf "✓ Compilation successful!\n";
    printf "  Input:  %s\n" input_file;
    printf "  Output: %s\n" output_file;
    printf "  Instructions: %d\n" instr_count;
    0
    
  with
  | Lexer.Lexer_error msg ->
      let pos = (Lexing.lexeme_start_p lexbuf) in
      eprintf "Lexical error at line %d, column %d: %s\n"
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)
        msg;
      1
  | Parsing.Parse_error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      eprintf "Syntax error at line %d, column %d\n"
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1);
      eprintf "  near: %s\n" (Lexing.lexeme lexbuf);
      1
  | e ->
      eprintf "Internal error: %s\n" (Printexc.to_string e);
      Printexc.print_backtrace stderr;
      1

(* Main entry point *)
let () =
  let opts = parse_args () in
  
  match opts.input_file, opts.output_file with
  | None, _ ->
      eprintf "Error: No input file specified\n";
      print_usage ();
      exit 1
  | Some input, None ->
      eprintf "Error: No output file specified\n";
      print_usage ();
      exit 1
  | Some input, Some output ->
      let exit_code = compile input output opts.verbose in
      exit exit_code
