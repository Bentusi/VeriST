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

(* Save bytecode to file in STVM format *)
let save_bytecode filename code =
  let oc = open_out_bin filename in
  
  (* Write instruction count (4 bytes, little-endian) *)
  let code_len = Stdlib.List.length code in
  output_byte oc (code_len land 0xFF);
  output_byte oc ((code_len lsr 8) land 0xFF);
  output_byte oc ((code_len lsr 16) land 0xFF);
  output_byte oc ((code_len lsr 24) land 0xFF);
  
  (* Write instructions *)
  let rec write_instructions = function
    | [] -> ()
    | instr :: rest ->
        (match instr with
         | Bytecode.ILoadInt n ->
             output_byte oc 0x01;
             (* Write 4-byte integer, little-endian *)
             output_byte oc (n land 0xFF);
             output_byte oc ((n lsr 8) land 0xFF);
             output_byte oc ((n lsr 16) land 0xFF);
             output_byte oc ((n lsr 24) land 0xFF)
         | Bytecode.ILoadBool b ->
             output_byte oc 0x02;
             output_byte oc (if b then 1 else 0)
         | Bytecode.ILoadVar v ->
             output_byte oc 0x05;
             (* Write variable name length and chars *)
             let len = Stdlib.List.length v in
             output_byte oc len;
             Stdlib.List.iter (fun c -> output_byte oc (Char.code c)) v
         | Bytecode.IStoreVar v ->
             output_byte oc 0x06;
             let len = Stdlib.List.length v in
             output_byte oc len;
             Stdlib.List.iter (fun c -> output_byte oc (Char.code c)) v
         | Bytecode.IAdd -> output_byte oc 0x10
         | Bytecode.ISub -> output_byte oc 0x11
         | Bytecode.IMul -> output_byte oc 0x12
         | Bytecode.IDiv -> output_byte oc 0x13
         | Bytecode.IMod -> output_byte oc 0x14
         | Bytecode.INeg -> output_byte oc 0x15
         | Bytecode.IEq -> output_byte oc 0x20
         | Bytecode.INe -> output_byte oc 0x21
         | Bytecode.ILt -> output_byte oc 0x22
         | Bytecode.ILe -> output_byte oc 0x23
         | Bytecode.IGt -> output_byte oc 0x24
         | Bytecode.IGe -> output_byte oc 0x25
         | Bytecode.IAnd -> output_byte oc 0x30
         | Bytecode.IOr -> output_byte oc 0x31
         | Bytecode.INot -> output_byte oc 0x32
         | Bytecode.IJmp addr ->
             output_byte oc 0x40;
             output_byte oc (addr land 0xFF);
             output_byte oc ((addr lsr 8) land 0xFF);
             output_byte oc ((addr lsr 16) land 0xFF);
             output_byte oc ((addr lsr 24) land 0xFF)
         | Bytecode.IJz addr ->
             output_byte oc 0x41;
             output_byte oc (addr land 0xFF);
             output_byte oc ((addr lsr 8) land 0xFF);
             output_byte oc ((addr lsr 16) land 0xFF);
             output_byte oc ((addr lsr 24) land 0xFF)
         | Bytecode.IJnz addr ->
             output_byte oc 0x42;
             output_byte oc (addr land 0xFF);
             output_byte oc ((addr lsr 8) land 0xFF);
             output_byte oc ((addr lsr 16) land 0xFF);
             output_byte oc ((addr lsr 24) land 0xFF)
         | Bytecode.IPop -> output_byte oc 0x60
         | Bytecode.IHalt -> output_byte oc 0xFF
        );
        write_instructions rest
  in
  write_instructions code;
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
