{
(* ST Language Lexer *)
open Parser

exception Lexer_error of string

let keyword_table = Hashtbl.create 53
let _ =
  Stdlib.List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    [
      ("PROGRAM", PROGRAM);
      ("END_PROGRAM", END_PROGRAM);
      ("VAR", VAR);
      ("END_VAR", END_VAR);
      ("IF", IF);
      ("THEN", THEN);
      ("ELSIF", ELSIF);
      ("ELSE", ELSE);
      ("END_IF", END_IF);
      ("WHILE", WHILE);
      ("DO", DO);
      ("END_WHILE", END_WHILE);
      ("FOR", FOR);
      ("TO", TO);
      ("BY", BY);
      ("END_FOR", END_FOR);
      ("CASE", CASE);
      ("OF", OF);
      ("END_CASE", END_CASE);
      ("FUNCTION", FUNCTION);
      ("END_FUNCTION", END_FUNCTION);
      ("RETURN", RETURN);
      ("INT", INT_TYPE);
      ("BOOL", BOOL_TYPE);
      ("REAL", REAL_TYPE);
      ("QINT", QINT_TYPE);
      ("QBOOL", QBOOL_TYPE);
      ("QREAL", QREAL_TYPE);
      ("TRUE", TRUE);
      ("FALSE", FALSE);
      ("AND", AND);
      ("OR", OR);
      ("NOT", NOT);
      ("MOD", MOD);
    ]
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = letter (letter | digit | '_')*
let whitespace = [' ' '\t' '\r']
let newline = '\n' | "\r\n"

rule token = parse
  | whitespace+     { token lexbuf }
  | newline         { Lexing.new_line lexbuf; token lexbuf }
  | "(*"            { comment lexbuf }
  | "//"            { line_comment lexbuf }
  
  (* Delimiters *)
  | ';'             { SEMICOLON }
  | ':'             { COLON }
  | ','             { COMMA }
  | '.'             { DOT }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  
  (* Operators *)
  | ":="            { ASSIGN }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { TIMES }
  | '/'             { DIVIDE }
  
  (* Comparison *)
  | '='             { EQ }
  | "<>"            { NE }
  | '<'             { LT }
  | "<="            { LE }
  | '>'             { GT }
  | ">="            { GE }
  
  (* Numbers *)
  | digit+ as n     { INT (int_of_string n) }
  
  (* Identifiers and keywords *)
  | ident as id     { 
      try Hashtbl.find keyword_table (Stdlib.String.uppercase_ascii id)
      with Not_found -> IDENT id
    }
  
  | eof             { EOF }
  | _ as c          { raise (Lexer_error (Printf.sprintf "Unexpected character: %c" c)) }

and comment = parse
  | "*)"            { token lexbuf }
  | newline         { Lexing.new_line lexbuf; comment lexbuf }
  | eof             { raise (Lexer_error "Unterminated comment") }
  | _               { comment lexbuf }

and line_comment = parse
  | newline         { Lexing.new_line lexbuf; token lexbuf }
  | eof             { EOF }
  | _               { line_comment lexbuf }
