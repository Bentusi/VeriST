type token =
  | PROGRAM
  | END_PROGRAM
  | VAR
  | END_VAR
  | IF
  | THEN
  | ELSIF
  | ELSE
  | END_IF
  | WHILE
  | DO
  | END_WHILE
  | FOR
  | TO
  | BY
  | END_FOR
  | CASE
  | OF
  | END_CASE
  | FUNCTION
  | END_FUNCTION
  | RETURN
  | INT_TYPE
  | BOOL_TYPE
  | TRUE
  | FALSE
  | AND
  | OR
  | NOT
  | MOD
  | SEMICOLON
  | COLON
  | COMMA
  | DOT
  | LPAREN
  | RPAREN
  | ASSIGN
  | PLUS
  | MINUS
  | TIMES
  | DIVIDE
  | EQ
  | NE
  | LT
  | LE
  | GT
  | GE
  | INT of (int)
  | IDENT of (string)
  | EOF

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
(* ST Language Parser - ocamlyacc version *)
open Types
open AST
open Values

(* Helper function to convert OCaml string to Coq char list *)
let char_list_of_string s =
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (Stdlib.String.get s i :: acc)
  in
  aux (Stdlib.String.length s - 1) []

let string_to_coq_string s = char_list_of_string s

let parse_error s =
  Printf.eprintf "Parse error: %s\n" s;
  flush stderr
# 75 "parser.ml"
let yytransl_const = [|
  257 (* PROGRAM *);
  258 (* END_PROGRAM *);
  259 (* VAR *);
  260 (* END_VAR *);
  261 (* IF *);
  262 (* THEN *);
  263 (* ELSIF *);
  264 (* ELSE *);
  265 (* END_IF *);
  266 (* WHILE *);
  267 (* DO *);
  268 (* END_WHILE *);
  269 (* FOR *);
  270 (* TO *);
  271 (* BY *);
  272 (* END_FOR *);
  273 (* CASE *);
  274 (* OF *);
  275 (* END_CASE *);
  276 (* FUNCTION *);
  277 (* END_FUNCTION *);
  278 (* RETURN *);
  279 (* INT_TYPE *);
  280 (* BOOL_TYPE *);
  281 (* TRUE *);
  282 (* FALSE *);
  283 (* AND *);
  284 (* OR *);
  285 (* NOT *);
  286 (* MOD *);
  287 (* SEMICOLON *);
  288 (* COLON *);
  289 (* COMMA *);
  290 (* DOT *);
  291 (* LPAREN *);
  292 (* RPAREN *);
  293 (* ASSIGN *);
  294 (* PLUS *);
  295 (* MINUS *);
  296 (* TIMES *);
  297 (* DIVIDE *);
  298 (* EQ *);
  299 (* NE *);
  300 (* LT *);
  301 (* LE *);
  302 (* GT *);
  303 (* GE *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  304 (* INT *);
  305 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\004\000\004\000\005\000\005\000\006\000\
\006\000\003\000\003\000\003\000\008\000\008\000\008\000\008\000\
\009\000\009\000\009\000\010\000\010\000\007\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\000\000"

let yylen = "\002\000\
\005\000\003\000\000\000\001\000\002\000\004\000\006\000\001\000\
\001\000\000\000\001\000\002\000\004\000\006\000\005\000\010\000\
\000\000\005\000\002\000\000\000\002\000\001\000\001\000\001\000\
\001\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\002\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\042\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\002\000\005\000\023\000\024\000\000\000\000\000\000\000\
\022\000\025\000\000\000\000\000\000\000\000\000\001\000\012\000\
\008\000\009\000\000\000\000\000\000\000\041\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\
\000\000\026\000\000\000\000\000\000\000\031\000\000\000\000\000\
\029\000\030\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\013\000\000\000\000\000\000\000\000\000\015\000\
\000\000\007\000\000\000\019\000\014\000\000\000\000\000\000\000\
\000\000\000\000\021\000\000\000\018\000\000\000\016\000"

let yydgoto = "\002\000\
\004\000\007\000\015\000\009\000\010\000\035\000\027\000\016\000\
\079\000\089\000"

let yysindex = "\002\000\
\000\255\000\000\218\254\000\000\010\255\223\254\004\255\242\254\
\032\255\223\254\066\000\066\000\234\254\020\255\052\255\004\255\
\238\254\000\000\000\000\000\000\000\000\066\000\066\000\066\000\
\000\000\000\000\099\255\143\255\022\255\066\000\000\000\000\000\
\000\000\000\000\227\254\161\000\080\000\000\000\004\255\066\000\
\066\000\066\000\066\000\066\000\066\000\066\000\066\000\066\000\
\066\000\066\000\066\000\066\000\004\255\066\000\101\000\000\000\
\066\000\000\000\027\255\161\000\143\000\000\000\033\255\033\255\
\000\000\000\000\028\255\028\255\028\255\028\255\028\255\028\255\
\048\255\164\255\000\000\122\000\066\000\004\255\061\255\000\000\
\066\000\000\000\122\255\000\000\000\000\185\255\004\255\024\255\
\069\255\027\255\000\000\004\255\000\000\067\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\002\255\000\000\082\255\000\000\
\000\000\081\255\000\000\000\000\000\000\000\000\000\000\017\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\227\255\000\000\000\000\023\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\086\255\000\000\000\000\000\000\
\000\000\000\000\090\255\229\255\075\000\000\000\050\255\076\255\
\000\000\000\000\253\255\255\255\023\000\025\000\049\000\051\000\
\000\000\000\000\000\000\000\000\000\000\091\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\095\255\023\255\000\000\
\000\000\090\255\000\000\085\255\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\240\255\092\000\000\000\000\000\254\255\000\000\
\018\000\000\000"

let yytablesize = 464
let yytable = "\032\000\
\003\000\056\000\001\000\003\000\033\000\034\000\003\000\057\000\
\011\000\028\000\005\000\003\000\006\000\012\000\003\000\008\000\
\013\000\017\000\010\000\036\000\037\000\038\000\059\000\010\000\
\010\000\010\000\029\000\055\000\010\000\010\000\010\000\010\000\
\010\000\077\000\078\000\018\000\073\000\060\000\061\000\062\000\
\063\000\064\000\065\000\066\000\067\000\068\000\069\000\070\000\
\071\000\072\000\003\000\074\000\014\000\031\000\076\000\027\000\
\030\000\042\000\054\000\080\000\027\000\084\000\042\000\027\000\
\027\000\043\000\044\000\045\000\046\000\085\000\090\000\091\000\
\045\000\046\000\083\000\094\000\027\000\027\000\086\000\092\000\
\027\000\028\000\095\000\010\000\004\000\027\000\028\000\027\000\
\027\000\028\000\028\000\027\000\027\000\027\000\027\000\027\000\
\027\000\010\000\017\000\010\000\010\000\019\000\028\000\028\000\
\039\000\020\000\028\000\093\000\000\000\000\000\000\000\028\000\
\000\000\028\000\028\000\000\000\000\000\028\000\028\000\028\000\
\028\000\028\000\028\000\000\000\000\000\040\000\041\000\087\000\
\042\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\043\000\044\000\045\000\046\000\047\000\048\000\049\000\050\000\
\051\000\052\000\000\000\000\000\040\000\041\000\000\000\042\000\
\000\000\053\000\000\000\000\000\000\000\000\000\000\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\051\000\
\052\000\040\000\041\000\000\000\042\000\000\000\000\000\000\000\
\000\000\081\000\000\000\000\000\043\000\044\000\045\000\046\000\
\047\000\048\000\049\000\050\000\051\000\052\000\040\000\041\000\
\000\000\042\000\000\000\000\000\000\000\000\000\000\000\088\000\
\000\000\043\000\044\000\045\000\046\000\047\000\048\000\049\000\
\050\000\051\000\052\000\040\000\041\000\000\000\042\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\043\000\044\000\
\045\000\046\000\047\000\048\000\049\000\050\000\051\000\052\000\
\040\000\000\000\038\000\000\000\000\000\040\000\000\000\038\000\
\040\000\040\000\038\000\038\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\040\000\040\000\038\000\
\038\000\040\000\032\000\038\000\033\000\000\000\040\000\032\000\
\038\000\033\000\032\000\032\000\033\000\033\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\
\032\000\033\000\033\000\032\000\034\000\033\000\035\000\000\000\
\032\000\034\000\033\000\035\000\034\000\034\000\035\000\035\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\034\000\034\000\035\000\035\000\034\000\036\000\035\000\
\037\000\000\000\034\000\036\000\035\000\037\000\036\000\036\000\
\037\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\036\000\036\000\037\000\037\000\036\000\
\039\000\037\000\000\000\000\000\036\000\039\000\037\000\000\000\
\039\000\039\000\020\000\021\000\000\000\000\000\022\000\000\000\
\000\000\000\000\000\000\000\000\023\000\000\000\039\000\000\000\
\024\000\039\000\040\000\041\000\000\000\042\000\039\000\000\000\
\000\000\025\000\026\000\058\000\000\000\043\000\044\000\045\000\
\046\000\047\000\048\000\049\000\050\000\051\000\052\000\040\000\
\041\000\000\000\042\000\075\000\000\000\000\000\000\000\000\000\
\000\000\000\000\043\000\044\000\045\000\046\000\047\000\048\000\
\049\000\050\000\051\000\052\000\040\000\041\000\000\000\042\000\
\082\000\000\000\000\000\000\000\000\000\000\000\000\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\051\000\
\052\000\040\000\000\000\000\000\042\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\043\000\044\000\045\000\046\000\
\047\000\048\000\049\000\050\000\051\000\052\000\042\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\043\000\044\000\
\045\000\046\000\047\000\048\000\049\000\050\000\051\000\052\000"

let yycheck = "\016\000\
\001\001\031\001\001\000\002\001\023\001\024\001\005\001\037\001\
\005\001\012\000\049\001\010\001\003\001\010\001\013\001\049\001\
\013\001\032\001\002\001\022\000\023\000\024\000\039\000\007\001\
\008\001\009\001\049\001\030\000\012\001\007\001\008\001\009\001\
\016\001\007\001\008\001\004\001\053\000\040\000\041\000\042\000\
\043\000\044\000\045\000\046\000\047\000\048\000\049\000\050\000\
\051\000\052\000\049\001\054\000\049\001\002\001\057\000\006\001\
\037\001\030\001\037\001\012\001\011\001\078\000\030\001\014\001\
\015\001\038\001\039\001\040\001\041\001\009\001\087\000\048\001\
\040\001\041\001\077\000\092\000\027\001\028\001\081\000\011\001\
\031\001\006\001\016\001\002\001\004\001\036\001\011\001\038\001\
\039\001\014\001\015\001\042\001\043\001\044\001\045\001\046\001\
\047\001\012\001\009\001\009\001\016\001\010\000\027\001\028\001\
\006\001\011\001\031\001\090\000\255\255\255\255\255\255\036\001\
\255\255\038\001\039\001\255\255\255\255\042\001\043\001\044\001\
\045\001\046\001\047\001\255\255\255\255\027\001\028\001\006\001\
\030\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\045\001\
\046\001\047\001\255\255\255\255\027\001\028\001\255\255\030\001\
\255\255\011\001\255\255\255\255\255\255\255\255\255\255\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\045\001\046\001\
\047\001\027\001\028\001\255\255\030\001\255\255\255\255\255\255\
\255\255\014\001\255\255\255\255\038\001\039\001\040\001\041\001\
\042\001\043\001\044\001\045\001\046\001\047\001\027\001\028\001\
\255\255\030\001\255\255\255\255\255\255\255\255\255\255\015\001\
\255\255\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\045\001\046\001\047\001\027\001\028\001\255\255\030\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\045\001\046\001\047\001\
\006\001\255\255\006\001\255\255\255\255\011\001\255\255\011\001\
\014\001\015\001\014\001\015\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\027\001\028\001\027\001\
\028\001\031\001\006\001\031\001\006\001\255\255\036\001\011\001\
\036\001\011\001\014\001\015\001\014\001\015\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\027\001\
\028\001\027\001\028\001\031\001\006\001\031\001\006\001\255\255\
\036\001\011\001\036\001\011\001\014\001\015\001\014\001\015\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\027\001\028\001\027\001\028\001\031\001\006\001\031\001\
\006\001\255\255\036\001\011\001\036\001\011\001\014\001\015\001\
\014\001\015\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\027\001\028\001\027\001\028\001\031\001\
\006\001\031\001\255\255\255\255\036\001\011\001\036\001\255\255\
\014\001\015\001\025\001\026\001\255\255\255\255\029\001\255\255\
\255\255\255\255\255\255\255\255\035\001\255\255\028\001\255\255\
\039\001\031\001\027\001\028\001\255\255\030\001\036\001\255\255\
\255\255\048\001\049\001\036\001\255\255\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\045\001\046\001\047\001\027\001\
\028\001\255\255\030\001\031\001\255\255\255\255\255\255\255\255\
\255\255\255\255\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\045\001\046\001\047\001\027\001\028\001\255\255\030\001\
\031\001\255\255\255\255\255\255\255\255\255\255\255\255\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\045\001\046\001\
\047\001\027\001\255\255\255\255\030\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\038\001\039\001\040\001\041\001\
\042\001\043\001\044\001\045\001\046\001\047\001\030\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\045\001\046\001\047\001"

let yynames_const = "\
  PROGRAM\000\
  END_PROGRAM\000\
  VAR\000\
  END_VAR\000\
  IF\000\
  THEN\000\
  ELSIF\000\
  ELSE\000\
  END_IF\000\
  WHILE\000\
  DO\000\
  END_WHILE\000\
  FOR\000\
  TO\000\
  BY\000\
  END_FOR\000\
  CASE\000\
  OF\000\
  END_CASE\000\
  FUNCTION\000\
  END_FUNCTION\000\
  RETURN\000\
  INT_TYPE\000\
  BOOL_TYPE\000\
  TRUE\000\
  FALSE\000\
  AND\000\
  OR\000\
  NOT\000\
  MOD\000\
  SEMICOLON\000\
  COLON\000\
  COMMA\000\
  DOT\000\
  LPAREN\000\
  RPAREN\000\
  ASSIGN\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIVIDE\000\
  EQ\000\
  NE\000\
  LT\000\
  LE\000\
  GT\000\
  GE\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'var_declarations) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    Obj.repr(
# 55 "parser.mly"
    ( _4 )
# 384 "parser.ml"
               : AST.stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var_list) in
    Obj.repr(
# 59 "parser.mly"
                         ( )
# 391 "parser.ml"
               : 'var_declarations))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "parser.mly"
    ( )
# 397 "parser.ml"
               : 'var_declarations))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var_decl) in
    Obj.repr(
# 64 "parser.mly"
             ( )
# 404 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_list) in
    Obj.repr(
# 65 "parser.mly"
                      ( )
# 412 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_spec) in
    Obj.repr(
# 69 "parser.mly"
                                    ( )
# 420 "parser.ml"
               : 'var_decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'type_spec) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 70 "parser.mly"
                                                      ( )
# 429 "parser.ml"
               : 'var_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
             ( TyInt )
# 435 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
              ( TyBool )
# 441 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
    ( SSkip )
# 447 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 80 "parser.mly"
              ( _1 )
# 454 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statement) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement_list) in
    Obj.repr(
# 81 "parser.mly"
                             ( SSeq (_1, _2) )
# 462 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 86 "parser.mly"
    ( SAssign (string_to_coq_string _1, _3) )
# 470 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'statement_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'else_part) in
    Obj.repr(
# 89 "parser.mly"
    ( SIf (_2, _4, _5) )
# 479 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    Obj.repr(
# 92 "parser.mly"
    ( SWhile (_2, _4) )
# 487 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'expression) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'for_step) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    Obj.repr(
# 95 "parser.mly"
    ( 
      (* Convert FOR to WHILE loop *)
      let var_id = string_to_coq_string _2 in
      let init = SAssign (var_id, _4) in
      let cond = EBinop (OpLe, EVar var_id, _6) in
      let increment = SAssign (var_id, 
        EBinop (OpAdd, EVar var_id, EConst (VInt _7))) in
      let loop_body = SSeq (_9, increment) in
      SSeq (init, SWhile (cond, loop_body))
    )
# 507 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "parser.mly"
    ( SSkip )
# 513 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'else_part) in
    Obj.repr(
# 110 "parser.mly"
    ( SIf (_2, _4, _5) )
# 522 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement_list) in
    Obj.repr(
# 112 "parser.mly"
    ( _2 )
# 529 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    Obj.repr(
# 116 "parser.mly"
    ( 1 )
# 535 "parser.ml"
               : 'for_step))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 117 "parser.mly"
           ( _2 )
# 542 "parser.ml"
               : 'for_step))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 122 "parser.mly"
    ( EConst (VInt _1) )
# 549 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    Obj.repr(
# 125 "parser.mly"
    ( EConst (VBool true) )
# 555 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    Obj.repr(
# 128 "parser.mly"
    ( EConst (VBool false) )
# 561 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 131 "parser.mly"
    ( EVar (string_to_coq_string _1) )
# 568 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 134 "parser.mly"
    ( _2 )
# 575 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 137 "parser.mly"
    ( EBinop (OpAdd, _1, _3) )
# 583 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 140 "parser.mly"
    ( EBinop (OpSub, _1, _3) )
# 591 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 143 "parser.mly"
    ( EBinop (OpMul, _1, _3) )
# 599 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 146 "parser.mly"
    ( EBinop (OpDiv, _1, _3) )
# 607 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 149 "parser.mly"
    ( EBinop (OpMod, _1, _3) )
# 615 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 152 "parser.mly"
    ( EBinop (OpEq, _1, _3) )
# 623 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 155 "parser.mly"
    ( EBinop (OpNe, _1, _3) )
# 631 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 158 "parser.mly"
    ( EBinop (OpLt, _1, _3) )
# 639 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 161 "parser.mly"
    ( EBinop (OpLe, _1, _3) )
# 647 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 164 "parser.mly"
    ( EBinop (OpGt, _1, _3) )
# 655 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 167 "parser.mly"
    ( EBinop (OpGe, _1, _3) )
# 663 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 170 "parser.mly"
    ( EBinop (OpAnd, _1, _3) )
# 671 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 173 "parser.mly"
    ( EBinop (OpOr, _1, _3) )
# 679 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 176 "parser.mly"
    ( EUnop (OpNot, _2) )
# 686 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 179 "parser.mly"
    ( EUnop (OpNeg, _2) )
# 693 "parser.ml"
               : 'expression))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : AST.stmt)
