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
  | REAL_TYPE
  | QINT_TYPE
  | QBOOL_TYPE
  | QREAL_TYPE
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
# 79 "parser.ml"
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
  281 (* REAL_TYPE *);
  282 (* QINT_TYPE *);
  283 (* QBOOL_TYPE *);
  284 (* QREAL_TYPE *);
  285 (* TRUE *);
  286 (* FALSE *);
  287 (* AND *);
  288 (* OR *);
  289 (* NOT *);
  290 (* MOD *);
  291 (* SEMICOLON *);
  292 (* COLON *);
  293 (* COMMA *);
  294 (* DOT *);
  295 (* LPAREN *);
  296 (* RPAREN *);
  297 (* ASSIGN *);
  298 (* PLUS *);
  299 (* MINUS *);
  300 (* TIMES *);
  301 (* DIVIDE *);
  302 (* EQ *);
  303 (* NE *);
  304 (* LT *);
  305 (* LE *);
  306 (* GT *);
  307 (* GE *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  308 (* INT *);
  309 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\004\000\004\000\005\000\005\000\006\000\
\006\000\006\000\006\000\006\000\006\000\003\000\003\000\003\000\
\008\000\008\000\008\000\008\000\009\000\009\000\009\000\010\000\
\010\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\007\000\007\000\007\000\007\000\007\000\000\000"

let yylen = "\002\000\
\005\000\003\000\000\000\001\000\002\000\004\000\006\000\001\000\
\001\000\001\000\001\000\001\000\001\000\000\000\001\000\002\000\
\004\000\006\000\005\000\010\000\000\000\005\000\002\000\000\000\
\002\000\001\000\001\000\001\000\001\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\046\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\002\000\005\000\027\000\028\000\000\000\000\000\000\000\
\026\000\029\000\000\000\000\000\000\000\000\000\001\000\016\000\
\008\000\009\000\010\000\011\000\012\000\013\000\000\000\000\000\
\000\000\045\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\000\000\030\000\000\000\000\000\
\000\000\035\000\000\000\000\000\033\000\034\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\017\000\000\000\
\000\000\000\000\000\000\019\000\000\000\007\000\000\000\023\000\
\018\000\000\000\000\000\000\000\000\000\000\000\025\000\000\000\
\022\000\000\000\020\000"

let yydgoto = "\002\000\
\004\000\007\000\015\000\009\000\010\000\039\000\027\000\016\000\
\083\000\093\000"

let yysindex = "\005\000\
\012\255\000\000\219\254\000\000\023\255\232\254\004\255\022\255\
\026\255\232\254\050\000\050\000\008\255\021\255\061\255\004\255\
\134\255\000\000\000\000\000\000\000\000\050\000\050\000\050\000\
\000\000\000\000\100\255\144\255\029\255\050\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\226\254\245\254\
\065\000\000\000\004\255\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
\004\255\050\000\086\000\000\000\050\000\000\000\017\255\245\254\
\128\000\000\000\230\254\230\254\000\000\000\000\095\255\095\255\
\095\255\095\255\095\255\095\255\052\255\165\255\000\000\107\000\
\050\000\004\255\062\255\000\000\050\000\000\000\122\255\000\000\
\000\000\186\255\004\255\024\255\067\255\017\255\000\000\004\255\
\000\000\068\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\002\255\000\000\086\255\000\000\
\000\000\088\255\000\000\000\000\000\000\000\000\000\000\065\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\232\255\
\000\000\000\000\250\254\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\081\255\000\000\000\000\000\000\000\000\000\000\089\255\234\255\
\060\000\000\000\054\255\076\255\000\000\000\000\244\255\246\255\
\018\000\020\000\030\000\032\000\000\000\000\000\000\000\000\000\
\000\000\090\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\084\255\250\254\000\000\000\000\089\255\000\000\093\255\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\240\255\100\000\000\000\000\000\254\255\000\000\
\019\000\000\000"

let yytablesize = 435
let yytable = "\032\000\
\014\000\014\000\014\000\003\000\060\000\001\000\003\000\046\000\
\011\000\028\000\061\000\003\000\003\000\012\000\003\000\005\000\
\013\000\049\000\050\000\040\000\041\000\042\000\046\000\081\000\
\082\000\006\000\063\000\059\000\008\000\018\000\047\000\048\000\
\049\000\050\000\051\000\052\000\053\000\054\000\055\000\056\000\
\077\000\064\000\065\000\066\000\067\000\068\000\069\000\070\000\
\071\000\072\000\073\000\074\000\075\000\076\000\003\000\078\000\
\014\000\017\000\080\000\031\000\029\000\030\000\031\000\084\000\
\031\000\088\000\014\000\031\000\031\000\058\000\089\000\014\000\
\014\000\014\000\094\000\095\000\014\000\096\000\087\000\098\000\
\014\000\032\000\090\000\099\000\031\000\031\000\032\000\014\000\
\031\000\032\000\032\000\004\000\014\000\031\000\024\000\031\000\
\031\000\021\000\014\000\031\000\031\000\031\000\031\000\031\000\
\031\000\043\000\032\000\032\000\014\000\019\000\032\000\000\000\
\097\000\000\000\000\000\032\000\000\000\032\000\032\000\000\000\
\000\000\032\000\032\000\032\000\032\000\032\000\032\000\091\000\
\046\000\000\000\044\000\045\000\000\000\046\000\000\000\000\000\
\047\000\048\000\049\000\050\000\000\000\047\000\048\000\049\000\
\050\000\051\000\052\000\053\000\054\000\055\000\056\000\000\000\
\044\000\045\000\057\000\046\000\033\000\034\000\035\000\036\000\
\037\000\038\000\000\000\047\000\048\000\049\000\050\000\051\000\
\052\000\053\000\054\000\055\000\056\000\000\000\044\000\045\000\
\000\000\046\000\085\000\000\000\000\000\000\000\000\000\000\000\
\000\000\047\000\048\000\049\000\050\000\051\000\052\000\053\000\
\054\000\055\000\056\000\044\000\045\000\000\000\046\000\000\000\
\092\000\000\000\000\000\000\000\000\000\000\000\047\000\048\000\
\049\000\050\000\051\000\052\000\053\000\054\000\055\000\056\000\
\044\000\045\000\000\000\046\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\047\000\048\000\049\000\050\000\051\000\
\052\000\053\000\054\000\055\000\056\000\044\000\000\000\042\000\
\000\000\000\000\044\000\000\000\042\000\044\000\044\000\042\000\
\042\000\036\000\000\000\037\000\000\000\000\000\036\000\000\000\
\037\000\036\000\036\000\037\000\037\000\000\000\044\000\044\000\
\042\000\042\000\044\000\000\000\042\000\000\000\000\000\044\000\
\000\000\042\000\036\000\036\000\037\000\037\000\036\000\038\000\
\037\000\039\000\000\000\036\000\038\000\037\000\039\000\038\000\
\038\000\039\000\039\000\040\000\000\000\041\000\000\000\000\000\
\040\000\000\000\041\000\040\000\040\000\041\000\041\000\000\000\
\038\000\038\000\039\000\039\000\038\000\000\000\039\000\000\000\
\000\000\038\000\000\000\039\000\040\000\040\000\041\000\041\000\
\040\000\043\000\041\000\000\000\000\000\040\000\043\000\041\000\
\000\000\043\000\043\000\000\000\000\000\000\000\020\000\021\000\
\000\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
\023\000\000\000\000\000\043\000\024\000\000\000\043\000\044\000\
\045\000\000\000\046\000\043\000\000\000\025\000\026\000\000\000\
\062\000\000\000\047\000\048\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\056\000\044\000\045\000\000\000\046\000\
\079\000\000\000\000\000\000\000\000\000\000\000\000\000\047\000\
\048\000\049\000\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\044\000\045\000\000\000\046\000\086\000\000\000\000\000\
\000\000\000\000\000\000\000\000\047\000\048\000\049\000\050\000\
\051\000\052\000\053\000\054\000\055\000\056\000\044\000\000\000\
\000\000\046\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\047\000\048\000\049\000\050\000\051\000\052\000\053\000\
\054\000\055\000\056\000"

let yycheck = "\016\000\
\007\001\008\001\009\001\002\001\035\001\001\000\005\001\034\001\
\005\001\012\000\041\001\010\001\001\001\010\001\013\001\053\001\
\013\001\044\001\045\001\022\000\023\000\024\000\034\001\007\001\
\008\001\003\001\043\000\030\000\053\001\004\001\042\001\043\001\
\044\001\045\001\046\001\047\001\048\001\049\001\050\001\051\001\
\057\000\044\000\045\000\046\000\047\000\048\000\049\000\050\000\
\051\000\052\000\053\000\054\000\055\000\056\000\053\001\058\000\
\053\001\036\001\061\000\006\001\053\001\041\001\002\001\012\001\
\011\001\082\000\002\001\014\001\015\001\041\001\009\001\007\001\
\008\001\009\001\091\000\052\001\012\001\011\001\081\000\096\000\
\016\001\006\001\085\000\016\001\031\001\032\001\011\001\002\001\
\035\001\014\001\015\001\004\001\012\001\040\001\011\001\042\001\
\043\001\009\001\009\001\046\001\047\001\048\001\049\001\050\001\
\051\001\006\001\031\001\032\001\016\001\010\000\035\001\255\255\
\094\000\255\255\255\255\040\001\255\255\042\001\043\001\255\255\
\255\255\046\001\047\001\048\001\049\001\050\001\051\001\006\001\
\034\001\255\255\031\001\032\001\255\255\034\001\255\255\255\255\
\042\001\043\001\044\001\045\001\255\255\042\001\043\001\044\001\
\045\001\046\001\047\001\048\001\049\001\050\001\051\001\255\255\
\031\001\032\001\011\001\034\001\023\001\024\001\025\001\026\001\
\027\001\028\001\255\255\042\001\043\001\044\001\045\001\046\001\
\047\001\048\001\049\001\050\001\051\001\255\255\031\001\032\001\
\255\255\034\001\014\001\255\255\255\255\255\255\255\255\255\255\
\255\255\042\001\043\001\044\001\045\001\046\001\047\001\048\001\
\049\001\050\001\051\001\031\001\032\001\255\255\034\001\255\255\
\015\001\255\255\255\255\255\255\255\255\255\255\042\001\043\001\
\044\001\045\001\046\001\047\001\048\001\049\001\050\001\051\001\
\031\001\032\001\255\255\034\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\042\001\043\001\044\001\045\001\046\001\
\047\001\048\001\049\001\050\001\051\001\006\001\255\255\006\001\
\255\255\255\255\011\001\255\255\011\001\014\001\015\001\014\001\
\015\001\006\001\255\255\006\001\255\255\255\255\011\001\255\255\
\011\001\014\001\015\001\014\001\015\001\255\255\031\001\032\001\
\031\001\032\001\035\001\255\255\035\001\255\255\255\255\040\001\
\255\255\040\001\031\001\032\001\031\001\032\001\035\001\006\001\
\035\001\006\001\255\255\040\001\011\001\040\001\011\001\014\001\
\015\001\014\001\015\001\006\001\255\255\006\001\255\255\255\255\
\011\001\255\255\011\001\014\001\015\001\014\001\015\001\255\255\
\031\001\032\001\031\001\032\001\035\001\255\255\035\001\255\255\
\255\255\040\001\255\255\040\001\031\001\032\001\031\001\032\001\
\035\001\006\001\035\001\255\255\255\255\040\001\011\001\040\001\
\255\255\014\001\015\001\255\255\255\255\255\255\029\001\030\001\
\255\255\255\255\033\001\255\255\255\255\255\255\255\255\255\255\
\039\001\255\255\255\255\032\001\043\001\255\255\035\001\031\001\
\032\001\255\255\034\001\040\001\255\255\052\001\053\001\255\255\
\040\001\255\255\042\001\043\001\044\001\045\001\046\001\047\001\
\048\001\049\001\050\001\051\001\031\001\032\001\255\255\034\001\
\035\001\255\255\255\255\255\255\255\255\255\255\255\255\042\001\
\043\001\044\001\045\001\046\001\047\001\048\001\049\001\050\001\
\051\001\031\001\032\001\255\255\034\001\035\001\255\255\255\255\
\255\255\255\255\255\255\255\255\042\001\043\001\044\001\045\001\
\046\001\047\001\048\001\049\001\050\001\051\001\031\001\255\255\
\255\255\034\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\042\001\043\001\044\001\045\001\046\001\047\001\048\001\
\049\001\050\001\051\001"

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
  REAL_TYPE\000\
  QINT_TYPE\000\
  QBOOL_TYPE\000\
  QREAL_TYPE\000\
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
# 56 "parser.mly"
    ( _4 )
# 393 "parser.ml"
               : AST.stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var_list) in
    Obj.repr(
# 60 "parser.mly"
                         ( )
# 400 "parser.ml"
               : 'var_declarations))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "parser.mly"
    ( )
# 406 "parser.ml"
               : 'var_declarations))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var_decl) in
    Obj.repr(
# 65 "parser.mly"
             ( )
# 413 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_list) in
    Obj.repr(
# 66 "parser.mly"
                      ( )
# 421 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_spec) in
    Obj.repr(
# 70 "parser.mly"
                                    ( )
# 429 "parser.ml"
               : 'var_decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'type_spec) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 71 "parser.mly"
                                                      ( )
# 438 "parser.ml"
               : 'var_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
             ( TyInt )
# 444 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "parser.mly"
              ( TyBool )
# 450 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "parser.mly"
              ( TyReal )
# 456 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "parser.mly"
              ( TyQInt )
# 462 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "parser.mly"
               ( TyQBool )
# 468 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "parser.mly"
               ( TyQReal )
# 474 "parser.ml"
               : 'type_spec))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "parser.mly"
    ( SSkip )
# 480 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 85 "parser.mly"
              ( _1 )
# 487 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statement) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement_list) in
    Obj.repr(
# 86 "parser.mly"
                             ( SSeq (_1, _2) )
# 495 "parser.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 91 "parser.mly"
    ( SAssign (string_to_coq_string _1, _3) )
# 503 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'statement_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'else_part) in
    Obj.repr(
# 94 "parser.mly"
    ( SIf (_2, _4, _5) )
# 512 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    Obj.repr(
# 97 "parser.mly"
    ( SWhile (_2, _4) )
# 520 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'expression) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'for_step) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    Obj.repr(
# 100 "parser.mly"
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
# 540 "parser.ml"
               : 'statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 113 "parser.mly"
    ( SSkip )
# 546 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'else_part) in
    Obj.repr(
# 115 "parser.mly"
    ( SIf (_2, _4, _5) )
# 555 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement_list) in
    Obj.repr(
# 117 "parser.mly"
    ( _2 )
# 562 "parser.ml"
               : 'else_part))
; (fun __caml_parser_env ->
    Obj.repr(
# 121 "parser.mly"
    ( 1 )
# 568 "parser.ml"
               : 'for_step))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 122 "parser.mly"
           ( _2 )
# 575 "parser.ml"
               : 'for_step))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 127 "parser.mly"
    ( EConst (VInt _1) )
# 582 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    Obj.repr(
# 130 "parser.mly"
    ( EConst (VBool true) )
# 588 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    Obj.repr(
# 133 "parser.mly"
    ( EConst (VBool false) )
# 594 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 136 "parser.mly"
    ( EVar (string_to_coq_string _1) )
# 601 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 139 "parser.mly"
    ( _2 )
# 608 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 142 "parser.mly"
    ( EBinop (OpAdd, _1, _3) )
# 616 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 145 "parser.mly"
    ( EBinop (OpSub, _1, _3) )
# 624 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 148 "parser.mly"
    ( EBinop (OpMul, _1, _3) )
# 632 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 151 "parser.mly"
    ( EBinop (OpDiv, _1, _3) )
# 640 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 154 "parser.mly"
    ( EBinop (OpMod, _1, _3) )
# 648 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 157 "parser.mly"
    ( EBinop (OpEq, _1, _3) )
# 656 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 160 "parser.mly"
    ( EBinop (OpNe, _1, _3) )
# 664 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 163 "parser.mly"
    ( EBinop (OpLt, _1, _3) )
# 672 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 166 "parser.mly"
    ( EBinop (OpLe, _1, _3) )
# 680 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 169 "parser.mly"
    ( EBinop (OpGt, _1, _3) )
# 688 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 172 "parser.mly"
    ( EBinop (OpGe, _1, _3) )
# 696 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 175 "parser.mly"
    ( EBinop (OpAnd, _1, _3) )
# 704 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 178 "parser.mly"
    ( EBinop (OpOr, _1, _3) )
# 712 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 181 "parser.mly"
    ( EUnop (OpNot, _2) )
# 719 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 184 "parser.mly"
    ( EUnop (OpNeg, _2) )
# 726 "parser.ml"
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
