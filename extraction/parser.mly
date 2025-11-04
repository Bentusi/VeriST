%{
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
%}

%token PROGRAM END_PROGRAM
%token VAR END_VAR
%token IF THEN ELSIF ELSE END_IF
%token WHILE DO END_WHILE
%token FOR TO BY END_FOR
%token CASE OF END_CASE
%token FUNCTION END_FUNCTION RETURN
%token INT_TYPE BOOL_TYPE
%token TRUE FALSE
%token AND OR NOT MOD
%token SEMICOLON COLON COMMA DOT
%token LPAREN RPAREN
%token ASSIGN
%token PLUS MINUS TIMES DIVIDE
%token EQ NE LT LE GT GE
%token <int> INT
%token <string> IDENT
%token EOF

%left OR
%left AND
%nonassoc NOT
%nonassoc EQ NE LT LE GT GE
%left PLUS MINUS
%left TIMES DIVIDE MOD
%nonassoc UMINUS

%start program
%type <AST.stmt> program
%%

program:
  | PROGRAM IDENT var_declarations statement_list END_PROGRAM
    { $4 }
  ;

var_declarations:
  | VAR var_list END_VAR { }
  | { }
  ;

var_list:
  | var_decl { }
  | var_decl var_list { }
  ;

var_decl:
  | IDENT COLON type_spec SEMICOLON { }
  | IDENT COLON type_spec ASSIGN expression SEMICOLON { }
  ;

type_spec:
  | INT_TYPE { TyInt }
  | BOOL_TYPE { TyBool }
  ;

statement_list:
  | { SSkip }
  | statement { $1 }
  | statement statement_list { SSeq ($1, $2) }
  ;

statement:
  | IDENT ASSIGN expression SEMICOLON
    { SAssign (string_to_coq_string $1, $3) }
  
  | IF expression THEN statement_list else_part END_IF
    { SIf ($2, $4, $5) }
  
  | WHILE expression DO statement_list END_WHILE
    { SWhile ($2, $4) }
  
  | FOR IDENT ASSIGN expression TO expression for_step DO statement_list END_FOR
    { 
      (* Convert FOR to WHILE loop *)
      let var_id = string_to_coq_string $2 in
      let init = SAssign (var_id, $4) in
      let cond = EBinop (OpLe, EVar var_id, $6) in
      let increment = SAssign (var_id, 
        EBinop (OpAdd, EVar var_id, EConst (VInt $7))) in
      let loop_body = SSeq ($9, increment) in
      SSeq (init, SWhile (cond, loop_body))
    }
  ;

else_part:
  | { SSkip }
  | ELSIF expression THEN statement_list else_part
    { SIf ($2, $4, $5) }
  | ELSE statement_list
    { $2 }
  ;

for_step:
  | { 1 }
  | BY INT { $2 }
  ;

expression:
  | INT
    { EConst (VInt $1) }
  
  | TRUE
    { EConst (VBool true) }
  
  | FALSE
    { EConst (VBool false) }
  
  | IDENT
    { EVar (string_to_coq_string $1) }
  
  | LPAREN expression RPAREN
    { $2 }
  
  | expression PLUS expression
    { EBinop (OpAdd, $1, $3) }
  
  | expression MINUS expression
    { EBinop (OpSub, $1, $3) }
  
  | expression TIMES expression
    { EBinop (OpMul, $1, $3) }
  
  | expression DIVIDE expression
    { EBinop (OpDiv, $1, $3) }
  
  | expression MOD expression
    { EBinop (OpMod, $1, $3) }
  
  | expression EQ expression
    { EBinop (OpEq, $1, $3) }
  
  | expression NE expression
    { EBinop (OpNe, $1, $3) }
  
  | expression LT expression
    { EBinop (OpLt, $1, $3) }
  
  | expression LE expression
    { EBinop (OpLe, $1, $3) }
  
  | expression GT expression
    { EBinop (OpGt, $1, $3) }
  
  | expression GE expression
    { EBinop (OpGe, $1, $3) }
  
  | expression AND expression
    { EBinop (OpAnd, $1, $3) }
  
  | expression OR expression
    { EBinop (OpOr, $1, $3) }
  
  | NOT expression
    { EUnop (OpNot, $2) }
  
  | MINUS expression %prec UMINUS
    { EUnop (OpNeg, $2) }
  ;
