open QArith_base
open Types

type value =
| VBool of bool
| VInt of int
| VReal of coq_Q
| VString of char list
| VVoid

(** val typeof : value -> ty **)

let typeof = function
| VBool _ -> TyBool
| VInt _ -> TyInt
| VReal _ -> TyReal
| VString _ -> TyString
| VVoid -> TyVoid

(* has_type : logical inductive *)
(* with constructors : T_Bool T_Int T_Real T_String T_Void *)

