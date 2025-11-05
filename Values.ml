open QArith_base
open Types

type quality =
| QGood
| QBad
| QUncertain

type value =
| VBool of bool
| VInt of int
| VReal of coq_Q
| VQBool of bool * quality
| VQInt of int * quality
| VQReal of coq_Q * quality
| VString of char list
| VVoid

(** val typeof : value -> ty **)

let typeof = function
| VBool _ -> TyBool
| VInt _ -> TyInt
| VReal _ -> TyReal
| VQBool (_, _) -> TyQBool
| VQInt (_, _) -> TyQInt
| VQReal (_, _) -> TyQReal
| VString _ -> TyString
| VVoid -> TyVoid

(* has_type : logical inductive *)
(* with constructors : T_Bool T_Int T_Real T_QBool T_QInt T_QReal T_String
   T_Void *)

