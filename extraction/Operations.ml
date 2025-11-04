open BinInt
open Datatypes
open QArith_base
open Values

(** val eval_arith_binop :
    (int -> int -> int) -> (coq_Q -> coq_Q -> coq_Q) -> value -> value ->
    value option **)

let eval_arith_binop op_int op_real v1 v2 =
  match v1 with
  | VInt n1 ->
    (match v2 with
     | VInt n2 -> Some (VInt (op_int n1 n2))
     | VReal r2 -> Some (VReal (op_real (inject_Z n1) r2))
     | _ -> None)
  | VReal r1 ->
    (match v2 with
     | VInt n2 -> Some (VReal (op_real r1 (inject_Z n2)))
     | VReal r2 -> Some (VReal (op_real r1 r2))
     | _ -> None)
  | _ -> None

(** val eval_comp_binop :
    (int -> int -> bool) -> (coq_Q -> coq_Q -> bool) -> value -> value ->
    value option **)

let eval_comp_binop op_int op_real v1 v2 =
  match v1 with
  | VInt n1 ->
    (match v2 with
     | VInt n2 -> Some (VBool (op_int n1 n2))
     | VReal r2 -> Some (VBool (op_real (inject_Z n1) r2))
     | _ -> None)
  | VReal r1 ->
    (match v2 with
     | VInt n2 -> Some (VBool (op_real r1 (inject_Z n2)))
     | VReal r2 -> Some (VBool (op_real r1 r2))
     | _ -> None)
  | _ -> None

(** val eval_bool_binop :
    (bool -> bool -> bool) -> value -> value -> value option **)

let eval_bool_binop op v1 v2 =
  match v1 with
  | VBool b1 ->
    (match v2 with
     | VBool b2 -> Some (VBool (op b1 b2))
     | _ -> None)
  | _ -> None

(** val eval_add : value -> value -> value option **)

let eval_add v1 v2 =
  eval_arith_binop Z.add coq_Qplus v1 v2

(** val eval_sub : value -> value -> value option **)

let eval_sub v1 v2 =
  eval_arith_binop Z.sub coq_Qminus v1 v2

(** val eval_mul : value -> value -> value option **)

let eval_mul v1 v2 =
  eval_arith_binop Z.mul coq_Qmult v1 v2

(** val eval_div : value -> value -> value option **)

let eval_div v1 v2 =
  match v1 with
  | VInt n1 ->
    (match v2 with
     | VInt n2 -> if Z.eqb n2 0 then None else Some (VInt (Z.div n1 n2))
     | VReal r2 ->
       if coq_Qeq_bool r2 { coq_Qnum = 0; coq_Qden = 1 }
       then None
       else Some (VReal (coq_Qdiv (inject_Z n1) r2))
     | _ -> None)
  | VReal r1 ->
    (match v2 with
     | VInt n2 ->
       if Z.eqb n2 0 then None else Some (VReal (coq_Qdiv r1 (inject_Z n2)))
     | VReal r2 ->
       if coq_Qeq_bool r2 { coq_Qnum = 0; coq_Qden = 1 }
       then None
       else Some (VReal (coq_Qdiv r1 r2))
     | _ -> None)
  | _ -> None

(** val eval_mod : value -> value -> value option **)

let eval_mod v1 v2 =
  match v1 with
  | VInt n1 ->
    (match v2 with
     | VInt n2 -> if Z.eqb n2 0 then None else Some (VInt (Z.modulo n1 n2))
     | _ -> None)
  | _ -> None

(** val eval_eq : value -> value -> value option **)

let eval_eq v1 v2 =
  eval_comp_binop Z.eqb coq_Qeq_bool v1 v2

(** val eval_ne : value -> value -> value option **)

let eval_ne v1 v2 =
  match eval_eq v1 v2 with
  | Some v -> (match v with
               | VBool b -> Some (VBool (negb b))
               | _ -> None)
  | None -> None

(** val eval_lt : value -> value -> value option **)

let eval_lt v1 v2 =
  eval_comp_binop Z.ltb (fun r1 r2 -> negb (coq_Qle_bool r2 r1)) v1 v2

(** val eval_le : value -> value -> value option **)

let eval_le v1 v2 =
  eval_comp_binop Z.leb coq_Qle_bool v1 v2

(** val eval_gt : value -> value -> value option **)

let eval_gt v1 v2 =
  eval_comp_binop Z.gtb (fun r1 r2 -> negb (coq_Qle_bool r1 r2)) v1 v2

(** val eval_ge : value -> value -> value option **)

let eval_ge v1 v2 =
  eval_comp_binop Z.geb (fun r1 r2 -> negb (coq_Qle_bool r2 r1)) v1 v2

(** val eval_and : value -> value -> value option **)

let eval_and v1 v2 =
  eval_bool_binop (&&) v1 v2

(** val eval_or : value -> value -> value option **)

let eval_or v1 v2 =
  eval_bool_binop (||) v1 v2

(** val eval_neg : value -> value option **)

let eval_neg = function
| VInt n -> Some (VInt (Z.opp n))
| VReal r -> Some (VReal (coq_Qopp r))
| _ -> None
