open String
open Values

type env = char list -> value option

(** val empty : env **)

let empty _ =
  None

(** val update : env -> char list -> value -> env **)

let update e x v y =
  if eqb x y then Some v else e y

(** val lookup : env -> char list -> value option **)

let lookup e =
  e
