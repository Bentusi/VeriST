open BinInt
open Bytecode
open Datatypes
open Values

(** val quality_marker_base : int **)

let quality_marker_base =
  (~-) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))

(** val quality_marker_of : quality -> int **)

let quality_marker_of = function
| QGood -> quality_marker_base
| QBad -> Z.sub quality_marker_base 1
| QUncertain -> Z.sub quality_marker_base ((fun p->2*p) 1)

(** val gen_quality_prefix : quality -> instr list **)

let gen_quality_prefix q =
  (ILoadInt (quality_marker_of q)) :: []

(** val gen_load_const : value -> instr list **)

let gen_load_const = function
| VBool b -> (ILoadBool b) :: []
| VInt n -> (ILoadInt n) :: []
| VReal r -> (ILoadReal r) :: []
| VQBool (b, q) -> app (gen_quality_prefix q) ((ILoadBool b) :: [])
| VQInt (n, q) -> app (gen_quality_prefix q) ((ILoadInt n) :: [])
| VQReal (r, q) -> app (gen_quality_prefix q) ((ILoadReal r) :: [])
| VString s -> (ILoadString s) :: []
| VVoid -> []
