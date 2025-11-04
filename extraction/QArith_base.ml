open BinInt
open BinPos
open Zbool

type coq_Q = { coq_Qnum : int; coq_Qden : int }

(** val inject_Z : int -> coq_Q **)

let inject_Z x =
  { coq_Qnum = x; coq_Qden = 1 }

(** val coq_Qeq_bool : coq_Q -> coq_Q -> bool **)

let coq_Qeq_bool x y =
  coq_Zeq_bool (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden)

(** val coq_Qle_bool : coq_Q -> coq_Q -> bool **)

let coq_Qle_bool x y =
  Z.leb (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden)

(** val coq_Qplus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qplus x y =
  { coq_Qnum =
    (Z.add (Z.mul x.coq_Qnum y.coq_Qden) (Z.mul y.coq_Qnum x.coq_Qden));
    coq_Qden = (Pos.mul x.coq_Qden y.coq_Qden) }

(** val coq_Qmult : coq_Q -> coq_Q -> coq_Q **)

let coq_Qmult x y =
  { coq_Qnum = (Z.mul x.coq_Qnum y.coq_Qnum); coq_Qden =
    (Pos.mul x.coq_Qden y.coq_Qden) }

(** val coq_Qopp : coq_Q -> coq_Q **)

let coq_Qopp x =
  { coq_Qnum = (Z.opp x.coq_Qnum); coq_Qden = x.coq_Qden }

(** val coq_Qminus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qminus x y =
  coq_Qplus x (coq_Qopp y)

(** val coq_Qinv : coq_Q -> coq_Q **)

let coq_Qinv x =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> { coq_Qnum = 0; coq_Qden = 1 })
    (fun p -> { coq_Qnum = x.coq_Qden; coq_Qden = p })
    (fun p -> { coq_Qnum = ((~-) x.coq_Qden); coq_Qden = p })
    x.coq_Qnum

(** val coq_Qdiv : coq_Q -> coq_Q -> coq_Q **)

let coq_Qdiv x y =
  coq_Qmult x (coq_Qinv y)
