type nat =
| O
| S of nat

type sumbool =
| Vrai
| Faux

(** val nateq_dec : nat -> nat -> sumbool **)

let rec nateq_dec n m =
  match n with
  | O -> (match m with
          | O -> Vrai
          | S _ -> Faux)
  | S n0 -> (match m with
             | O -> Faux
             | S n1 -> nateq_dec n0 n1)
