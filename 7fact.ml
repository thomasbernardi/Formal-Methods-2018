type nat =
| O
| S of nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val fact : nat -> nat **)

let rec fact = function
| O -> S O
| S n0 -> mul (S n0) (fact n0)