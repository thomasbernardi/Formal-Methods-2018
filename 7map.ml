type nat =
  | O
  | S of nat
  
  type 'a list =
  | Nil
  | Cons of 'a * 'a list
  
  type 'a sig0 = 'a
    (* singleton inductive, whose constructor was exist *)
  
  (** val map : (nat -> nat) -> nat list -> nat list **)
  
  let rec map f = function
  | Nil -> Nil
  | Cons (y, l) -> Cons ((f y), (map f l))
  