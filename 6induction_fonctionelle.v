Require Import FunInd.

Inductive is_even : nat -> Prop :=
| is_even_O : is_even 0
| is_even_S : forall n : nat, is_even n -> is_even (S (S n)).


Fixpoint even (n : nat) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | (S (S n)) => even n
  end.

Functional Scheme even_ind := Induction for even Sort Prop.

Theorem even_sound :
  forall (n : nat) (v : Prop), (even n) = True -> is_even n.

Proof.
intro.
intro.
functional induction (even n) using even_ind; intros.
apply is_even_O.
elimtype False.
rewrite H.
auto.
apply is_even_S.
apply IHP.
assumption.
Qed.

Theorem even_complete : forall (n : nat) (v : Prop), is_even n -> (even n) = True.
intro.
intro.
intro.
induction H.
simpl.
reflexivity.
simpl.
assumption.
Qed.

Inductive is_fact : nat -> nat -> Prop :=
| is_fact_1 : is_fact 0 1
| is_fact_S : forall (n : nat) (r : nat), is_fact n r -> is_fact (S n) ((S n) * r).

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | (S n) => (S n) * (fact n)
  end.

Functional Scheme fact_ind := Induction for fact Sort Prop.

Theorem fact_sound :
  forall (n : nat) (r : nat), (fact n) = r -> is_fact n r.

Proof.
intro.
functional induction (fact n) using fact_ind; intros.
rewrite <- H.
apply is_fact_1.
elim H.
apply is_fact_S.
apply IHn0.
reflexivity.
Qed.

Open Scope list_scope.
Inductive is_perm : list nat -> list nat -> Prop :=
| perm_base : forall (l : list nat) (a : nat), is_perm (a :: l) (l ++ a::nil)
| perm_ind  : forall (l1 : list nat) (l2 : list nat) (a : nat), is_perm l1 l2 -> is_perm (a :: l1) (a :: l2)
| perm_ref  : forall (l1 : list nat) (l2 : list nat), l1 = l2 -> is_perm l1 l2
| perm_tran : forall (l1 : list nat) (l2 : list nat) (l3 : list nat), (is_perm l1 l2) -> (is_perm l2 l3) -> is_perm l1 l3
| perm_sem  : forall (l1 : list nat) (l2 : list nat), is_perm l1 l2 -> is_perm l2 l1.

Lemma trans_1 : is_perm (1::2::3::nil) (3::2::1::nil).
apply (perm_tran (1::2::3::nil) ((2::3::nil)++(1::nil)) (3::2::1::nil)).
apply perm_base.
simpl.
apply (perm_tran (2::3::1::nil) ((3::1::nil)++(2::nil)) (3::2::1::nil)).
apply perm_base.
simpl.
apply perm_ind.
apply (perm_tran (1::2::nil) ((1::nil)++(2::nil)) (2::1::nil)).
simpl.
apply perm_ref.
reflexivity.
apply perm_base.
Qed.

Inductive sorted : list nat -> Prop :=
| sorted_empty  : sorted nil
| sorted_one    : forall n : nat, sorted (n::nil)
| sorted_rec    : forall (n : nat) (m : nat) (l : list nat), n <= m -> sorted (m::l) -> sorted (n::m::l).

Lemma sort_1 : sorted (1::2::3::nil).
apply sorted_rec.
apply le_S.
apply le_n.
apply sorted_rec.
apply le_S.
apply le_n.
apply sorted_one.
Qed.

Require Import Compare_dec.
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => (x::nil)
  | h::t => match (le_dec x h) with
            | left _ => (x::h::t)
            | right _ => (h::(insert x t))
  end
end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
end.

Functional Scheme sort_ind := Induction for sort Sort Prop.
Functional Scheme insert_ind := Induction for insert Sort Prop.

Require Export Omega.
Lemma perm_insert : forall (a : nat) (l : list nat), is_perm (a::l) (insert a l).
intros.
functional induction (insert a l) using insert_ind.
apply perm_ref.
reflexivity.
apply perm_ref.
reflexivity.
apply (perm_tran (a::h::t) (h::a::t) (h::insert a t)).
apply (perm_tran (a::h::t) ((h::t)++(a::nil)) (h::a::t)).
apply perm_base.
simpl.
apply perm_ind.
apply perm_sem.
apply perm_base.
apply perm_ind.
apply IHl0.
Qed.

Lemma sort_insert : forall (a : nat) (l : list nat), sorted l -> sorted (insert a l).
intros.
elim H.
simpl.
apply sorted_one.
intros.
simpl.
elim (le_dec a n).
intros.
apply sorted_rec.
omega.
apply sorted_one.
intros.
apply sorted_rec.
omega.
apply sorted_one.
intros n m.
simpl.
elim (le_dec a m).
intros.
elim (le_dec a n).
intros.
apply sorted_rec.
omega.
apply sorted_rec.
omega.
apply H1.
intros.
apply sorted_rec.
omega.
apply sorted_rec.
omega.
apply H1.
intros.
elim (le_dec a n).
intros.
apply sorted_rec.
omega.
apply sorted_rec.
omega.
apply H1.
intros.
apply sorted_rec.
auto.
auto.
Qed.
Theorem sort_sound :
  forall (l : list nat) (ls : list nat), sort l = ls -> (is_perm l ls) /\ (sorted ls).

Proof.
intro.
functional induction (sort l) using sort_ind; intros.
rewrite <- H.
split.
apply perm_ref.
reflexivity.
apply sorted_empty.
rewrite <- H.
split.
apply (perm_tran (h::t) (h::sort t) (insert h (sort t))).
apply perm_ind.
apply IHl0.
reflexivity.
apply perm_insert.
apply sort_insert.
apply IHl0.
reflexivity.
Qed.