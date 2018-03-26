Lemma ind_ex1 : forall n : nat, n * 1 = n.
intro.
elim n.
simpl.
reflexivity.
intros.
simpl.
rewrite H.
reflexivity.
Qed.

Fixpoint f (x : nat) {struct x} : nat :=
  match x with
  |0 => 1
  |S x => 2 * f(x)
  end.
Lemma ind_ex2 : f(10) = 1024.
simpl.
reflexivity.
Qed.

Require Import Lists.List.

Open Scope list_scope.
Lemma ind_ex3 : forall (E : Type) (l : list E) (e : E),
    rev(l ++ e :: nil) = e :: rev(l).
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma ind_ex4 : forall (E : Type) (l : list E), rev (rev l) = l.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite ind_ex3.
rewrite IHl.
reflexivity.
Qed.

Require Import Classical.

Lemma auto_eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
intros.
decide equality.
Qed.


Lemma man_eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
intros.
induction m.
induction n.
left.
reflexivity.
intros.
destruct IHn.
right.
rewrite e.
congruence.
right.
congruence.
destruct IHm.
right.
rewrite e.
apply n_Sn.














