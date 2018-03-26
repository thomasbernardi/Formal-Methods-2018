Parameter E : Set.
Parameters P Q : E -> Prop.

Lemma ex1_1 : (forall x : E, (P x) -> (Q x)) -> (exists x : E, (P x)) -> (exists x : E, (Q x)).
intros.
elim H0.
intros.
exists x.
apply H.
assumption.
Qed.

Lemma ex1_2 : (exists x : E, (P x)) \/ (exists x : E, (Q x)) -> exists x : E, (P x) \/ (Q x).
intros.
elim H.
intros.
elim H0.
intros.
exists x.
left.
assumption.
intros.
elim H0.
intros.
exists x.
right.
assumption.
Qed.

Require Import Lists.List.

Open Scope list_scope.

Lemma ex2_1 : forall (F : Set) (l1 l2 : list F), length (l1++l2) = (length l1) + (length l2).
intros.
induction l1.
induction l2.
auto.
auto.
simpl.
rewrite IHl1.
auto.
Qed.

Inductive is_even : nat -> Prop :=
| is_even_O : is_even 0
| is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

Inductive is_even_list : list nat -> Prop :=
| is_even_zero : is_even_list nil
| is_even_rec : forall (a : nat) (l : list nat), (is_even a) -> (is_even_list l) -> is_even_list (a::l).

Lemma ex3_2 : is_even_list (0::2::4::nil).
apply is_even_rec.
apply is_even_O.
apply is_even_rec.
apply is_even_S.
apply is_even_O.
apply is_even_rec.
apply is_even_S.
apply is_even_S.
apply is_even_O.
apply is_even_zero.
Qed.

Lemma ex3_3 : ~ is_even_list (0::1::2::4::nil).
intro.
inversion H.
inversion H3.
inversion H6.
Qed.

