Require Export Omega.
Lemma nateq_dec : forall n m : nat, {n = m} + {n <> m}.
double induction n m; intros.
auto.
elim H; intros.
right; auto.
right; auto.
right; auto.
elim (H0 n0); intros.
rewrite a; auto.
auto.
Defined.

Require Export Extraction.
Recursive Extraction nateq_dec.

Inductive is_fact : nat -> nat -> Prop :=
| is_fact_1 : is_fact 0 1
| is_fact_S : forall (n : nat) (r : nat), is_fact n r -> is_fact (S n) ((S n) * r).

Lemma fact : forall n : nat, {v : nat | is_fact n v}.
intro.
induction n.
exists 1.
apply is_fact_1.
elim IHn.
intros.
exists ((S n) * x).
apply is_fact_S.
assumption.
Defined.

Recursive Extraction fact.
Open Scope list_scope.
Inductive mapped : (nat -> nat) -> list nat -> list nat -> Prop :=
| mapped_none : forall (f : nat -> nat), mapped f nil nil
| mapped_rec : forall (f : nat -> nat) (l1 l2 : list nat) (n1 n2 : nat),
    mapped f l1 l2 -> n2 = (f n1) -> mapped f (n1::l1) (n2::l2).

Lemma map : forall (f : nat -> nat) (l1 : list nat), {l2 : list nat | mapped f l1 l2}.
intro.
intro.
induction l1.
exists nil.
apply mapped_none.
elim IHl1.
intros.
exists ((f a) :: x).
apply mapped_rec.
assumption.
reflexivity.
Defined.

Recursive Extraction map.
