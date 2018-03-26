Parameter E : Set.
Parameters P Q : E -> Prop.

Goal forall x : E, (P x) -> exists y : E, (P y) \/ (Q y).
intros.
exists x.
left.
assumption.
Save exo1.

Goal (exists x : E, (P x) \/ (Q x)) -> (exists x : E, (P x)) \/ (exists x : E, (Q x)).
intros.
elim (H).
intros.
elim (H0).
intros.
left.
exists x.
assumption.
intros.
right.
exists x.
assumption.
Save exo2.

Goal (forall x : E, (P x)) /\ (forall x : E, (Q x)) -> forall x : E, (P x) /\ (Q x).
intros.
elim (H).
intros.
split.
apply (H0).
apply (H1).
Save exo3.

Goal (forall x : E, (P x) /\ (Q x)) -> (forall x : E, (P x)) /\ (forall x : E, (Q x)).
intros.
split.
intro.
apply (H).
intro.
apply (H).
Save exo4.

Goal (forall x : E, ~ (P x)) -> ~ (exists x : E, (P x)).
intros.
intro.
elim (H0).
intros.
apply (H x).
assumption.
Save exo5.


















