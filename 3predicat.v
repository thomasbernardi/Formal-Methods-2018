Parameters A B C : Prop.

Goal A -> B -> A.
intros.
assumption.
Save exo1.

Goal (A -> B -> C) -> (A -> B) -> A -> C.
intros.
apply (H H1).
apply (H0 H1).
Save exo2.

Goal A /\ B -> B.
intros.
elim (H).
intros.
assumption.
Save exo3.

Goal B -> A \/ B.
intros.
right.
assumption.
Save exo4.

Goal (A \/ B) -> (A -> C) -> (B -> C) -> C.
intros.
elim (H).
intros.
apply (H0 H2).
intros.
apply (H1 H2).
Save exo5.

Goal A -> False -> ~ A.
intros.
intro.
assumption.
Save exo6.

Goal False -> A.
intros.
elimtype False.
assumption.
Save exo7.

Goal (A <-> B) -> A -> B.
intros.
elim (H).
intros.
apply (H1 H0).
Save exo8.

Goal (A <-> B) -> B -> A.
intros.
elim (H).
intros.
apply (H2 H0).
Save exo9.

Goal (A -> B) -> (B -> A) -> (A <-> B).
intros.
split.
intros.
apply (H H1).
intros.
apply (H0 H1).
Save exo10.

Goal (A -> B) -> (~ A \/ B).
intros.
right.
apply H.

