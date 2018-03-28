Require Export ZArith.
Require Export FunInd.
Require Export Omega.
Open Scope Z_scope.

Inductive AB : Set :=
  | Node : Z -> AB -> AB -> AB
  | Empty : AB.

Inductive is_ABR : AB -> Prop :=
  | Is_Empty : is_ABR Empty
  | Is_Leaf : forall v : Z, is_ABR (Node v Empty Empty)
  | Node_Both : forall (v vl vr : Z) (al ar sall salr sarl sarr : AB), is_ABR al -> is_ABR ar ->
    al = (Node vl sall salr) -> ar = (Node vr sarl sarr) -> vl <= v -> v <= vr ->
    is_ABR (Node v al ar)
  | Node_Left : forall (v vl : Z) (al sal sar : AB), is_ABR al -> al = (Node vl sal sar) ->
    vl <= v -> is_ABR (Node v al Empty)
  | Node_Right : forall (v vr : Z) (ar sal sar : AB), is_ABR ar -> ar = (Node vr sal sar) ->
    v <= vr -> is_ABR (Node v Empty ar).

Definition benchmark_01 := (Node 3 (Node 1 (Node 0 Empty Empty) (Node 3 Empty Empty)) (Node 5 Empty Empty)).
Definition benchmark_02 := (Node 5 (Node 3 (Node 2 Empty Empty) (Node 3 Empty Empty)) (Node 7 (Node 7 Empty Empty) (Node 8 Empty Empty))).
Definition benchmark_03 := (Node 15 (Node 12 (Node 11 (Node 5 Empty Empty) Empty) (Node 14 (Node 12 Empty (Node 13 Empty Empty)) (Node 15 Empty Empty))) (Node 18 (Node 17 Empty Empty) (Node 19 Empty (Node 20 Empty Empty)))).

Lemma p1 : is_ABR benchmark_01.
eapply Node_Both.
eapply Node_Both.
apply Is_Leaf.
apply Is_Leaf.
auto.
auto.
omega.
omega.
apply Is_Leaf.
auto.
auto.
omega.
omega.
Qed.

Ltac apply_is_ABR :=
  repeat
  apply Is_Empty || apply Is_Leaf || eapply Node_Right ||
  eapply Node_Left || eapply Node_Both || auto || omega.

Lemma p2 : is_ABR benchmark_02.
apply_is_ABR.
Qed.


Lemma p3 : is_ABR benchmark_03.
eapply Node_Both.
eapply Node_Both.
eapply Node_Left.
eapply Is_Leaf.
auto.
omega.
eapply Node_Both.
eapply Node_Right.
apply Is_Leaf.
auto.
omega.
apply Is_Leaf.
auto.
auto.
omega.
omega.
auto.
auto.
omega.
omega.
eapply Node_Both.
apply Is_Leaf.
eapply Node_Right.
apply Is_Leaf.
auto.
omega.
auto.
auto.
omega.
omega.
auto.
auto.
omega.
omega.
Qed.

Lemma p4 : is_ABR benchmark_03.
apply_is_ABR.
Qed.

Inductive value_exists : AB -> Z -> Prop :=
  | Curr : forall (v : Z) (a al ar : AB), a = (Node v al ar) -> value_exists a v
  | Left : forall (v vl : Z) (a al ar : AB), a = (Node v al ar) -> value_exists al vl ->
    value_exists a vl
  | Right : forall (v vr : Z) (a al ar : AB), a = (Node v al ar) -> value_exists ar vr ->
    value_exists a vr.

Lemma p5 : value_exists benchmark_01 3.
eapply Curr.
reflexivity.
Qed.

Lemma p6 : value_exists benchmark_03 17.
eapply Right.
reflexivity.
eapply Left.
reflexivity.
eapply Curr.
reflexivity.
Qed.

Require Export Compare_dec.

Fixpoint search (arbre : AB) (v : Z) : bool :=
  match arbre with
  | Empty => false
  | Node w al ar =>
    if Z.eq_dec w v then true
    else if Z_lt_dec w v then search ar v
    else search al v
end.

Functional Scheme search_ind := Induction for search Sort Prop.

Theorem search_sound : 
  forall (arbre : AB) (v : Z), is_ABR arbre -> search arbre v = true -> value_exists arbre v.

Proof.
intro.
intro.
intro.
functional induction (search arbre v) using search_ind; intros.
eapply Curr.
auto.
eapply Right.
auto.
apply IHb.
inversion H.
apply_is_ABR.
assumption.
apply_is_ABR.
assumption.
assumption.
eapply Left.
auto.
apply IHb.
inversion H.
apply_is_ABR.
assumption.
assumption.
apply_is_ABR.
assumption.
contradict H0.
discriminate.
Qed.

Theorem search_complete : forall (arbre : AB) (v : Z), is_ABR arbre -> value_exists arbre v -> search arbre v = true.

Proof.
intro.
intro.
intro.
intro.
induction H0.
induction H.
contradict H0.
intro.
discriminate H.
rewrite H0.
simpl.
elim (Z.eq_dec v v); intro.
reflexivity.
elim (Z_lt_dec v v); intro; contradict b; reflexivity.
rewrite H0.
simpl.
elim (Z.eq_dec v v); intro.
reflexivity.
elim (Z_lt_dec v v); intro; contradict b; reflexivity.
rewrite H0.
simpl.
elim (Z.eq_dec v v); intro.
reflexivity.
elim (Z_lt_dec v v); intro; contradict b; reflexivity.
rewrite H0.
simpl.
elim (Z.eq_dec v v); intro.
reflexivity.
elim (Z_lt_dec v v); intro; contradict b; reflexivity.
rewrite H0.
simpl.
elim (Z.eq_dec v vl); intro.
reflexivity.
elim (Z_lt_dec v vl); intro.
inversion H1.
apply IHvalue_exists.






Focus 2.
eapply Right.
reflexivity.
apply IHb.
induction ar.
apply_is_ABR.

apply IHar1.
intros.
discrimnate.
reflexivity.
omega.

Fixpoint insert