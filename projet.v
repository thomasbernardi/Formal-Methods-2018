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
  | Node_Both : forall (v vL vR : Z) (aL aR saLL saLR saRL saRR : AB), is_ABR aL -> is_ABR aR ->
    aL = (Node vL saLL saLR) -> aR = (Node vR saRL saRR) -> vL <= v -> v <= vR ->
    is_ABR (Node v aL aR)
  | Node_Left : forall (v vL : Z) (aL saL saR : AB), is_ABR aL -> aL = (Node vL saL saR) ->
    vL <= v -> is_ABR (Node v aL Empty)
  | Node_Right : forall (v vR : Z) (aR saL saR : AB), is_ABR aR -> aR = (Node vR saL saR) ->
    v <= vR -> is_ABR (Node v Empty aR).

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
  | Curr : forall (v : Z) (a aL aR : AB), a = (Node v aL aR) -> value_exists a v
  | Left : forall (v vL : Z) (a aL aR : AB), a = (Node v aL aR) -> value_exists aL vL ->
    value_exists a vL
  | Right : forall (v vR : Z) (a aL aR : AB), a = (Node v aL aR) -> value_exists aR vR ->
    value_exists a vR.

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
  | Node w aL aR =>
    if Z.eq_dec w v then true
    else if Z_lt_dec w v then search aR v
    else search aL v
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

Fixpoint insert (arbre : AB) (v : Z) : AB :=
  match arbre with
  | Empty => (Node v Empty Empty)
  | Node w aL aR =>
    if Z.eq_dec w v then arbre
    else if Z_lt_dec w v then (Node w aL (insert aR v))
    else (Node w (insert aL v) aR)
end.

Functional Scheme insert_ind := Induction for insert Sort Prop.

Theorem insert_sound : forall (a_in a_out : AB) (v : Z), is_ABR a_in -> a_out = (insert a_in v) ->
    is_ABR a_out /\ value_exists a_out v /\ (forall (w : Z), value_exists a_in w -> value_exists a_out w).
intro.
intro.
intro.
intro.
functional induction (insert a_in v) using insert_ind; intros; split.
rewrite H0.
assumption.
split.
rewrite H0.
eapply Curr.
auto.


Theorem search_complete : forall (arbre : AB) (v : Z), is_ABR arbre -> value_exists arbre v -> search arbre v = true.

Proof.
intro.
intro.
intro.
intro.
induction H0; induction H.
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
elim (Z.eq_dec v vL); intro.
reflexivity.
elim (Z_lt_dec v vL); intro; contradict H0; discriminate.
rewrite H0.
simpl.
elim (Z.eq_dec v vL); intro.
reflexivity.
elim (Z_lt_dec v vL); intro.
inversion H1; contradict H0; rewrite H; discriminate.
inversion H1; contradict H0; rewrite H; discriminate.

simpl.
elim (Z.eq_dec v0 vL); intro.
reflexivity.
elim (Z_lt_dec v0 vL); intro.

inversion H1.
injection H0; intros.
rewrite H3 in H11.
rewrite H7 in H11.
injection H11; intros.
contradict H15.
omega.
injection H0; intros.
rewrite H3 in H12.
rewrite H7 in H12.


(*next goal*)
injection H0.
intros.
rewrite <- H8 in IHvalue_exists.
apply IHvalue_exists.
apply H.


discriminate.
apply IHis_ABR2.
rewrite <- H0.
rewrite H4.
injection H0.
contradict H0.
injection.
intros.
contradict b.

congruence.

apply IHis_ABR2.






