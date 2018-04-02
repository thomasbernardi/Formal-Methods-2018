Require Export ZArith.
Require Export FunInd.
Require Export Omega.
Open Scope Z_scope.

Inductive AB : Set :=
  | Node : Z -> AB -> AB -> AB
  | Empty : AB.

(*is_ABR node lower upper
equal goes left*)
Inductive is_ABR : AB -> (option Z) -> (option Z) -> Prop :=
  | Empty_ABR : forall (vL vR : option Z), is_ABR Empty vL vR
  | No_Limits : forall (v : Z) (aL aR : AB), is_ABR aL None (Some v) -> is_ABR aR (Some v) None -> 
    is_ABR (Node v aL aR) None None
  | Lower : forall (v vL : Z) (aL aR : AB), v > vL -> is_ABR aL (Some vL) (Some v) ->
    is_ABR aR (Some v) None -> is_ABR (Node v aL aR) (Some vL) None
  | Upper : forall (v vR : Z) (aL aR : AB), v <= vR -> is_ABR aL None (Some v) ->
    is_ABR aR (Some v) (Some vR) -> is_ABR (Node v aL aR) None (Some vR)
  | Both : forall (v vL vR : Z) (aL aR : AB), v > vL -> v <= vR -> is_ABR aL (Some vL) (Some v) ->
    is_ABR aR (Some v) (Some vR) -> is_ABR (Node v aL aR) (Some vL) (Some vR).

Definition benchmark_01 := (Node 3 (Node 1 (Node 0 Empty Empty) (Node 3 Empty Empty)) (Node 5 Empty Empty)).
Definition benchmark_02 := (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 7 (Node 7 Empty Empty) (Node 8 Empty Empty))).
Definition benchmark_03 := (Node 15 (Node 12 (Node 11 (Node 5 Empty Empty) Empty) (Node 14 (Node 13 Empty (Node 13 Empty Empty)) (Node 15 Empty Empty))) (Node 18 (Node 17 Empty Empty) (Node 19 Empty (Node 20 Empty Empty)))).

Lemma p1 : is_ABR benchmark_01 None None.
apply No_Limits.
apply Upper.
omega.
apply Upper.
omega.
apply Empty_ABR.
apply Empty_ABR.
apply Both.
omega.
omega.
apply Empty_ABR.
apply Empty_ABR.
apply Lower.
omega.
apply Empty_ABR.
apply Empty_ABR.

Ltac apply_is_ABR :=
  repeat
  apply Empty_ABR || apply No_Limits || apply Lower || apply Upper || apply Both || auto || omega.

Lemma p2 : is_ABR benchmark_02 None None.
apply_is_ABR.
Qed.


Lemma p3 : is_ABR benchmark_03 None None.
apply_is_ABR.
Qed.

Inductive value_exists : AB -> Z -> Prop :=
  | Curr : forall (v : Z) (aL aR : AB), value_exists (Node v aL aR) v
  | Left : forall (v vL : Z) (aL aR : AB), value_exists aL vL ->
    value_exists (Node v aL aR) vL
  | Right : forall (v vR : Z) (aL aR : AB), value_exists aR vR ->
    value_exists (Node v aL aR) vR.

Lemma p5 : value_exists benchmark_01 3.
eapply Curr.
Qed.

Lemma p6 : value_exists benchmark_03 17.
eapply Right.
eapply Left.
eapply Curr.
Qed.

Fixpoint search (arbre : AB) (v : Z) : bool :=
  match arbre with
  | Empty => false
  | Node w aL aR =>
    if Z.eq_dec v w then true
    else if Z_le_dec v w then search aL v
    else search aR v
end.

Functional Scheme search_ind := Induction for search Sort Prop.

Lemma both_upper : forall (arbre : AB) (vL vR : Z), is_ABR arbre (Some vL) (Some vR) -> 
    is_ABR arbre None (Some vR).
intros.
induction H; apply_is_ABR.
Qed.

Lemma both_lower : forall (arbre : AB) (vL vR : Z), is_ABR arbre (Some vL) (Some vR) -> 
    is_ABR arbre (Some vL) None.
intros.
induction H; apply_is_ABR.
Qed.

Lemma both_reduce : forall (arbre : AB) (vL vR : Z), is_ABR arbre (Some vL) (Some vR) ->
    is_ABR arbre None None.
intros.
induction H; apply_is_ABR.
eapply both_upper.
apply H0.
eapply both_lower.
apply H1.
eapply both_upper.
apply H1.
eapply both_lower.
apply H2.
Qed.

Lemma both_option_reduce : forall (arbre : AB) (vL vR : option Z), is_ABR arbre vL vR ->
    is_ABR arbre None None.
intros.
induction H; apply_is_ABR.
eapply both_upper.
apply H0.
eapply both_lower.
apply H1.
eapply both_upper.
apply H1.
eapply both_lower.
apply H2.
Qed.

Theorem search_sound : 
  forall (arbre : AB) (v : Z), is_ABR arbre None None -> search arbre v = true -> value_exists arbre v.

Proof.
intro.
intro.
intro.
functional induction (search arbre v) using search_ind; intros.
eapply Curr.
eapply Left.
apply IHb.
inversion H.
eapply both_option_reduce.
apply H3.
assumption.
apply Right.
apply IHb.
inversion H.
eapply both_option_reduce.
apply H5.
assumption.
contradict H0.
auto.
Qed.


Lemma left_less : forall (aL aR : AB) (v vL : Z) (L R : option Z), is_ABR (Node v aL aR) L R -> value_exists aL vL ->
    vL <= v.
intros.
induction H0.
inversion H.
inversion H5.
omega.
inversion H6.
omega.
inversion H6.
omega.
inversion H7.
omega.
apply IHvalue_exists.
inversion H.
apply_is_ABR.
inversion H6.
Focus 2.
apply_is_ABR.
inversion H7.



Theorem search_complete : forall (arbre : AB) (v : Z), is_ABR arbre None None ->
    value_exists arbre v -> search arbre v = true.
intro.
intro.
intro.
intro.
induction H0.
simpl.
elim (Z.eq_dec v v); intro; auto.
simpl.
elim (Z.eq_dec vL v); intro; auto.
elim (Z_le_dec vL v); intro; auto.
apply IHvalue_exists.
inversion H.
eapply both_option_reduce.
apply H3.




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
functional induction (insert a_in v) using insert_ind; intros.
rewrite H0.
split.
assumption.
split.
eapply Curr.
auto.
intros.
assumption.

rewrite H0.
split.
inversion H; apply_is_ABR.
simpl.
reflexivity.
omega.








