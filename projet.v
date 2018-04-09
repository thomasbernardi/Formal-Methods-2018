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
  | Empty_N : is_ABR Empty None None
  | Empty_L : forall (vL : Z), is_ABR Empty (Some vL) None
  | Empty_U : forall (vR : Z), is_ABR Empty None (Some vR)
  | Empty_B : forall (vL vR : Z), vL <= vR -> is_ABR Empty (Some vL) (Some vR)
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
Definition benchmark_03 := (Node 15 (Node 12 (Node 11 (Node 5 Empty Empty) Empty) (Node 14 (Node 13 Empty (Node 14 Empty Empty)) (Node 15 Empty Empty))) (Node 18 (Node 17 Empty Empty) (Node 19 Empty (Node 20 Empty Empty)))).

Lemma p1 : is_ABR benchmark_01 None None.
apply No_Limits.
apply Upper.
omega.
apply Upper.
omega.
apply Empty_U.
apply Empty_B.
omega.
apply Both.
omega.
omega.
apply Empty_B.
omega.
apply Empty_B.
omega.
apply Lower.
omega.
apply Empty_B.
omega.
apply Empty_L.

Ltac apply_is_ABR :=
  repeat
  apply Empty_N || apply Empty_L || apply Empty_U || apply Empty_B || 
  apply No_Limits || apply Lower || apply Upper || apply Both || auto || omega.

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

Lemma limits : forall (arbre : AB) (vL vR : Z), is_ABR arbre (Some vL) (Some vR) -> vL <= vR.
intros.
inversion H.
assumption.
omega.
Qed.

Lemma combine_limits_R : forall (arbre : AB) (vL vR1 vR2 : Z), is_ABR arbre (Some vL) (Some vR1) ->
    is_ABR arbre None (Some vR2) -> vR1 <= vR2 ->  is_ABR arbre (Some vL) (Some vR2).
intros.
induction arbre.
apply_is_ABR.
inversion H.
omega.
inversion H0.
omega.
inversion H.
assumption.
inversion H0.
assumption.
apply_is_ABR.
inversion H.
omega.
Qed.

Lemma right_loosen : forall (arbre : AB) (vR1 vR2 : Z), is_ABR arbre None (Some vR1) ->
    vR1 <= vR2 -> is_ABR arbre None (Some vR2).
intros.
induction arbre.
apply_is_ABR.
inversion H.
omega.
inversion H.
assumption.
inversion H.
eapply combine_limits_R.
apply H7.
apply IHarbre2.
eapply both_upper.
apply H7.
omega.
apply_is_ABR.
Qed.

Lemma left_less : forall (aL aR : AB) (v vL : Z), is_ABR (Node v aL aR) None None -> 
    value_exists aL vL -> vL <= v.
intros.
induction H0.
inversion H.
inversion H2.
omega.
apply IHvalue_exists.
inversion H.
apply_is_ABR.
inversion H3.
eapply right_loosen.
apply H11.
omega.
apply IHvalue_exists.
inversion H.
apply_is_ABR.
inversion H3.
eapply both_upper.
apply H12.
Qed.

Lemma combine_limits_L : forall (arbre : AB) (vL1 vL2 vR : Z), is_ABR arbre (Some vL1) (Some vR) ->
    is_ABR arbre (Some vL2) None -> vL2 <= vL1 ->  is_ABR arbre (Some vL2) (Some vR).
intros.
induction arbre.
apply_is_ABR.
inversion H.
omega.
inversion H.
omega.
inversion H0.
assumption.
inversion H.
assumption.
apply_is_ABR.
inversion H.
omega.
Qed.

Lemma left_loosen : forall (arbre : AB) (vL1 vL2 : Z), is_ABR arbre (Some vL1) None ->
    vL2 <= vL1 -> is_ABR arbre (Some vL2) None.
intros.
induction arbre.
apply_is_ABR.
inversion H.
omega.
inversion H.
eapply combine_limits_L.
apply H6.
apply IHarbre1.
eapply both_lower.
apply H6.
assumption.
inversion H.
assumption.
apply_is_ABR.
Qed.

Lemma right_more : forall (aL aR : AB) (v vR : Z), is_ABR (Node v aL aR) None None -> 
    value_exists aR vR -> vR > v.
intros.
induction H0.
inversion H.
inversion H4.
omega.
apply IHvalue_exists.
inversion H.
apply_is_ABR.
inversion H5.
eapply both_lower.
apply H11.
apply IHvalue_exists.
inversion H.
apply_is_ABR.
inversion H5.
eapply left_loosen.
apply H12.
omega.
Qed.

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
contradict b0.
eapply left_less.
apply H.
apply H0.
simpl.
elim (Z.eq_dec vR v); intro; auto.
elim (Z_le_dec vR v); intro; auto.
destruct a.
eapply right_more.
apply H.
apply H0.
apply IHvalue_exists.
inversion H.
eapply both_option_reduce.
apply H5.
Qed.


Fixpoint insert (arbre : AB) (v : Z) : AB :=
  match arbre with
  | Empty => (Node v Empty Empty)
  | Node w aL aR =>
    if Z.eq_dec v w then arbre
    else if Z_le_dec v w then (Node w (insert aL v) aR)
    else (Node w aL (insert aR v))
end.

Functional Scheme insert_ind := Induction for insert Sort Prop.

Lemma insert_is_ABR : forall (v : Z) (a_in a_out : AB), is_ABR a_in None None ->
    a_out = (insert a_in v) -> is_ABR a_out None None.
intro.
intro.
intro.
intro.
intro.
functional induction (insert a_in v) using insert_ind; intros.
rewrite e.
apply_is_ABR.
inversion H.
assumption.
inversion H.
assumption.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H3.
rewrite H0.



Lemma left_limit : forall (arbre : AB) (v vL vR : Z), is_ABR arbre (Some vL) None ->
    value_exists arbre v -> vL <= v.
intros.
induction H0.
inversion H.
omega.
apply IHvalue_exists.
inversion H.
eapply both_lower.
apply H6.
apply IHvalue_exists.















Lemma limits_inherit : forall (aL aR : AB) (v vL : Z), is_ABR (Node v aL aR) (Some vL) None ->
    is_ABR aL (Some vL) None.
intros.
induction aL.
apply_is_ABR.
inversion H.
inversion H5.
omega.






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
contradict b0.
inversion H.
induction (Left v vL aL aR).
inversion H3.
inversion H0.
rewrite <- H1 in H.
inversion H.
inversion H5.
omega.
rewrite <- H2 in H.
inversion H.
inversion H6.
inversion H14.



Theorem insert_sound : forall (v : Z) (a_in a_out : AB), is_ABR a_in None None ->
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











