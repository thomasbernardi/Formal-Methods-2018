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
  | Empty_B : forall (vL vR : Z), vL < vR -> is_ABR Empty (Some vL) (Some vR)
  | No_Limits : forall (v : Z) (aL aR : AB), is_ABR aL None (Some v) -> is_ABR aR (Some v) None -> 
    is_ABR (Node v aL aR) None None
  | Lower : forall (v vL : Z) (aL aR : AB), v > vL -> is_ABR aL (Some vL) (Some v) ->
    is_ABR aR (Some v) None -> is_ABR (Node v aL aR) (Some vL) None
  | Upper : forall (v vR : Z) (aL aR : AB), v <= vR -> is_ABR aL None (Some v) ->
    is_ABR aR (Some v) (Some vR) -> is_ABR (Node v aL aR) None (Some vR)
  | Both : forall (v vL vR : Z) (aL aR : AB), v > vL -> v < vR -> is_ABR aL (Some vL) (Some v) ->
    is_ABR aR (Some v) (Some vR) -> is_ABR (Node v aL aR) (Some vL) (Some vR).

Definition benchmark_01 := (Node 3 (Node 1 (Node 0 Empty Empty) (Node 2 Empty Empty)) (Node 5 Empty Empty)).
Definition benchmark_02 := (Node 5 (Node 3 (Node 2 Empty Empty) (Node 4 Empty Empty)) (Node 7 (Node 6 Empty Empty) (Node 8 Empty Empty))).
Definition benchmark_03 := (Node 16 (Node 10 (Node 9 (Node 5 Empty Empty) Empty) (Node 14 (Node 11 Empty (Node 12 Empty Empty)) (Node 15 Empty Empty))) (Node 18 (Node 17 Empty Empty) (Node 19 Empty (Node 20 Empty Empty)))).

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
Qed.

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

Lemma limits : forall (arbre : AB) (vL vR : Z), is_ABR arbre (Some vL) (Some vR) -> vL < vR.
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
inversion H.
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
    value_exists aL vL -> vL < v.
intros.
induction H0.
inversion H.
inversion H2.
eapply limits.
apply H11.
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
cut (vL < v).
omega.
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
    else if Z_lt_dec v w then (Node w (insert aL v) aR)
    else (Node w aL (insert aR v))
end.

Functional Scheme insert_ind := Induction for insert Sort Prop.

Lemma combine : forall (vL vR : Z) (arbre : AB), is_ABR arbre None (Some vR) ->
    is_ABR arbre (Some vL) None -> vL < vR -> is_ABR arbre (Some vL) (Some vR).
intros.
induction arbre.
apply_is_ABR.
inversion H0.
omega.
inversion H.
eapply limits.
apply H8.
inversion H0.
assumption.
inversion H.
assumption.
apply_is_ABR.
Qed.

Lemma insert_right : forall (v vR : Z) (arbre : AB), is_ABR arbre None (Some vR) ->
    is_ABR (insert arbre v) None None -> v < vR -> is_ABR (insert arbre v) None (Some vR).
intros.
functional induction (insert arbre v) using insert_ind; intros.
assumption.
apply_is_ABR.
inversion H.
omega.
inversion H0.
assumption.
inversion H.
assumption.
apply_is_ABR.
inversion H.
inversion H.
assumption.
inversion H0.
apply combine.
apply IHa.
eapply both_upper.
inversion H.
apply H13.
eapply both_option_reduce.
apply H6.
assumption.
assumption.
omega.
apply_is_ABR.
Qed.

Lemma insert_left : forall (v vL : Z) (arbre : AB), is_ABR arbre (Some vL) None ->
    is_ABR (insert arbre v) None None -> v > vL -> is_ABR (insert arbre v) (Some vL) None.
intros.
functional induction (insert arbre v) using insert_ind; intros.
assumption.
apply_is_ABR.
apply combine.
inversion H0.
assumption.
apply IHa.
inversion H.
eapply both_lower.
apply H7.
inversion H0.
eapply both_option_reduce.
apply H4.
omega.
omega.
inversion H.
assumption.
apply_is_ABR.
inversion H.
omega.
inversion H.
assumption.
inversion H0.
assumption.
apply_is_ABR.
Qed.

Lemma insert_is_ABR : forall (v : Z) (a_in : AB), is_ABR a_in None None ->
    is_ABR (insert a_in v) None None.
intro.
intro.
intro.
functional induction (insert a_in v) using insert_ind; intros.
apply_is_ABR.
inversion H.
assumption.
inversion H.
assumption.
apply_is_ABR.
inversion H.
eapply insert_right; auto.
apply IHa.
eapply both_option_reduce.
apply H2.
inversion H.
assumption.
inversion H.
apply_is_ABR.
apply insert_left; auto.
apply IHa.
eapply both_option_reduce.
apply H4.
omega.
apply_is_ABR.
Qed.

Lemma insert_new_value : forall (v : Z) (a_in : AB), is_ABR a_in None None ->
    value_exists (insert a_in v) v.
intros.
functional induction (insert a_in v) using insert_ind; intros.
apply Curr.
apply Left.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H2.
apply Right.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H4.
apply Curr.
Qed.

Lemma insert_no_loss : forall (v : Z) (a_in : AB), is_ABR a_in None None ->
    (forall (w : Z), value_exists a_in w -> value_exists (insert a_in v) w).
intros.
functional induction (insert a_in v) using insert_ind; intros.
assumption.
inversion H0.
apply Curr.
apply Left.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H8.
assumption.
apply Right.
assumption.
inversion H0.
apply Curr.
apply Left.
assumption.
apply Right.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H10.
assumption.
inversion H0.
Qed.

Theorem insert_sound : forall (v : Z) (a_in a_out : AB), is_ABR a_in None None -> a_out = (insert a_in v) ->
    is_ABR a_out None None /\ value_exists a_out v /\ (forall (w : Z), value_exists a_in w -> value_exists a_out w).
intros.
rewrite H0.
split.
apply insert_is_ABR.
assumption.
split.
apply insert_new_value.
assumption.
apply insert_no_loss.
assumption.
Qed.

Fixpoint find_max (arbre : AB) : option Z :=
  match arbre with
  | Empty => None
  | (Node x _ Empty) => (Some x)
  | (Node x _ aR) => find_max aR
end.

Fixpoint delete (arbre : AB) (v : Z) : AB :=
  match arbre with
  | Empty => Empty
  | (Node w aL aR) =>
    if Z.eq_dec w v then 
    match aL, aR with
    | Empty, aR => aR
    | aL, Empty => aL
    | aL, aR => let max := find_max aL in
      match max with
      | None => aR
      | Some x => (Node x (delete aL x) aR)
    end
   end
    else if Z_lt_dec v w then (Node w (delete aL v) aR)
    else (Node w aL (delete aR v))
end.

Functional Scheme find_max_ind := Induction for find_max Sort Prop.
Functional Scheme delete_ind := Induction for delete Sort Prop.

Lemma max_gt : forall (arbre : AB) (x vR : Z) (L : option Z), is_ABR arbre L (Some vR) ->
    (find_max arbre) = (Some x) -> x < vR.
intros.
functional induction (find_max arbre) using find_max_ind.
apply IHo.
inversion H.
eapply both_upper.
apply H8.
apply combine.
eapply both_upper.
apply H9.
eapply left_loosen.
eapply both_lower.
apply H9.
cut (vL < x0); omega.
cut (vL < x0); omega.
apply H0.
inversion H0.
rewrite <- H2.
inversion H.
eapply limits.
apply H9.
eapply limits.
apply H10.
inversion H0.
Qed.

Lemma min_less : forall (arbre : AB) (x vL : Z) (R : option Z), is_ABR arbre (Some vL) R ->
    find_max arbre = (Some x) -> x > vL.
intros.
functional induction (find_max arbre) using find_max_ind.
apply IHo.
inversion H.
eapply left_loosen.
apply H8.
cut (vL < x0).
omega.
eapply limits.
apply H7.
apply combine.
eapply both_upper.
apply H9.
eapply left_loosen.
eapply both_lower.
apply H9.
cut (vL < x0).
omega.
eapply limits.
apply H8.
cut (vL < x0).
omega.
eapply limits.
apply H8.
auto.
inversion H0.
rewrite <- H2.
inversion H; omega.
inversion H0.
Qed.

Lemma max_limit : forall (arbre : AB) (x : Z), is_ABR arbre None None -> 
    (find_max arbre) = (Some x) -> is_ABR arbre None (Some (x + 1)).
intros.
functional induction (find_max arbre) using find_max_ind.
apply_is_ABR.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (x + 1))).
intros.
inversion H1.
inversion H.
inversion H13.
omega.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H5.
auto.
inversion H.
auto.
inversion H.
inversion H5.
omega.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (x + 1))).
intros.
inversion H1.
eapply limits.
apply combine.
eapply right_loosen.
eapply both_upper.
apply H8.
omega.
eapply both_lower.
apply H8.
eapply limits.
apply H8.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H5.
auto.
inversion H.
inversion H5.
auto.
inversion H.
inversion H5.
apply combine.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (x + 1))).
intros.
inversion H13.
eapply both_upper.
apply H20.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H5.
auto.
apply H12.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (x + 1))).
intros.
inversion H13.
eapply limits.
apply H20.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H5.
auto.
inversion H.
inversion H0.
apply_is_ABR.
rewrite <- H7.
auto.
inversion H0.
Qed.

Lemma delete_right : forall (arbre : AB) (v vR : Z), is_ABR arbre None (Some vR) ->
    is_ABR (delete arbre v) None None -> is_ABR (delete arbre v) None (Some vR).
intros.
functional induction (delete arbre v) using delete_ind; apply_is_ABR.
cut (x < vR).
omega.
eapply max_gt.
inversion H.
eapply right_loosen.
apply H6.
omega.
apply e3.
inversion H0.
simpl.
auto.
inversion H0.
inversion H5.
omega.
inversion H.
inversion H7.
omega.
inversion H.
inversion H7.
apply combine.
eapply both_upper.
apply H15.
eapply left_loosen.
eapply both_lower.
apply H15.
cut (x < w).
omega.
eapply max_gt.
apply H6.
auto.
inversion H0.
inversion H21.
omega.
inversion H.
inversion H7.
apply H16.
inversion H.
inversion H7.
omega.
inversion H0.
auto.
inversion H.
inversion H7.
auto.
inversion H.
inversion H6.
cut (w < vR).
omega.
eapply limits.
apply H7.
inversion H.
inversion H6.
auto.
inversion H.
inversion H6.
apply combine.
eapply right_loosen.
eapply both_upper.
apply H14.
cut (w < vR).
omega.
eapply limits.
apply H7.
eapply both_lower.
apply H14.
cut (w < vR).
omega.
eapply limits.
apply H7.
inversion H.
eapply both_upper.
apply H7.
inversion H.
omega.
inversion H0.
apply H3.
inversion H.
auto.
inversion H.
auto.
inversion H.
auto.
inversion H0.
inversion H.
apply combine.
apply IHa.
eapply both_upper.
apply H12.
eapply both_option_reduce.
apply H5.
auto.
eapply limits.
apply H12.
Qed.

Lemma delete_left : forall (arbre : AB) (v vL : Z), is_ABR arbre (Some vL) None ->
    is_ABR (delete arbre v) None None -> is_ABR (delete arbre v) (Some vL) None.
intros.
functional induction (delete arbre v) using delete_ind; apply_is_ABR.
eapply min_less.
inversion H.
apply H6.
auto.
apply combine.
inversion H0.
simpl.
auto.
apply IHa.
inversion H.
eapply both_lower.
apply H6.
eapply both_option_reduce.
simpl.
inversion H0.
apply H3.
cut (x > vL).
omega.
eapply min_less.
inversion H.
apply H6.
auto.
cut (x <= w).
intro.
inversion H.
inversion H8.
omega.
cut (x < w).
omega.
eapply max_gt.
inversion H.
apply H6.
auto.
inversion H.
inversion H7.
apply combine.
eapply both_upper.
apply H13.
eapply left_loosen.
eapply both_lower.
apply H13.
cut (x < w).
omega.
eapply max_gt.
apply H6.
auto.
cut (x < w).
omega.
eapply max_gt.
apply H6.
auto.
inversion H.
inversion H7.
auto.
inversion H.
inversion H7.
auto.
cut (vL < w).
omega.
eapply limits.
apply H6.
inversion H.
inversion H7.
apply combine.
eapply both_upper.
apply H13.
eapply left_loosen.
eapply both_lower.
apply H13.
cut (vL < w).
omega.
eapply limits.
apply H6.
cut (vL < w).
omega.
eapply limits.
apply H6.
inversion H.
inversion H7.
auto.
inversion H.
inversion H6.
omega.
inversion H.
inversion H6.
auto.
inversion H.
inversion H6.
eapply both_lower.
apply H16.
inversion H.
eapply left_loosen.
apply H7.
cut (vL < w).
omega.
eapply limits.
apply H6.
inversion H.
omega.
apply combine.
inversion H0.
auto.
apply IHa.
inversion H.
eapply both_lower.
apply H6.
inversion H0.
eapply both_option_reduce.
apply H3.
inversion H.
omega.
inversion H.
auto.
inversion H.
omega.
inversion H.
auto.
inversion H0.
auto.
Qed.

Lemma max_deleted_limit : forall (arbre : AB) (v : Z), is_ABR arbre None None ->
    (find_max arbre) = (Some v) -> is_ABR (delete arbre v) None (Some v).
intro.
intro.
intro.
functional induction (find_max arbre) using find_max_ind; intros.
inversion H.
unfold delete at 1.
elim (Z.eq_dec x v); intros.
contradict a.
cut (x < v).
omega.
cut (_x0 < v + 1).
intros.
inversion H5.
omega.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (v + 1))).
intros.
inversion H6.
eapply limits.
apply H13.
eapply max_limit.
eapply both_option_reduce.
apply H5.
auto.
elim (Z_lt_dec v x); intros.
contradict a.
cut (x < v).
omega.
cut (_x0 < v + 1).
intros.
inversion H5.
omega.
cut (is_ABR (Node _x0 _x1 _x2) None (Some (v + 1))).
intros.
inversion H6.
eapply limits.
apply H13.
eapply max_limit.
eapply both_option_reduce.
apply H5.
auto.
apply_is_ABR.
fold (delete (Node _x0 _x1 _x2) v).
apply combine.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H10.
apply H0.
eapply delete_left.
apply H5.
eapply both_option_reduce.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H10.
auto.
omega.
unfold delete.
elim (Z.eq_dec x v); intros.
inversion H.
inversion H0.
case_eq _x; intros.
rewrite <- H6.
rewrite <- H7.
auto.
rewrite <- H6.
rewrite <- H7.
auto.
contradict b.
inversion H0.
reflexivity.
inversion H0.
Qed.

Lemma delete_is_ABR : forall (arbre : AB) (v : Z), is_ABR arbre None None ->
    is_ABR (delete arbre v) None None.
intros.
functional induction (delete arbre v) using delete_ind; apply_is_ABR.
inversion H.
eapply max_deleted_limit.
eapply both_option_reduce.
apply H2.
auto.
inversion H.
cut (x < w).
inversion H4.
omega.
eapply max_gt.
apply H2.
auto.
inversion H.
inversion H4.
apply combine.
eapply both_upper.
apply H10.
eapply left_loosen.
eapply both_lower.
apply H10.
cut (x < w).
omega.
eapply max_gt.
apply H2.
auto.
cut (x < w).
omega.
eapply max_gt.
apply H2.
auto.
inversion H.
inversion H4.
auto.
inversion H.
inversion H4.
eapply both_upper.
apply H10.
inversion H.
inversion H4.
auto.
inversion H.
inversion H2.
auto.
inversion H.
inversion H2.
eapply both_lower.
apply H11.
inversion H.
eapply both_option_reduce.
apply H4.
eapply delete_right.
inversion H.
auto.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H2.
inversion H.
auto.
inversion H.
auto.
eapply delete_left.
inversion H.
auto.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H4.
Qed.

Lemma max_exists : forall (v : Z) (arbre : AB), is_ABR arbre None None ->
    (find_max arbre) = (Some v) -> value_exists arbre v.
intros.
functional induction (find_max arbre) using find_max_ind.
apply Right.
apply IHo.
inversion H.
eapply both_option_reduce.
apply H5.
auto.
inversion H0.
rewrite <- H2.
apply Curr.
inversion H0.
Qed.

Lemma left_DNE : forall (v : Z) (arbre : AB), is_ABR arbre (Some v) None ->
    ~ (value_exists arbre v).
intros.
intro.
induction H0.
inversion H.
cut (v < v).
omega.
eapply limits.
apply H5.
apply IHvalue_exists.
inversion H.
eapply both_lower.
apply H6.
apply IHvalue_exists.
inversion H.
eapply left_loosen.
apply H7.
cut (vR < v).
omega.
eapply limits.
apply H6.
Qed.

Lemma right_DNE : forall (v : Z) (arbre : AB), is_ABR arbre None (Some v) ->
    ~ (value_exists arbre v).
intros.
intro.
induction H0.
inversion H.
cut (v < v).
omega.
eapply limits.
apply H6.
apply IHvalue_exists.
inversion H.
eapply right_loosen.
apply H6.
cut (v < vL).
omega.
eapply limits.
apply H7.
apply IHvalue_exists.
inversion H.
eapply both_upper.
apply H7.
Qed.

Lemma ind_DNE : forall (v x : Z) (aL aR : AB), ~(value_exists aL v) -> ~(value_exists aR v) ->
    x <> v -> ~(value_exists (Node x aL aR) v).
intros.
intro.
inversion H2.
contradict H3.
auto.
contradict H7.
auto.
contradict H7.
auto.
Qed.

Lemma combined_DNE : forall (v x : Z) (aL aR : AB), is_ABR (Node v aL aR) None None ->
    x <> v -> ~ (value_exists (Node x aL aR) v).
intros.
intro.
inversion H1.
contradict H2.
auto.
contradict H6.
eapply right_DNE.
inversion H.
auto.
contradict H6.
eapply left_DNE.
inversion H.
auto.
Qed.

Lemma benchmark_test : value_exists benchmark_03 10.
eapply search_sound.
apply_is_ABR.
simpl.
auto.
Qed.

Lemma berchmark_test_delete : search (delete benchmark_03 10) 10 = false.
simpl.
auto.
Qed.

Lemma deleted_DNE : forall (v : Z) (arbre : AB), is_ABR arbre None None -> 
    ~ (value_exists (delete arbre v) v).
intros.
functional induction (delete arbre v) using delete_ind; intros.
eapply combined_DNE.
apply_is_ABR.
eapply delete_right.
inversion H.
auto.
eapply delete_is_ABR.
inversion H.
eapply both_option_reduce.
apply H2.
inversion H.
inversion H4.
auto.
inversion H.
inversion H4.
auto.
inversion H.
inversion H4.
auto.
inversion H.
cut (x < w).
omega.
eapply max_gt.
apply H2.
auto.
eapply left_DNE.
inversion H.
auto.
eapply right_DNE.
inversion H.
auto.
eapply left_DNE.
inversion H.
auto.
eapply ind_DNE.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H2.
eapply left_DNE.
inversion H.
eapply left_loosen.
apply H4.
omega.
auto.
eapply ind_DNE.
eapply right_DNE.
inversion H.
eapply right_loosen.
apply H2.
omega.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H4.
auto.
intro.
inversion H0.
Qed.

Lemma max_node_exists : forall (v : Z) (aL aR : AB), is_ABR (Node v aL aR) None None ->
    find_max (Node v aL aR) <> None.
intros.
simpl.
functional induction (find_max aR) using find_max_ind.
apply IHo.
inversion H.
inversion H4.
inversion H11.
apply_is_ABR.
apply combine.
eapply both_upper.
apply H17.
eapply left_loosen.
eapply both_lower.
apply H17.
cut (v < x).
omega.
eapply limits.
apply H10.
cut (v < x).
omega.
eapply limits.
apply H10.
intro.
inversion H0.
intro.
inversion H0.
Qed.

Lemma delete_no_loss : forall (v x : Z) (arbre : AB), is_ABR arbre None None -> x <> v ->
    value_exists arbre v -> value_exists (delete arbre x) v.
intros.
functional induction (delete arbre x) using delete_ind.
case_eq (Z.eq_dec v x); intros.
rewrite e.
apply Curr.
inversion H1.
contradict H3.
auto.
apply Left.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H10.
omega.
auto.
apply Right.
auto.
contradict e3.
apply max_node_exists.
inversion H.
eapply both_option_reduce.
apply H4.
inversion H1.
contradict H2.
auto.
auto.
inversion H6.
inversion H1.
contradict H2.
auto.
inversion H6.
auto.
inversion H1.
apply Curr.
apply Left.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H9.
auto.
auto.
apply Right.
auto.
inversion H1.
apply Curr.
apply Left.
auto.
apply Right.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H11.
auto.
auto.
inversion H1.
Qed.

Theorem delete_sound : forall (v : Z) (a_in a_out : AB), is_ABR a_in None None -> a_out = (delete a_in v) ->
    is_ABR a_out None None /\ ~(value_exists a_out v) /\ (forall (w : Z), w <> v -> value_exists a_in w -> value_exists a_out w).
intros.
rewrite H0.
split.
apply delete_is_ABR.
auto.
split.
apply deleted_DNE.
auto.
intros.
apply delete_no_loss; auto.
Qed.
