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

Lemma combine : forall (vL vR : Z) (arbre : AB), is_ABR arbre None (Some vR) ->
    is_ABR arbre (Some vL) None -> vL <= vR -> is_ABR arbre (Some vL) (Some vR).
intros.
induction arbre.
apply_is_ABR.
inversion H0.
omega.
inversion H.
omega.
inversion H0.
assumption.
inversion H.
assumption.
apply_is_ABR.
Qed.

Lemma insert_right : forall (v vR : Z) (arbre : AB), is_ABR arbre None (Some vR) ->
    is_ABR (insert arbre v) None None -> v <= vR -> is_ABR (insert arbre v) None (Some vR).
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

Lemma max_geq : forall (arbre : AB) (x vR : Z) (L : option Z), is_ABR arbre L (Some vR) ->
    (find_max arbre) = (Some x) -> x <= vR.
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
eapply limits.
apply H8.
inversion H9.
cut (vL <= x0).
omega.
eapply limits.
apply H8.
apply H0.
inversion H0.
rewrite <- H2.
inversion H; omega.
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
eapply limits.
apply H7.
apply combine.
eapply both_upper.
apply H9.
eapply left_loosen.
eapply both_lower.
apply H9.
eapply limits.
apply H8.
cut (vL <= x0).
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
    (find_max arbre) = (Some x) -> is_ABR arbre None (Some x).
intros.
functional induction (find_max arbre) using find_max_ind.
apply_is_ABR.
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
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
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
intros.
inversion H1.
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
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
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
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
intros.
inversion H13.
omega.
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
eapply max_geq.
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
eapply max_geq.
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
cut (w <= vR).
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
eapply limits.
apply H7.
eapply both_lower.
apply H14.
cut (w <= vR).
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
eapply max_geq.
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
eapply max_geq.
apply H6.
auto.
cut (x <= w).
omega.
eapply max_geq.
apply H6.
auto.
inversion H.
inversion H7.
auto.
inversion H.
inversion H7.
auto.
cut (vL <= w).
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
eapply limits.
apply H6.
cut (vL <= w).
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



Lemma delete_is_ABR : forall (arbre : AB) (v : Z), is_ABR arbre None None ->
    is_ABR (delete arbre v) None None.
intros.
functional induction (delete arbre v) using delete_ind; apply_is_ABR.
eapply delete_right.
apply_is_ABR.
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
intros.
inversion H0.
eapply limits.
apply H7.
eapply max_limit.
inversion H.
eapply both_option_reduce.
apply H2.
apply e3.
inversion H.
inversion H2.
apply H10.
inversion H.
inversion H2.
apply combine.
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
intros.
inversion H12.
eapply both_upper.
apply H19.
eapply max_limit.
eapply both_option_reduce.
apply H2.
auto.
eapply both_lower.
apply H11.
cut (is_ABR (Node _x0 _x1 _x2) None (Some x)).
intros.
inversion H12.
omega.
eapply max_limit.
inversion H.
eapply both_option_reduce.
apply H14.
auto.
apply IHa.
inversion H.
eapply both_option_reduce.
apply H2.
inversion H.
inversion H4.
cut (x <= w).
omega.
eapply max_geq.
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
eapply max_geq.
apply H2.
auto.
cut (x <= w).
omega.
eapply max_geq.
apply H2.
auto.
inversion H.
inversion H4.
apply H11.
inversion H.
inversion H4.
eapply both_upper.
apply H10.
inversion H.
inversion H4.
apply H11.
inversion H.
inversion H2.
apply H10.
inversion H.
inversion H2.
eapply both_lower.
apply H11.
inversion H.
eapply both_option_reduce.
apply H4.
eapply delete_right.
inversion H.
apply H2.
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

Fixpoint delete_all (arbre : AB) (v : Z) {struct arbre} : AB :=
  let del_one := (delete arbre v) in
  if (search del_one v) then (delete_all del_one v) else del_one.

Fixpoint leftmost_value (v : Z) (aL : AB) : Z :=
  match aL with
  | Empty => v
  | (Node vL aLL aLR) => leftmost_value vL aLL
end.

Fixpoint delete_leftmost (arbre : AB) : AB :=
  match arbre with
  | Empty => Empty
  | (Node v aL aR) =>
    match aL with
    | Empty => aR
    | (Node vL aLL aLR) => (Node v (delete_leftmost aL) aR)
  end
end.

Fixpoint 
delete (arbre : AB) (v : Z) : AB :=
  match arbre with
  | Empty => Empty
  | (Node w aL aR) =>
    let del_1 := match aL with
    | Empty =>
      match aR with
      | Empty =>
        if Z.eq_dec w v then Empty
        else arbre
      | (Node vR aRL aRR) =>
        if Z.eq_dec w v then aR
        else (Node w Empty (delete aR v))
    end
    | (Node vL aLL aLR) =>
      match aR with
      | Empty =>
        if Z.eq_dec w v then aL
        else (Node w (delete aL v) Empty)
      | (Node vR aRL aRR) =>
        if Z.eq_dec w v then (Node (leftmost_value vR aRL) aL (delete_leftmost aR) )
        else if Z_le_dec w v then (Node w (delete aL v) aR)
        else (Node w aL (delete aR v))
    end
  end
    in if (search del_1 v) then (delete del_1 v) else del_1
end.
Functional Scheme lval_ind := Induction for leftmost_value Sort Prop.
Functional Scheme ldel_ind := Induction for delete_leftmost Sort Prop.
Functional Scheme delete_ind := Induction for delete Sort Prop.

Lemma limit_inherit_left : forall (v : Z) (aL aR : AB) (L R : option Z), is_ABR (Node v aL aR) L R ->
    is_ABR aL L (Some v).
intros.
inversion H; assumption.
Qed.

Lemma delete_left : forall (vR : Z) (arbre : AB) (L R : option Z), is_ABR arbre L (Some vR) ->
    is_ABR (delete_leftmost arbre) L R -> is_ABR (delete_leftmost arbre) L (Some vR).
intros.
functional induction (delete_leftmost arbre) using ldel_ind; intros; apply_is_ABR.
inversion H; apply_is_ABR.
eapply limit_inherit_left.
rewrite H5.
apply H0.
rewrite H6.
eapply limit_inherit_left.
apply H0.
inversion H.
eapply both_upper.
apply H8.
eapply combine.
eapply both_upper.
apply H9.
eapply left_loosen.
eapply both_lower.
apply H9.
omega.
omega.
Qed.

Lemma left_delete_is_ABR : forall (arbre : AB) (L R : option Z), is_ABR arbre L R ->
    is_ABR (delete_leftmost arbre) L R.
intros.
functional induction (delete_leftmost arbre) using ldel_ind; intros; apply_is_ABR.
inversion H; apply_is_ABR.
eapply delete_left.
apply H5.
rewrite H2.
apply IHa.
rewrite <- H2.
rewrite <- H4.
eapply both_option_reduce.
apply H5.
eapply delete_left.
assumption.
rewrite H4.
apply IHa.
rewrite <- H4.
rewrite <- H5.
eapply both_lower.
apply H6.
eapply delete_left.
assumption.
rewrite H4.
apply IHa.
rewrite <- H4.
rewrite <- H5.
eapply right_loosen.
apply H6.
assumption.
eapply delete_left.
assumption.
rewrite H5.
apply IHa.
rewrite <- H5.
rewrite <- H6.
apply combine.
eapply right_loosen.
eapply both_upper.
apply H7.
assumption.
eapply both_lower.
apply H7.
omega.
inversion H.
eapply both_option_reduce.
apply H6.
eapply left_loosen.
apply H7.
omega.
eapply both_upper.
apply H7.
apply combine.
eapply both_upper.
apply H8.
eapply left_loosen.
eapply both_lower.
apply H8.
omega.
omega.
Qed.

Lemma leftmost_within_left : forall (v vL: Z) (aL aR : AB) (R : option Z), is_ABR (Node v aL aR) (Some vL) R ->
    vL < leftmost_value v aL .
intros.
functional induction (leftmost_value v aL) using lval_ind; intros.
apply IHz.
inversion H.
apply_is_ABR.
inversion H6.
assumption.
inversion H6.
assumption.
eapply left_loosen.
apply H7.
inversion H6.
assumption.
apply_is_ABR.
inversion H7.
assumption.
inversion H7.
omega.
inversion H7.
assumption.
apply combine.
eapply both_upper.
apply H8.
eapply left_loosen.
eapply both_lower.
apply H8.
inversion H7.
assumption.
inversion H7.
omega.
inversion H.
inversion H6.
omega.
inversion H7.
omega.
Qed.

Lemma limits_inequality : forall (v vL vR : Z) (aL aR : AB), is_ABR (Node v aL aR) (Some vL) (Some vR) -> vR > vL.
intros.
inversion H.
inversion H7.
inversion H8.
omega.
omega.
omega.
Qed.

Lemma leftmost_within_right : forall (v vR: Z) (aL aR : AB) (L : option Z), is_ABR (Node v aL aR) L (Some vR) ->
    vR >= leftmost_value v aL .
intros.
functional induction (leftmost_value v aL) using lval_ind; intros.
apply IHz.
inversion H.
inversion H6.
apply_is_ABR.
apply combine.
eapply both_upper.
apply H7.
eapply left_loosen.
eapply both_lower.
apply H7.
omega.
omega.
inversion H7.
apply_is_ABR.
apply combine.
eapply both_upper.
apply H8.
eapply left_loosen.
eapply both_lower.
apply H8.
omega.
omega.
inversion H.
omega.
omega.
Qed.

Lemma delete_is_ABR : forall (arbre : AB) (v : Z), is_ABR arbre None None ->
    is_ABR (delete arbre v) None None.
intros.
functional induction (delete arbre v) using delete_ind; intros; apply_is_ABR.
apply Z.lt_le_incl.
eapply leftmost_within_left.
inversion H.
inversion H2.
eapply left_loosen.
apply H4.
omega.
inversion H.
inversion H2.
auto.
inversion H.
inversion H2.
apply combine.
eapply right_loosen.
eapply both_upper.
apply H11.
apply Z.lt_le_incl.
eapply leftmost_within_left.
apply H4.
eapply both_lower.
apply H11.
apply Z.lt_le_incl.
eapply leftmost_within_left.
eapply left_loosen.
apply H4.
omega.
inversion H.
eapply left_delete_is_ABR.
apply_is_ABR.

Lemma delete_left_is_ABR : 


Hypotheses:
H : is_ABR (Node w (Node _x _x0 _x1) (Node vR aRL _x2)) None None
e2 : Z.eq_dec w w = left eq_refl
v : Z
aL, aR : AB
H2 : is_ABR (Node _x _x0 _x1) None (Some w)
H4 : is_ABR (Node vR aRL _x2) (Some w) None
H0 : v = w
H1 : aL = Node _x _x0 _x1
H3 : aR = Node vR aRL _x2


Goal:
is_ABR (delete_leftmost (Node vR aRL _x2)) (Some (leftmost_value vR aRL)) None


Lemma left_swap : forall (v v1 v2 : Z) (arbre : AB) (L R : option Z), is_ABR arbre L R ->
    v2 < (leftmost_value v1 arbre) -> v2 < v1 -> v < v1 -> v < (leftmost_value v2 arbre).
intros.
functional induction (leftmost_value v2 arbre) using lval_ind; intros.
apply IHz.
inversion H.
eapply both_option_reduce.
apply H8.
eapply both_lower.
apply H9.
eapply right_loosen.
apply H9.
assumption.
eapply combine.
eapply right_loosen.
eapply both_upper.
apply H10.
assumption.
eapply both_lower.
apply H10.
omega.







