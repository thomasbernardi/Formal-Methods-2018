Require Export ZArith.
Require Export FunInd.
Open Scope Z_scope.

Inductive expr : Set :=
  | Cte : Z -> expr
  | Var : nat -> expr
  | Plus : expr -> expr -> expr
  | Moins : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Div : expr -> expr -> expr .

Inductive value : Set :=
  | Val : Z -> value
  | Err : value.

Definition context := nat -> (option Z).

Inductive eval (env : context) : expr -> value -> Prop :=
  | ECte : forall c : Z, eval env (Cte c) (Val c)
  | EVar : forall (n : nat) (v : Z), (env n) = Some v -> eval env (Var n) (Val v)
  | EVar_Err : forall (n : nat), (env n) = None -> eval env (Var n) Err
  | EPlus : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (Val v1) -> eval env e2 (Val v2)
    -> v = v1 + v2 -> eval env (Plus e1 e2) (Val v)
  | EPlus_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Plus e1 e2) Err
  | EPlus_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (Val v) -> eval env e2 Err
    -> eval env (Plus e1 e2) Err
  | EMoins : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (Val v1) -> eval env e2 (Val v2)
    -> v = v1 - v2 -> eval env (Moins e1 e2) (Val v)
  | EMoins_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Moins e1 e2) Err
  | EMoins_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (Val v) -> eval env e2 Err
    -> eval env (Moins e1 e2) Err
  | EMult : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (Val v1) -> eval env e2 (Val v2)
    -> v = v1 * v2 -> eval env (Mult e1 e2) (Val v)
  | EMult_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Mult e1 e2) Err
  | EMult_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (Val v) -> eval env e2 Err
    -> eval env (Mult e1 e2) Err
  | EDiv : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (Val v1) -> eval env e2 (Val v2)
    -> v = v1 / v2 -> eval env (Div e1 e2) (Val v)
  | EDiv_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Div e1 e2) Err
  | EDiv_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (Val v) -> eval env e2 Err
    -> eval env (Div e1 e2) Err.

Definition env0 (n : nat) : (option Z) :=
  match n with
  | 0%nat => Some 2
  | _ => None
  end.

Lemma eval0 : eval env0 (Mult (Plus (Cte 4) (Var 0)) (Moins (Cte 9) (Var 0))) (Val 42).
  eapply EMult.
  eapply EPlus.
  apply ECte.
  apply EVar.
  simpl.
  auto.
  auto.
  eapply EMoins.
  apply ECte.
  apply EVar.
  simpl.
  auto.
  auto.
  auto.
Qed.

Lemma eval1 : eval env0 (Mult (Plus (Cte 3) (Var 1)) (Moins (Cte 9) (Var 0))) Err.
  eapply EMult_ErrL.
  eapply EPlus_ErrR.
  eapply ECte.
  eapply EVar_Err.
  auto.
Qed.

Ltac apply_eval_val :=
  repeat
  eapply EPlus || eapply EMoins || eapply EMult || eapply EDiv ||
  apply ECte || apply EVar || simpl || auto.

Ltac apply_eval_err :=
  match goal with
  | |- eval _ (Var _) Err => apply EVar_Err; simpl; auto
  | |- eval _ (Plus _ _) Err => 
        (eapply EPlus_ErrL; apply_eval_err) ||
        (eapply EPlus_ErrR; [ apply_eval_val | apply_eval_err ])
  | |- eval _ (Moins _ _) Err => 
        (eapply EMoins_ErrL; apply_eval_err) ||
        (eapply EMoins_ErrR; [ apply_eval_val | apply_eval_err ])
  | |- eval _ (Mult _ _) Err => 
        (eapply EMult_ErrL; apply_eval_err) ||
        (eapply EMult_ErrR; [ apply_eval_val | apply_eval_err ])
  | |- eval _ (Div _ _) Err => 
        (eapply EDiv_ErrL; apply_eval_err) ||
        (eapply EDiv_ErrR; [ apply_eval_val | apply_eval_err ])
end.

Lemma eval0_2 : eval env0 (Mult (Plus (Cte 4) (Var 0)) (Moins (Cte 9) (Var 0))) (Val 42).
  apply_eval_val.
Qed.

Lemma eval1_2 : eval env0 (Mult (Plus (Cte 3) (Var 1)) (Moins (Cte 9) (Var 0))) Err.
  apply_eval_err.
Qed.

Fixpoint f_eval (env : context) (e : expr) : value :=
  match e with
  | Cte c => Val c
  | Var n => match (env n) with
    | Some v => Val v
    | None => Err
    end
  | Plus e1 e2 =>
    let v1 := f_eval env e1 in
    match v1 with
    | Err => Err
    | Val g1 => 
      let v2 := f_eval env e2 in
      match v2 with
      | Err => Err
      | Val g2 => Val (g1 + g2)
      end
     end
  | Moins e1 e2 =>
    let v1 := f_eval env e1 in
      match v1 with
      | Err => Err
      | Val g1 => 
        let v2 := f_eval env e2 in
        match v2 with
        | Err => Err
        | Val g2 => Val (g1 - g2)
        end
       end
  | Mult e1 e2 =>
    let v1 := f_eval env e1 in
      match v1 with
      | Err => Err
      | Val g1 => 
        let v2 := f_eval env e2 in
        match v2 with
        | Err => Err
        | Val g2 => Val (g1 * g2)
        end
      end
  | Div e1 e2 =>
    let v1 := f_eval env e1 in
      match v1 with
      | Err => Err
      | Val g1 => 
        let v2 := f_eval env e2 in
        match v2 with
        | Err => Err
        | Val g2 => Val (g1 / g2)
        end
      end
    end.

Lemma eval0_3 : f_eval env0 (Mult (Plus (Cte 4) (Var 0)) (Moins (Cte 9) (Var 0))) = Val 42.
  auto.
Qed.

Lemma eval1_3 : f_eval env0 (Mult (Plus (Cte 3) (Var 1)) (Moins (Cte 9) (Var 0))) = Err.
  auto.
Qed.

Functional Scheme f_eval_ind := Induction for f_eval Sort Prop.

Theorem f_eval_sound : forall (env : context) (e : expr) (v : value), 
    (f_eval env e) = v -> eval env e v.
intro.
intro.
functional induction (f_eval env e) using f_eval_ind; intros.
rewrite  <- H.
apply_eval_val.
rewrite <- H.
apply_eval_val.
rewrite <- H.
apply_eval_err.
rewrite <- H.
apply EPlus with (v1 := g1) (v2 := g2).
apply_eval_val.
apply_eval_val.
auto.
rewrite <- H.
apply EPlus_ErrR with (v := g1).
apply_eval_val.
apply (IHv0 Err).
auto.
rewrite <- H.
apply EPlus_ErrL.
auto.
rewrite <- H.
apply EMoins with (v1 := g1) (v2 := g2).
apply_eval_val.
apply_eval_val.
auto.
rewrite <- H.
apply EMoins_ErrR with (v := g1).
apply_eval_val.
auto.
rewrite <- H.
apply EMoins_ErrL.
auto.
rewrite <- H.
apply EMult with (v1 := g1) (v2 := g2).
apply_eval_val.
apply_eval_val.
auto.
rewrite <- H.
apply EMult_ErrR with (v := g1).
apply_eval_val.
auto.
rewrite <- H.
apply EMult_ErrL.
auto.
rewrite <- H.
apply EDiv with (v1 := g1) (v2 := g2).
apply_eval_val.
apply_eval_val.
auto.
rewrite <- H.
apply EDiv_ErrR with (v := g1).
apply_eval_val.
auto.
rewrite <- H.
apply EDiv_ErrL.
auto.
Qed.













