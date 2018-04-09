Require Export ZArith.
Require Export FunInd.
Open Scope Z_scope.
Open Scope list.

Inductive expr : Set :=
  | Cte : Z -> expr
  | Var : nat -> expr
  | Plus : expr -> expr -> expr
  | Moins : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Div : expr -> expr -> expr
  | True : expr
  | False : expr
  | Non : expr -> expr
  | And : expr -> expr -> expr
  | Or : expr -> expr -> expr
  | Eq : expr -> expr -> expr
  | Neq : expr -> expr -> expr
  | Lt : expr -> expr -> expr
  | Leq : expr -> expr -> expr
  | Gt : expr -> expr -> expr
  | Geq : expr -> expr -> expr.


Inductive value : Set :=
  | ValZ : Z -> value
  | ValB : bool -> value
  | Err : value.

Inductive env_value : Set :=
  | EValZ : Z -> env_value
  | EValB : bool -> env_value.

Definition context := list (nat * env_value).

Fixpoint get_val (n : nat) (env : context) : option env_value :=
  match env with
  | nil => None
  | (index, val)::t =>
    match eq_nat_dec n index with
    | left _ => Some val
    | _ => get_val n t
  end
end.

Inductive eval (env : context) : expr -> value -> Prop :=
  | ECte : forall c : Z, eval env (Cte c) (ValZ c)
  | EVarZ : forall (n : nat) (v : Z), (get_val n env) = Some (EValZ v) -> eval env (Var n) (ValZ v)
  | EVarB : forall (n : nat) (v : bool), (get_val n env) = Some (EValB v) -> eval env (Var n) (ValB v)
  | EVar_Err : forall (n : nat), (get_val n env) = None -> eval env (Var n) Err
  | EPlus : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (ValZ v1) -> eval env e2 (ValZ v2)
    -> v = v1 + v2 -> eval env (Plus e1 e2) (ValZ v)
  | EPlus_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Plus e1 e2) Err
  | EPlus_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env e2 Err
    -> eval env (Plus e1 e2) Err
  | EPlus_ErrBL : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env (Plus e1 e2) Err
  | EPlus_ErrBR : forall (e1 e2 : expr) (v : Z) (b : bool),
    eval env e1 (ValZ v) -> eval env e2 (ValB b) -> eval env (Plus e1 e2) Err
  | EMoins : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (ValZ v1) -> eval env e2 (ValZ v2)
    -> v = v1 - v2 -> eval env (Moins e1 e2) (ValZ v)
  | EMoins_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Moins e1 e2) Err
  | EMoins_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env e2 Err
    -> eval env (Moins e1 e2) Err
  | EMoins_ErrBL : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env (Moins e1 e2) Err
  | EMoins_ErrBR : forall (e1 e2 : expr) (v : Z) (b : bool),
    eval env e1 (ValZ v) -> eval env e2 (ValB b) -> eval env (Moins e1 e2) Err
  | EMult : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (ValZ v1) -> eval env e2 (ValZ v2)
    -> v = v1 * v2 -> eval env (Mult e1 e2) (ValZ v)
  | EMult_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Mult e1 e2) Err
  | EMult_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env e2 Err
    -> eval env (Mult e1 e2) Err
  | EMult_ErrBL : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env (Mult e1 e2) Err
  | EMult_ErrBR : forall (e1 e2 : expr) (v : Z) (b : bool),
    eval env e1 (ValZ v) -> eval env e2 (ValB b) -> eval env (Mult e1 e2) Err
  | EDiv : forall (e1 e2 : expr) (v1 v2 v : Z),
    eval env e1 (ValZ v1) -> eval env e2 (ValZ v2)
    -> v = v1 / v2 -> eval env (Div e1 e2) (ValZ v)
  | EDiv_ErrL : forall (e1 e2 : expr),
    eval env e1 Err -> eval env (Div e1 e2) Err
  | EDiv_ErrR : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env e2 Err
    -> eval env (Div e1 e2) Err
  | EDiv_ErrBL : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env (Div e1 e2) Err
  | EDiv_ErrBR : forall (e1 e2 : expr) (v : Z) (b : bool),
    eval env e1 (ValZ v) -> eval env e2 (ValB b) -> eval env (Div e1 e2) Err
  | ETrue : eval env True (ValB true)
  | EFalse : eval env False (ValB false)
  | ENon : forall (e : expr) (b nb : bool), eval env e (ValB b) -> 
    nb = negb b -> eval env (Non e) (ValB nb)
  | ENon_ErrDne : forall e : expr, eval env e Err -> eval env (Non e) Err
  | ENon_ErrZ : forall (e : expr) (v : Z), eval env e (ValZ v) -> eval env (Non e) Err
  | EAnd : forall (e1 e2 : expr) (b1 b2 b: bool), eval env e1 (ValB b1) ->
    eval env e2 (ValB b2) -> b = (andb b1 b2) -> eval env (And e1 e2) (ValB b)
  | EAnd_ErrL : forall (e1 e2 : expr), eval env e1 Err -> eval env (And e1 e2) Err
  | EAnd_ErrR : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env e2 Err -> eval env (And e1 e2) Err
  | EAnd_ErrZL : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env (And e1 e2) Err
  | EAnd_ErrZR : forall (e1 e2 : expr) (b : bool) (v : Z),
    eval env e1 (ValB b) -> eval env e2 (ValZ v) -> eval env (And e1 e2) Err
  | EOr : forall (e1 e2 : expr) (b1 b2 b : bool), eval env e1 (ValB b1) -> 
    eval env e2 (ValB b2) -> b = (orb b1 b2) -> eval env (Or e1 e2) (ValB b)
  | EOr_ErrL : forall (e1 e2 : expr), eval env e1 Err -> eval env (Or e1 e2) Err
  | EOr_ErrR : forall (e1 e2 : expr) (b : bool),
    eval env e1 (ValB b) -> eval env e2 Err -> eval env (Or e1 e2) Err
  | EOr_ErrZL : forall (e1 e2 : expr) (v : Z),
    eval env e1 (ValZ v) -> eval env (Or e1 e2) Err
  | EOr_ErrZR : forall (e1 e2 : expr) (b : bool) (v : Z),
    eval env e1 (ValB b) -> eval env e2 (ValZ v) -> eval env (Or e1 e2) Err.

Open Scope nat_scope.

Lemma eval1 : eval ((1, (EValZ 1))::(2, (EValZ 3))::(3, (EValB true))::nil) 
    (Plus (Cte 5) (Cte 2)) (ValZ 7).
eapply EPlus.
apply ECte.
apply ECte.
auto.
Qed.
apply EOr.
apply EAnd.
apply EOrL.
apply ETrue.
apply ETrue.
Qed.















