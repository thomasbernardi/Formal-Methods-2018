Require Export ZArith.
Require Export FunInd.
Require Export Omega.
Open Scope Z_scope.

Inductive AB : Set :=
  | Node : Z -> AB -> AB -> AB
  | Leaf : Z -> AB
  | Empty : AB.

Definition node_value (a : AB) : option Z :=
  match a with
  | (Node v _ _) => Some v
  | (Leaf v) => Some v
  | Empty => None 
end.

Inductive is_ABR : AB -> Prop :=
  | Is_Empty : is_ABR Empty
  | Is_Leaf : forall v : Z, is_ABR (Leaf v)
  | Node_Both : forall (v vl vr : Z) (al ar : AB), is_ABR al -> is_ABR ar ->
    Some vl = (node_value al) -> Some vr = (node_value ar) -> vl <= v -> v <= vr ->
    is_ABR (Node v al ar)
  | Node_Left : forall (v vl : Z) (al : AB), is_ABR al -> Some vl = (node_value al) ->
    vl <= v -> is_ABR (Node v al Empty)
  | Node_Right : forall (v vr : Z) (ar : AB), is_ABR ar -> Some vr = (node_value ar) ->
    v <= vr -> is_ABR (Node v Empty ar).

Definition benchmark_01 := (Node 3 (Node 1 (Leaf 0) (Leaf 3)) (Leaf 5)).
Definition benchmark_02 := (Node 5 (Node 3 (Leaf 2) (Leaf 3)) (Node 7 (Leaf 7) (Leaf 8))).
Definition benchmark_03 := (Node 15 (Node 12 (Node 11 (Leaf 5) Empty) (Node 14 (Node 12 Empty (Leaf 13)) (Leaf 15))) (Node 18 (Leaf 17) (Node 19 Empty (Leaf 20)))).

Lemma p1 : is_ABR benchmark_01.
apply (Node_Both _ 1 5).
apply (Node_Both _ 0 3).
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

Lemma p2 : is_ABR benchmark_02.
apply (Node_Both _ 3 7).
apply (Node_Both _ 2 3).
apply Is_Leaf.
apply Is_Leaf.
auto.
auto.
omega.
omega.
apply (Node_Both _ 7 8).
apply Is_Leaf.
apply Is_Leaf.
auto.
auto.
omega.
omega.
auto.
auto.
omega.
omega.
Qed.

Lemma
