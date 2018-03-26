Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.

Lemma isos_ex1 : forall A B : Set,
 A * unit * B = B * (unit * A).
intros.
rewrite Com.
rewrite P_unit.
rewrite Ass.
rewrite P_unit.
reflexivity.
Qed.

Lemma isos_ex2 : forall A B C : Set,
  (A * unit -> B * (C * unit)) =
  (A * unit -> (C -> unit) * C) * (unit -> A -> B).
intros.
rewrite P_unit.
rewrite Dis.
rewrite AL_unit.
rewrite AR_unit.
rewrite Dis.
rewrite AR_unit.
rewrite P_unit.
rewrite Dis.
rewrite AR_unit.
rewrite (Com unit (A -> C)).
rewrite P_unit.
rewrite Com.
reflexivity.
Qed.

Ltac normalize :=
  repeat
    match goal with
    | |- context[?A * unit] => rewrite P_unit
    | |- context[?A -> unit] => rewrite AR_unit
    | |- context[unit -> ?A] => rewrite AL_unit
    | |- context[?A -> ?B * ?C] => rewrite Dis
    | |- context[?A * ?B -> ?C] => rewrite Cur
    | |- context[?A * (?B * ?C)] => rewrite Ass
    end.

Lemma isos_ex1_auto : forall A B : Set,
 A * unit * B = B * (unit * A).
intros.
normalize.
rewrite Com.
reflexivity.
Qed.


Lemma isos_ex2_auto : forall A B C : Set,
  (A * unit -> B * (C * unit)) =
  (A * unit -> (C -> unit) * C) * (unit -> A -> B).
intros.
normalize.
rewrite (Com unit (A -> C)).
normalize.
rewrite Com.
reflexivity.
Qed.

Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.

Lemma Peano_ex1 : 
    (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.

Lemma Peano_ex2 :
    (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
rewrite ax7.
rewrite ax7.
rewrite ax6.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.

Ltac calc :=
  repeat
    match goal with
    | |- context[(plus ?x o)] => rewrite ax4
    | |- context[(plus ?x (s ?y))] => rewrite ax5
    | |- context[(mult ?x o)] => rewrite ax6
    | |- context[(mult ?x (s ?y))] => rewrite ax7
    end.

Lemma Peano_ex1_auto : 
    (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
calc.
reflexivity.
Qed.

Lemma Peano_ex2_auto :
    (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
calc.
reflexivity.
Qed.


Hint Rewrite ax4 ax5 ax6 ax7 : peano.

Lemma Peano_ex1_autorewrite : 
    (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
autorewrite with peano using try reflexivity.
Qed.


Lemma Peano_ex2_autorewrite :
    (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
autorewrite with peano using try reflexivity.
Qed.













