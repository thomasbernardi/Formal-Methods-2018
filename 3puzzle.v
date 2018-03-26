Section Puzzle.

Parameters Scottish RedSocks WearKilt Married GoOutSunday : Prop.

Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt \/ ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish /\ Married.
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : False.
elim (rule2).
intro.
apply (rule3).
apply (rule5 H).
elim (rule4).
intros.
apply (H1).
apply (rule5 H).
intros.
apply (H).
apply (rule1).
intro.
apply (rule3).
apply (rule5).
apply (rule6 H0).
elim (rule4).
intros.
apply (H2 H0).


