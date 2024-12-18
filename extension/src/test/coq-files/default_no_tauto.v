Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_default_no_intros: A -> A.
Proof.
tauto.
Qed.