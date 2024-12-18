Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_benbta_yes_tauto: A -> A.
Proof.
(*! benbta_proof *)
tauto.
Qed.