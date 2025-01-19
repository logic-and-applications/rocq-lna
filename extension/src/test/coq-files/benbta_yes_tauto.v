Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_lnata_yes_tauto: A -> A.
Proof.
(*! lnata_proof *)
intros.
tauto.
Qed.