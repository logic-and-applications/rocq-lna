Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_lna_yes_before_pragma: A -> A.
Proof.
intros.
(*! lna_proof *)
hyp H.
Qed.