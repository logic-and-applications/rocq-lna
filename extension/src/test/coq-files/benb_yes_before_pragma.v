Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_benb_yes_before_pragma: A -> A.
Proof.
intros.
(*! benb_proof *)
hyp H.
Qed.