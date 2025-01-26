Require Import LnA.LnA.

Parameter A: Prop.

Lemma test_unfinished1: A -> A.
Proof.
intros.
hyp H.

Lemma test_unfinished2: A -> A.
Proof.
intros.

Lemma test_unfinished3: A -> A.
Proof.
imp_i H.

Lemma test_unfinished4: A -> A.
Proof.
(*! lnata_proof*)
intros.
tauto.