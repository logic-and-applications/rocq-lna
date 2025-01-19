Require Import LnA.LnA.

Parameter A: Prop.

Lemma combined_tactics1: A -> A -> A.
Proof.
intros H1; imp_i H2; hyp H1.
Qed.

Lemma combined_tactics2: A -> A -> A.
Proof.
imp_i H1; intros H2; hyp H2.
Qed.

Lemma combined_tactics3: A -> A -> A.
Proof.
imp_i H1; imp_i H2; tauto.
Qed.

Lemma combined_tactics4: A -> A -> A.
Proof.
intros; pose proof H;   tauto.
Qed.

Lemma combined_tactics_with_newlines_in_between: A -> A -> A.
Proof.
  intros; 
  
    pose proof H; 

  tauto.  
Qed.