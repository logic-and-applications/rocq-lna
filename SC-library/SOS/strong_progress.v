Require Import SCcoq.Framework_common.
Require Import SCcoq.SOS.Framework_SOS.

Definition is_final (conf:Config) := (exists s, conf = Final s)%type.

Theorem strong_progress:
forall conf:Config,
 is_final conf
 \/
 (exists conf', conf ==> conf').
Proof.
  intro.
  induction conf.
  - right. induction S.
    + eexists. apply ass_sos. reflexivity.
    + eexists. apply skip_sos. 
    + inversion IHS1. induction x.
      * exists <<S; S2,s0>>. apply comp_I_sos. assumption.                           
      * exists <<S2, s0>>. apply comp_II_sos. assumption.
    + assert (Beval s b = true \/ Beval s b = false).
      { induction (B[[b]]s). 
        - left. reflexivity.
        - right. reflexivity.
      }
      destruct H.
      * exists <<S1,s>>. apply if_tt_sos. assumption.
      * exists <<S2,s>>. apply if_ff_sos. assumption.
    + exists <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP,s>>. apply while_sos. 
  - left. unfold is_final. exists s. reflexivity.
Qed.
