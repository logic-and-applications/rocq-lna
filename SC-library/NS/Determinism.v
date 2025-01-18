Require Import SCcoq.Framework_common.
Require Import SCcoq.NS.FrameworkNS.

Local Open Scope Z_scope.
Open Scope while_scope.

(*--------------------------------Determinism--------------------------------*)
(* Natural Semantics is deterministic *)
Theorem Seval_deterministic
        (S : Stm)
        (s s' s'' : State)
  : << S, s >> --> s'  ->
    << S, s >> --> s'' ->
    s' = s''.
Proof.
  intros H1.
  revert s''.
  induction H1 ; intros s'' H2 ; inversion H2 ; subst.
  - (* ass *)
    reflexivity.
  - (* skip *)
    reflexivity.
  - (* comp *)
    assert (st' = st'0) as H3.
    { apply IHSeval1; assumption. }
    subst st'0.
    apply IHSeval2. assumption.
  - (* if tt, b1 evaluates to true *)
    apply IHSeval. assumption.
  - (* if tt,  b1 evaluates to false (contradiction) *)
    rewrite H in H7. discriminate H7.
  - (* if ff, b1 evaluates to true (contradiction) *)
    rewrite H in H7. discriminate H7.
  - (* if ff, b1 evaluates to false *)
    apply IHSeval. assumption.
  - (* while tt, b1 evaluates to true *)
    assert (st' = st'0) as H3.
    { apply IHSeval1; assumption. }
    subst st'0.
    apply IHSeval2. assumption.
  - (* while tt, b1 evaluates to false (contradiction) *)
    rewrite H in H5.
    discriminate H5.
  - (* while ff, b1 evaluates to true (contradiction) *)
    rewrite H in H4.
    discriminate H4.
  - (* while ff, b1 evaluates to false *)
    reflexivity.
Qed.
