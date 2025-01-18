Require Import SCcoq.Framework_common.
Require Import SCcoq.SOS.Framework_SOS.
Require Import ZArith_base.
Require Import Lia.
Require Import Strings.String.

Inductive multi_k {X : Type} (R : relation X) : nat -> relation X :=
| multikrefl : forall (x : X), multi_k R 0 x x
| multikstep : forall (x y z : X) (k:nat),
                    R x y->
                    multi_k R k y z ->
                    multi_k R (S k) x z.
Notation " t ==>[ k ]  t' " := (multi_k sstep k t t' ) (at level 50).

Definition single_multi_k
           {X : Type}
           (R : relation X)
           {x y : X}
  : R x y -> multi_k R 1 x y.
Proof.
  intros r.
  eapply multikstep.
  - exact r.
  - apply multikrefl.
Qed.

Local Open Scope Z_scope.

Example e : <<SKIP, (x !-> 2)>> ==>[1] <<x!->2>>.
Proof.
  eapply multikstep.
  apply skip_sos.
  eapply multikrefl.
Qed.

Local Close Scope Z_scope.
Close Scope while_scope.

Definition isStuck (conf: Config) :=
  ~ (exists (conf' : Config), conf ==> conf').

Lemma final_is_stuck: forall s, isStuck <<s>> .
Proof.
  intros.
  unfold isStuck.
  intros.
  intro.
  destruct H.
  inversion H.
Qed.

Lemma identity_zero:
forall c,
 c ==>[0] c.
Proof.
  apply multikrefl.
Qed.
 

Lemma stuck_stops:
forall c c' k,
  isStuck c ->
  c ==>[ k ] c' ->
  k = 0 /\ c' = c.
Proof.
  intros.
  unfold isStuck in H.
  induction k.
  - inversion H0; subst.
    split. reflexivity. reflexivity.
  - destruct H0. split. reflexivity. reflexivity.
    destruct H.
    exists y. assumption.
Qed.

Lemma state_k_zero:
  forall k s conf,
    <<s>> ==>[k] conf
    ->
    k = 0 /\ conf = <<s>>.
Proof.
  intros.
  apply stuck_stops.
  apply final_is_stuck.
  assumption.
Qed.

Lemma zero_steps:
  forall c c',
    c ==>[0] c' -> c = c'.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma zero_steps_rev:
  forall c c',
    c = c' ->
    c ==>[0] c'.
Proof.
  intros.
  subst.
  apply identity_zero.
Qed.

Lemma one_step:
  forall c c',
    c ==> c' ->
    c ==>[1] c'.
Proof.
  intros.
  apply (multikstep sstep c c').
  - assumption.
  - apply zero_steps_rev.
    reflexivity.
Qed.

Lemma one_step_rev:
  forall c c',
    c ==>[1] c' ->
    c ==> c'.
Proof.
  intros.
  inversion H ; subst.
  apply zero_steps in H2.
  subst.
  assumption. 
Qed.

Theorem strong_induction_help:
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, (forall k : nat, ((k <= n)%nat -> P k)) -> P (S n))
    ->
    forall (n : nat) (m : nat), m <= n -> P m.
Proof.
  intros P HZ HS n.
  induction n as [ | n IHn ] ; intros m Hmn.
  - assert (m = 0).
    { lia. }
    subst.
    exact HZ.
  - assert (m = S n \/ m <= n) as Hm.
    {
      lia.
    }
    induction Hm as [p | p].
    + subst.
      apply HS.
      apply IHn.
    + apply IHn.
      exact p.
Defined.

Theorem strong_induction:
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, (forall k : nat, ((k <= n)%nat -> P k)) -> P (S n))
    ->
    forall n : nat, P n.
Proof.
  intros P H0 HS n.
  apply (strong_induction_help P H0 HS n n).
  lia.
Qed.

Lemma comp_complete: 
  forall k Ss1 Ss2 s s'',
    <<Ss1; Ss2, s>> ==>[k] <<s''>>
    ->
    exists s' k1 k2,
      <<Ss1,s>>==>[k1] <<s'>> /\ <<Ss2,s'>> ==>[k2] <<s''>> /\ k = (k1 + k2).
Proof.
  (*induction on the length of the derivation seqence*)
  induction k using strong_induction.
  - (*0*)
    intros.
    inversion H.
  - (*IS*)
    rename k into k0.
    intros.
    inversion H0. subst. 
    inversion H2; subst.
    +(*compI*)      
      assert (exists (s' : State) (k1 k2 : nat),
                 << S1', st' >> ==>[ k1] << s' >> /\
                         << Ss2, s' >> ==>[ k2] << s'' >> /\ k0 = k1 + k2).      
      {
        apply H.
        * reflexivity. 
        * assumption.
      }
      destruct H1. rename x into s0. destruct H1. rename x into k1.
      destruct H1. rename x into k2. destruct H1. destruct H4.
      exists s0.
      exists (S k1).
      exists k2.
      split.
      -- apply (multikstep sstep<< Ss1, s >> << S1', st' >> ).
         --- assumption.
         --- assumption.
      -- split.
         --- assumption.
         --- lia.
    +(*compII*)
      exists st'.
      exists 1.
      exists k0.
      split.
      * apply one_step. assumption.
      * split.
        ** assumption.
        ** reflexivity.
Qed.

Theorem half_comp:
  forall k S1 s s',
    <<S1,s>> ==>[k] <<s'>>
    ->
    forall S2,
      <<S1; S2, s>> ==>[k] <<S2, s'>>.
Proof.
  induction k using strong_induction.
  - intros.
    inversion H.
  - intros S1 s s' c.
    inversion c ; subst.
    induction y. (* if it is commi or compii - if S1 is executed in many or 1 steps *)
    + rename s0 into s''.
      rename S into S1'.
      intro S2.
      apply (multikstep sstep<< S1; S2, s >> << S1';S2, s'' >>).
      * apply comp_I_sos.
        assumption.
      * apply H.
        ** reflexivity.
        ** assumption.
    + intro S2.
      rename s0 into s''.
      apply (multikstep sstep<< S1; S2, s >> <<S2, s'' >>).
      * apply comp_II_sos.
        assumption.
      * assert (k = 0 /\ <<s'>> = <<s''>>) as X.
        {
          apply stuck_stops.
          apply final_is_stuck.
          assumption.
        }
        destruct X as [p q].
        inversion q.
        subst.
        apply zero_steps_rev.
        reflexivity.
Qed.

Lemma exec_comp :
  forall k1 k2 S1 s S2 s' s'',
    <<S1, s>> ==>[k1] << s'>>
    ->
    << S2, s'>> ==>[k2] <<s''>>
    ->
    exists k,
      <<S1; S2, s>> ==>[k] <<s''>> /\ k = k1+k2.
Proof.
  induction k1 using  strong_induction ; intros k2 S1 s S2 s' s''.
  - exists k2.
    split.
    + assert (<< S1, s >> = << s' >>).
      {
        apply zero_steps.
        assumption.
      }
      inversion H1.
    + lia.
  - remember (k1 + k2) as k0.
    exists (S k0).
    split.
    + inversion H0.
      induction y.
      * subst.
        rename S into S1'.    
        apply (multikstep sstep<< S1; S2, s >> << S1';S2, s0 >>).
        -- apply comp_I_sos. assumption.
        -- assert (exists k0 : nat,
                      << S1'; S2, s0 >> ==>[ k0] << s'' >> /\ k0 = k1+k2 ).
           {
             apply H with s'.
             - reflexivity.
             - assumption.
           - assumption.
           }
           destruct H2.
           destruct H2.
           subst.
           assumption.
      * subst.
        apply (multikstep sstep<< S1; S2, s >> <<S2, s0 >>).
        -- apply comp_II_sos.
           assumption.
        -- assert (k1 = 0 /\ <<s'>> = <<s0>>).
           {
             apply state_k_zero.
             assumption.
           }
           destruct H2.
           inversion H5.
           subst.
           assumption.
    + lia.
Qed.
