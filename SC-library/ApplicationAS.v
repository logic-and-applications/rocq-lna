Require Import SCcoq.AS.

(*-------------------------------Hoare_Logic---------------------------------*)
(* Example from the book *)
Example Example6_8a :
  |= {{ B[[BTrue]] }} WHILE BTrue DO SKIP {{ B[[BTrue]] }}.
Proof.
  intros P Q.
  apply consp with 
    (P':= B[[BTrue]]) (Q' := ~B[[BTrue]] /\p B[[BTrue]]).
  - apply whilep.
    apply hoare_post_true.
    intros st.
    unfold bassn.
    simpl.
    reflexivity.
  - (* Precondition implies invariant *)
    intros st H.
    reflexivity.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl.
    unfold assert_implies.
    unfold and_sub.
    intros st [H0 H1].
    reflexivity.
Qed.

Import Annotated.
Example annotatedprogram : Annotated :=
  {{ B[[BTrue]] }}
  WHILE BTrue
  DO  
    {{B[[BTrue]] /\p B[[BTrue]]}} =>>
    {{B[[BTrue]]}}
    SKIP
    {{ B[[BTrue]] }}
  {{ ~B[[BTrue]] /\p B[[BTrue]]}} =>>
  {{ B[[BFalse]] }}.

Example annotatedprogram_correct :
  ann_correct annotatedprogram.
Proof.

  verify.
  destruct H.
  destruct H.
  exact H0.
Qed.

Example annotatedprogram' : Annotated :=
  {{ B[[BTrue]] }}
  WHILE BTrue
  DO  
    {{B[[BTrue]]}}
    SKIP
    {{ B[[BTrue]] }}
  {{ B[[BTrue]] }}.

Example annotatedprogram_correct' :
  ann_correct annotatedprogram'.
Proof.
  verify.
Qed.

Fixpoint real_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Example my_fact (m:nat) : Annotated := (
    {{ fun st => st x = m }} =>>
    {{ fun st => st x > 0 -> real_fact (st x) =
        real_fact m /\ m >= st x }}
  y ::= ANum 1
    {{ fun st => st x > 0 -> st y * real_fact (st x) =
        real_fact m /\ m >= st x }};
  WHILE BNot (BEq (AId x) (ANum 1))
  DO   {{ fun st => st x - 1 > 0 ->
        st y * st x * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1) }}
     y ::= AMult (AId y) (AId x)
       {{ fun st => st x - 1 > 0 ->
        st y * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1) }};
     x ::= AMinus (AId x) (ANum 1)
       {{ fun st => st x > 0 -> st y * real_fact (st x)
        = real_fact m /\ m >= st x }}
    {{ fun st => st y = real_fact m /\ m > 0}}
).

Theorem my_factcorrect : forall m,
  ann_correct (my_fact m).
Proof.
  intros.
  verify. 
  - rewrite <- plus_n_O.
    assert ((y !-> 1, st) x > 0 ->
        real_fact (st x) = real_fact m /\ m >= st x).
    { apply H. }
    apply H1 in H0.
    apply H0.
  - assert (forall n, n <> 0 -> n * real_fact (n - 1) 
        = real_fact n).
    + intros. 
      destruct n.
      * contradiction.
      * cbn.
        rewrite Nat.sub_0_r.
        reflexivity.
    + assert (st x > 0) as X.
      {
        lia.
      }
      specialize (H1 X).
      destruct H1.
      rewrite <- H1.
      assert (exists (k : nat), st x = S k).
      {
        induction (st x).
        - inversion X.
        - eexists.
          reflexivity.
      }
      destruct H4 as [k p].
      rewrite p.
      cbn.
      (*rewrite <- mult_assoc.*)
      rewrite Nat.sub_0_r.
      lia.
      (*
      replace (real_fact k + k * real_fact k) with ((k+1)* real_fact k).
      lia.
      reflexivity.
      cbn.
      reflexivity. *)
  - assert (st x = 1).
    (* Search (_ =? _ = true). *)
    { 
      apply Nat.eqb_eq.
      exact H.
    }
    rewrite H1 in H0.
    simpl in H0.
    lia.
  - assert (st x = 1).
    {
      apply Nat.eqb_eq.
      exact H.
    }
    lia.
  - cbn in *.
    apply H.
    exact H0.
  - cbn in *.
    apply H.
    exact H0.
Qed.

(*
Example Example6_8b :
  {{ B[[BTrue]] }} WHILE BTrue DO SKIP {{ ~B[[BTrue]] }}.
Proof.
  intros P Q.
  apply consp with 
    (P':= B[[BTrue]]) (Q' := ~B[[BTrue]] /\p B[[BTrue]]).
  apply whilep.
  - apply hoare_post_true.
    intros st.
    unfold bassn.
    simpl.
    reflexivity.
  - (* Precondition implies invariant *)
    intros st H.
    constructor.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl.
    unfold assert_implies.
    unfold and_sub.
    intros st [H0 H1].
    apply H0.
Qed.

(* Definition of factorial *)
Fixpoint real_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(* Proof of the factorial program *)
Example Example6_9:
  forall (m:nat),
  {{ fun st => st x = m }}
  y ::= 1; WHILE ~(x = 1)
  DO (y ::= y * x; x ::= x - 1)
  {{ fun st => st y = (real_fact m) /\ m > 0}}.
Proof.
  intros m.
  apply consp_pre with (fun (st : State) => (st x > 0 ->
        real_fact (st x) = real_fact m /\ m >= st x)).
  apply compp with (fun (st : State) => (st x > 0 ->
        st y * real_fact (st x) = real_fact m /\ m >= st x)).
  eapply consp_post.
  apply whilep.
  apply consp_pre with (fun (st : State) => st x - 1 > 0 ->
        st y * st x * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1)).
  apply compp with (fun (st : State) => st x - 1 > 0 ->
        st y * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1)).
  eapply consp_pre.
  apply assp.
  - intros st P Q.
    unfold bassn, assn_sub, assert_implies, t_update. simpl.
    unfold bassn, assn_sub, assert_implies, t_update in Q.
    simpl in Q.
    apply P in Q.
    apply Q.
  - eapply consp_pre.
    apply assp.
    intros st P Q.
    unfold bassn, assn_sub, assert_implies, t_update. simpl.
    unfold bassn, assn_sub, assert_implies, t_update in Q.
    simpl in Q.
    apply P in Q.
    apply Q.
  - unfold and_sub.
    intros st P Q.
    destruct P.
    unfold bassn in H.
    simpl in H.
    apply negb_true_iff in H.
    apply beq_nat_false in H.
    assert (forall n, n <> 0 -> n * real_fact (n - 1) =
        real_fact n).
    + intros. destruct n.
      * destruct H1. reflexivity.
      * simpl. rewrite <- minus_n_O. reflexivity.
    + rewrite <- mult_assoc. rewrite H1.
      * lia.
      * lia.
  - unfold and_sub.
    intros st P. destruct P.
    unfold bassn2 in H.
    apply not_true_iff_false in H.
    simpl in H.
    apply negb_false_iff in H.
    apply beq_nat_true in H.
    assert (st x > 0).
    { lia. }
    apply H0 in H1.
    assert (real_fact (st x) = 1).
    { rewrite H. reflexivity. }
    rewrite H2 in H1.
    lia.
  - eapply consp_pre.
    apply assp.
    intros st P Q.
    unfold bassn, assn_sub, assert_implies, t_update. simpl.
    unfold bassn, assn_sub, assert_implies, t_update in Q.
    simpl in Q.
    apply P in Q.
    rewrite <- plus_n_O.
    apply Q.
  - intros st P H.
    rewrite P.
    lia.
Qed.

(*----------------------------Annotated_Programs-----------------------------*)
(* We can also prove the examples above in their annotated program form *)
Import Annotated.
Example annotatedprogram : Annotated := (
  {{ B[[BTrue]] }}
  WHILE BTrue
  DO  
    {{B[[BTrue]] /\p B[[BTrue]]}} =>>
    {{B[[BTrue]]}}
    SKIP
    {{ B[[BTrue]] }}
  {{ ~B[[BTrue]] /\p B[[BTrue]]}} =>>
  {{ B[[BFalse]] }}
)
.

Example annotatedprogram_correct :
  ann_correct (annotatedprogram).
Proof.
  verify.
  unfold and_sub in H.
  destruct H.
  unfold not in H.
  destruct H.
  reflexivity.
Qed.

Example my_fact (m:nat) : Annotated := (
    {{ fun st => st x = m }} =>>
    {{ fun st => st x > 0 -> real_fact (st x) =
        real_fact m /\ m >= st x }}
  y ::= ANum 1
    {{ fun st => st x > 0 -> st y * real_fact (st x) =
        real_fact m /\ m >= st x }};
  WHILE BNot (BEq (AId x) (ANum 1))
  DO   {{ fun st => (st x > 0 -> 
        st y * real_fact (st x) = real_fact m /\ m >= st x)
        /\ st x <> 1 }} =>>
       {{ fun st => st x - 1 > 0 ->
        st y * st x * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1) }}
     y ::= AMult (AId y) (AId x)
       {{ fun st => st x - 1 > 0 ->
        st y * real_fact (st x - 1) =
        real_fact m /\ m >= (st x - 1) }};
     x ::= AMinus (AId x) (ANum 1)
       {{ fun st => st x > 0 -> st y * real_fact (st x)
        = real_fact m /\ m >= st x }}
    {{ fun st => (st x > 0 -> st y * real_fact (st x) =
        real_fact m /\ m >= st x) /\ st x = 1 }} =>>
    {{ fun st => st y = real_fact m /\ m > 0}}
).

Theorem my_factcorrect : forall m,
  ann_correct (my_fact m).
Proof.
  intros.
  verify. 
  - rewrite <- plus_n_O.
    assert ((y !-> 1, st) x > 0 ->
        real_fact (st x) = real_fact m /\ m >= st x).
    { apply H. }
    apply H1 in H0.
    apply H0.
  - assert (forall n, n <> 0 -> n * real_fact (n - 1) 
        = real_fact n).
    + intros. 
      destruct n.
      * destruct H1.
        reflexivity.
      * simpl.
        rewrite <- minus_n_O.
        reflexivity.
    + unfold not.
      intros.
      rewrite H2 in H.
      discriminate H.
  - apply beq_nat_true in H.
    apply H.
  - assert (forall n, n <> 0 -> n * real_fact (n - 1) =
        real_fact n).
    + intros.
      destruct n.
      * destruct H2.
        reflexivity.
      * simpl.
        rewrite <- minus_n_O.
        reflexivity.
    + rewrite <- mult_assoc.
      rewrite H2.
      * lia.
      * lia.
  - assert ((y !-> st y * st x, st) x - 1 > 0 ->
        st y * st x * real_fact (st x - 1)
        = real_fact m /\ m >= st x - 1).
    { apply H. }
    apply H1 in H0.
    apply H0.
  - assert ((x !-> st x - 1, st) x > 0 ->
        st y * real_fact (st x - 1)
        = real_fact m /\ m >= st x - 1).
    { apply H. }
    apply H1 in H0.
    apply H0.
  - assert (1 > 0).
    { lia. }
    apply H in H0.
    assert (real_fact 1 = 1).
    { reflexivity. }
    rewrite H1 in H0.
    assert (st y * 1 = st y).
    { lia. }
    rewrite H2 in H0.
    apply H0.
Qed.
*)
