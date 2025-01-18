Require Import SCcoq.Framework_common.

(* Open Z scope and while_scope *)
Local Open Scope Z_scope.
Open Scope while_scope.

(*----------------------------Natural_Semantics------------------------------*)
(* Semantics Stm and notation for transitions *)
Reserved Notation "conf '-->' st'"
                  (at level 40).

Inductive Seval : Config -> State -> Prop :=
  | ass_ns  : forall st a1 n x,
      Aeval st a1 = n ->
      << x ::= a1 , st>> --> (x !-> n, st)
  | skip_ns : forall st,
     << SKIP , st >> --> st
  | comp_ns : forall s1 s2 st st' st'',
      << s1 , st >> --> st' ->
      << s2 , st' >> --> st'' ->
      <<( s1 ; s2 ), st >> --> st''
  | if_tt_ns : forall st st' b s1 s2,
      Beval st b = true ->
      << s1 , st >> --> st' ->
      << IF_ b THEN s1 ELSE s2 , st >> --> st'
  | if_ff_ns : forall st st' b s1 s2,
      Beval st b = false ->
      << s2 , st >> --> st' ->
      << IF_ b THEN s1 ELSE s2 , st>> --> st'
  | while_tt_ns : forall st st' st'' b s,
      Beval st b = true ->
      << s, st >> --> st' ->
      << WHILE b DO s , st' >> --> st'' ->
      << WHILE b DO s , st >> --> st''
  | while_ff_ns : forall b st s,
      Beval st b = false ->
      << WHILE b DO s , st >>  --> st 
where "conf '-->' st'" := ( Seval conf st' ).

(*----------------------------Semantic_Equivalence---------------------------*)
Definition Aequiv (a1 a2 : Aexp) : Prop :=
  forall (st : State),
    Aeval st a1 = Aeval st a2.

Definition Bequiv (b1 b2 : Bexp) : Prop :=
  forall (st : State),
    Beval st b1 = Beval st b2.

Definition Sequiv (S1 S2 : Stm) : Prop :=
  forall (st st' : State),
    << S1 , st >> --> st' <-> << S2 , st >> --> st'.

Theorem stm_eq :
  forall S s s' s'',
  << S, s >> --> s' ->
  s' = s'' ->
  << S, s >> --> s''.
Proof.
  intros.
  subst.
  apply H.
Qed.
