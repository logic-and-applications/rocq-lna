Require Import Strings.String.
Require Import SCcoq.Framework_common.

Reserved Notation " conf '==>' conf' "
                  (at level 99). (*levels?*)

Inductive sstep : Config -> Config -> Prop:=
| skip_sos : forall  st, <<SKIP, st>> ==> st
| ass_sos: forall x a n st,
    Aeval st a = n ->
    <<(x::=a), st>> ==> <<(x !-> n, st)>>(*t_update st x n)*)

(*don't forget - a derivation tree is written bottom up but read top-down. 
This is reading*)
| comp_I_sos: forall S1 S1' S2 st st',
    <<S1, st>> ==> <<S1', st'>> ->
    <<S1; S2, st>> ==> <<S1'; S2, st'>>

| comp_II_sos:  forall S1  S2 st st',
    <<S1, st>> ==> Final st' ->
    <<S1;S2, st>> ==> <<S2, st'>>
  
| if_tt_sos: forall b S1 S2 st,
    Beval st b = true ->
    <<IF_ b THEN S1 ELSE S2, st>> ==> <<S1, st>>

| if_ff_sos: forall b S1 S2 st,
    Beval st b=  false ->
    <<IF_ b THEN S1 ELSE S2, st>> ==> <<S2, st>>
  
|  while_sos: forall b S st,
    <<WHILE b DO S, st>> ==>
    <<IF_ b THEN (S; WHILE b DO S) ELSE SKIP, st>>
  where " conf '==>' conf' " := (sstep conf conf').


Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multirefl : forall (x : X), multi R x x
  | multistep : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
                    
Notation " t '==>*' t' " := (multi sstep t t') (at level 40).

(*those, to the end are for the equality of states*)
Theorem stm_eq:
  forall S s conf' conf'',
  <<S,s>>==> conf' ->
  conf' =conf'' ->
  <<S,s>> ==> conf''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Theorem no_stm_eq:
  forall s conf' conf'',
  <<s>>==>* conf' ->
  conf' =conf'' ->
  <<s>> ==>* conf''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Theorem conf_stm_eq:
  forall conf conf' conf'',
  conf==>* conf' ->
  conf' =conf'' ->
  conf ==>* conf''.
Proof.
  intros.
  rewrite H0 in H.
  apply H.
Qed.

Theorem conf_eq_rn:
  forall S s s',
  s = s' -> <<S,s>> = <<S,s'>>.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem conf_eq_fn:
  forall s s',
  s = s' -> <<s>> = <<s'>>.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Ltac wrap_up_star :=
   eapply no_stm_eq; (*repart, or*)
   try eapply multirefl;
   apply conf_eq_fn;
   eq_states.
