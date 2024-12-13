Inductive var: Set := p: nat -> var.


Inductive formula: Set :=
|Atom: var -> formula
|Top: formula
|Bottom: formula
|Not: formula -> formula
|And: formula -> formula -> formula
|Or: formula -> formula -> formula
|Imp: formula -> formula -> formula
|BiImp: formula -> formula -> formula
|Box: formula -> formula
|Diamond: formula -> formula.

Infix "/\_" := And (at level 52).
Infix "\/_" := Or (at level 52).
Infix "->_" :=  Imp (at level 51, right associativity).
Infix "<->_" := BiImp (at level 53, left associativity).

Notation "~_" := Not.

 (*Check (Box(Atom(p O))) --> (Box(Atom(p O)) || (Atom(p(S O)))). *)
Record frame: Type := {
  W: Set; (* worlds *)
  R: W -> W -> Prop}. (* accessibility relation R \subseteq W x W *)

Record kripke: Type := {
  F: frame; (* F = (W,R) *)
  L: (W F) -> var -> Prop}.
(* labelling function L: W -> Atomomic -> {True,False} *)
(* M,x ||- phi *)

Fixpoint satisfies (M:kripke) (x: (W (F M))) (phi: formula): Prop :=
match phi with 
|Top => True
|Bottom => False
|(Not phi) => ~(satisfies M x phi)
|(And phi_1 phi_2) =>
  (satisfies M x phi_1) /\ (satisfies M x phi_2)
|(Or phi_1 phi_2) =>
  (satisfies M x phi_1) \/ (satisfies M x phi_2)
|(Imp phi_1 phi_2) =>
  (satisfies M x phi_1) -> (satisfies M x phi_2)
|(BiImp phi_1 phi_2) =>
  (satisfies M x phi_1) <-> (satisfies M x phi_2)
|(Box phi) =>
  (forall y: (W (F M)), (R (F M) x y) -> (satisfies M y phi))
|(Diamond phi) =>
  (exists y: (W (F M)) , (R (F M) x y) /\ (satisfies M y phi))
|(Atom (p n)) => (L M x (p n)) 
end.

Axiom diamond_to_box :
forall phi:formula,
  Diamond phi = Not (Box (Not phi)).

Axiom box_to_diamond:
forall phi:formula,
  Box phi = Not (Diamond (Not phi)).

(* M ||- phi *)
Definition M_satisfies 
(M: kripke) (phi: formula) := forall w: (W (F M)), satisfies M w phi.

(* F |= phi *)
Definition valid_in_frame_with_labeling
  (F: frame) (phi: formula) (L: (W F) -> var -> Prop):=
(M_satisfies (Build_kripke F L) phi).
(* Definition valid_in_frame (F:frame) (phi:formula) :=
forall L, valid_in_frame_with_labeling F phi L.
*)

(* |= phi *)
(*
Definition valid (phi:formula) :=
forall (F:frame), (valid_in_frame F phi).
*)
