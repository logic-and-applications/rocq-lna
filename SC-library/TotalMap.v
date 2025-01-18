(* First, we need some imports from the Coq library *)
Require Import Bool.Bool.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.

(* To define the states we will use the total maps from the Maps chapter of
   Software Foundations *)
Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
 Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if string_dec x x' then v else m x'.

(* Some notations *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Notation "x '!->' v ',' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition string_noteq
           {A : Type}
           {s1 s2 : string}
           (p : s1 = s2)
           (q : eqb s1 s2 = false)
  : A.
Proof.
  induction p.
  rewrite eqb_refl in q.
  contradiction (diff_true_false q).
Qed.

Ltac eq_states :=
  apply functional_extensionality ;
  intro ; unfold t_update ;
  repeat match goal with
           |- context [string_dec ?v ?x] =>
           destruct (string_dec v x)
         end ; try reflexivity ;
  subst ;
  match goal with
  | [p : ?s = ?s' |- _] => try (refine (string_noteq p _) ; reflexivity)
  | _ => idtac
  end ;
  try contradiction.

(** Some notation for string which will be used *)
Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
