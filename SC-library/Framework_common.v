(* First, we need some imports from the Coq library *)
Require Import Bool.Bool.
Require Import ZArith_base.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Export SCcoq.TotalMap.

(* Open Z scope, needed for Num *)
Local Open Scope Z_scope.
Declare Scope while_scope.
Open Scope while_scope.

(* Syntax Num*)
Inductive Num : Type :=
  | NZero
  | NOne
  | NEven (n : Num)
  | NOdd (n : Num).

(* Semantics Num*)
Fixpoint Neval (n : Num) : Z :=
  match n with
  | NZero => 0
  | NOne => 1
  | NEven n => 2*(Neval n)
  | NOdd n => 2*(Neval n) + 1
  end.

(* Variables of the type Num should be recognized as integers *)
(*Coercion Neval: Num >-> Z.*)

(* However, this should also work the other way around
   We do this by using the Coq standard library type positive *)
Fixpoint pos_to_num (n : positive) : Num:=
 match n with
  |xH => NOne
  |xO n' => NEven (pos_to_num n')
  |xI n' => NOdd (pos_to_num n')
  end.

Definition z_to_num (z : Z) : Num :=
  match z with
  | Z0 => NZero
  | Zpos n => pos_to_num n
  | Zneg n => pos_to_num n
  end.

Coercion z_to_num: Z >-> Num.
  
(* We want to define a total map from variables to integers *)
Definition State := total_map Z.
Definition empty_State := (_ !-> 0).
Notation "x '!->' v" := (x !-> v, empty_State)
  (at level 100, v at next level, right associativity).

(* Syntax Aexp*)
Inductive Aexp : Type :=
| ANum (n : Num)
| AId (x : string)
| APlus (a1 a2 : Aexp)
| AMinus (a1 a2 : Aexp)
| AMult (a1 a2 : Aexp).

Fixpoint substAexp
         (a : Aexp)
         (x : string)
         (a' : Aexp)
  : Aexp
  := match a with
     | ANum n => ANum n
     | AId y => if string_dec x y then a' else AId y
     | APlus a1 a2 => APlus (substAexp a1 x a') (substAexp a2 x a')
     | AMinus a1 a2 => AMinus (substAexp a1 x a') (substAexp a2 x a')
     | AMult a1 a2 => AMult (substAexp a1 x a') (substAexp a2 x a')
     end.

(* Semantics Aexp *)
Fixpoint Aeval (st : State) (a : Aexp) : Z :=
  match a with
  | ANum n => Neval n
  | AId x => st x
  | APlus a1 a2 => (Aeval st a1) + (Aeval st a2)
  | AMinus a1 a2  => (Aeval st a1) - (Aeval st a2)
  | AMult a1 a2 => (Aeval st a1) * (Aeval st a2)
  end.

(* Coercions are needed such that variables and numerals are seen as Aexp
   and we can evaluate with them *)
Coercion AId : string >-> Aexp.
Coercion ANum : Num >-> Aexp.

(* Syntax Bexp*)
Inductive Bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : Aexp)
  | BLe (a1 a2 : Aexp)
  | BNot (b : Bexp)
  | BAnd (b1 b2 : Bexp).

Fixpoint substBexp
         (b : Bexp)
         (x : string)
         (a' : Aexp)
  : Bexp
  := match b with
     | BTrue => BTrue
     | BFalse => BFalse
     | BEq a1 a2 => BEq (substAexp a1 x a') (substAexp a2 x a')
     | BLe a1 a2 => BLe (substAexp a1 x a') (substAexp a2 x a')
     | BNot b => BNot (substBexp b x a')
     | BAnd b1 b2 => BAnd (substBexp b1 x a') (substBexp b2 x a')
     end.

(* Semantics Bexp *)
Fixpoint Beval (st : State) (b : Bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (Aeval st a1) =? (Aeval st a2)
  | BLe a1 a2   => (Aeval st a1) <=? (Aeval st a2)
  | BNot b1     => negb (Beval st b1)
  | BAnd b1 b2  => andb (Beval st b1) (Beval st b2)
  end.

Definition bool_to_bexp (b : bool) : Bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> Bexp.

(* Notation such that we can use our normal arithmetic operators *)
Bind Scope while_scope with Aexp.
Bind Scope while_scope with Bexp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : while_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : while_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : while_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : while_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : while_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : while_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : while_scope.

(* Notation such that we can use similar notation as the book uses *)
Notation " 'A[[' a ']]' st " := (Aeval st a)
  (at level 90, left associativity).
Notation " 'B[[' b ']]' st " := (Beval st b)
  (at level 90, left associativity).
Notation " 'N[[' n ']]'" := (Neval n)
  (at level 90, left associativity).

(* Syntax Statements*)
Inductive Stm : Type :=
  | ass (x : string) (a : Aexp)
  | skip
  | comp (s1 s2 : Stm)
  | if_ (b : Bexp) (s1 s2 : Stm)
  | while (b : Bexp) (s : Stm).

(* Notations such that we can use similar statement notation as the book *)
Notation "x '::=' a" :=
  (ass x a) (at level 60).
Notation "'SKIP'" :=
   skip.
Notation "s1 ; s2" := 
  (comp s1 s2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' s " :=
  (while b s) (at level 80, right associativity).
Notation "'IF_' b 'THEN' s1 'ELSE' s2 " := 
  (if_ b s1 s2) (at level 80, right associativity).

(* Configurations definition *)
Inductive Config: Type :=
| Running (S:Stm) (s:State)
| Final (s:State).

Coercion Final: State >-> Config.
Notation "'<<' s '>>' " := (Final s).
Notation "'<<' S ',' st '>>'" := (Running S st).
