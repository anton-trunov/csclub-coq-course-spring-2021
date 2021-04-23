From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section CaseTacticForTypeFamilies.

(** * Exercise *)
(* CONSTRAINTS: do _not_ use `rewrite`, `->` or any lemmas to solve this exercise.
   Use _only_ the `case` tactic *)
Lemma sym T (x y : T) :
  x = y -> y = x.
Proof.
Admitted.
(* Hint: use the `case: ... / ...` variant *)


(** * Exercise *)
(* Figure out what `alt_spec` means and prove the lemma *)
Lemma altP P b :
  reflect P b -> alt_spec P b b.
Proof.
Admitted.
(* Hint: use the `case: ... / ...` variant *)

End CaseTacticForTypeFamilies.



Section MultiRules.

(** * Exercise: A spec for boolean equality *)
Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Type :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.


Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof.
Admitted.
(** Hint: Use `case: (altP eqP)` to get the right assumptions.
          Also, try using `case: eqP` instead to see the difference. *)


(** * Exercise: use `eqVneq` to prove this lemma *)
Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof.
Admitted.


(** * Exercise *)
Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof.
Admitted.

Arguments andX {a b}.

(** * Exercise: prove the following lemma using `andX` lemma. *)
(* CONSTRAINTS: you may only use `move` and `rewrite` to solve this;
     no `case` or `[]` or any other form of case-splitting is allowed!
     and no lemmas other than `andX` *)
Lemma andX_example a b :
  a && b -> b && a && a && b.
Proof.
Admitted.
(** Hint: `reflect`-lemmas may act like functions (implications) *)

End MultiRules.


