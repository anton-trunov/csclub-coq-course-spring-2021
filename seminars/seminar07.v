From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Exercise: Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

(** This should not fail! *)
Fail Check (1, Yes) == (1, Maybe).


(** * Exercise: Define equality type for the following datatype *)
Record record : predArgType := Mk_record {
  A : nat;
  B : bool;
  C : nat * nat;
}.


Variable test : record.
Fail Check (test == test).




(** Optional exercises:
There is a library to reduce boilerplate while building
instances of basic MathComp classes for inductive data types:
https://github.com/arthuraa/deriving.

Install it (it's available from extra-dev opam repository)
and use it to solve some of the above exercise.
*)



(** * Odd and even numbers *)


Structure odd_nat := Odd {
  oval :> nat;
  oprop : odd oval
}.

(** Prove the main property of [odd_nat] *)
Lemma oddP (n : odd_nat) : odd n.
Admitted.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP (n : even_nat) : ~~ (odd n).
Admitted.


(** ** Part 1: Arithmetics *)


(** The objective is to make it work: knowing that
    [n] is [odd] Coq should infer that [n * 3]
    is also [odd], and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(* Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := @Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Admitted.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Admitted.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)
(*
Canonical odd_even (m : even_nat) : odd_nat :=
  ...
 *)

(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)
(*
Canonical even_odd (m : odd_nat) : even_nat :=
  ...
*)

(** Now let's deal with multiplication *)
Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Admitted.

(** Teach Coq that [*] preserves being [odd] *)
(*
Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  ...
 *)

(* It should work now! *)
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.


(** ** Part 2: Equality *)

(** We can't use [==] on [odd] natural numbers because
   [odd_nat] is not an [eqType] *)
Fail Check forall n : odd_nat, n == n.

(** Use the [subType] machinery in order
   to teach Coq that [odd_nat] is an [eqType] *)
(*
Canonical odd_subType :=
Definition odd_eqMixin :=
Canonical odd_eqType :=
 *)

(* This should work now *)
Check forall n : odd_nat, n == n.
Lemma odd_nat_eq_refl (n : odd_nat) :
Proof. by rewrite eq_refl. Qed.

(** Now deal with [even_nat] *)
Fail Check forall (m : even_nat), m == m.

Check forall (m : even_nat), m == m.

Lemma odd_nat_eq_refl (n : even_nat) :
Proof. by rewrite eq_refl. Qed.




