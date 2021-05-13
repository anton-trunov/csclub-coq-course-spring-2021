From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Exercise: Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

(* Set Printing All. *)
Check 'I_3. (* [0..n) *)
Print ordinal.

Definition tri_to_ord (t : tri) : 'I_3 :=
  match t with
  | Yes => inord 0
  | No => inord 1
  | Maybe => inord 2
  end.

Definition ord_tri (o : 'I_3) : tri :=
  match (o : nat) with
  | 0 => Yes
  | 1 => No
  | _ => Maybe
  end.

Lemma ord_triK : cancel tri_to_ord ord_tri.
Proof.
(* Search nat_of_ord inord. *)
by case; rewrite /ord_tri /tri_to_ord inordK.
Qed.

Definition tri_eqMixin := CanEqMixin ord_triK.
Canonical tri_eqType := EqType tri tri_eqMixin.


(** This should not fail! *)
Check (1, Yes) == (1, Maybe).
(* Compute (1, Yes) == (1, Maybe). *)
(* Check erefl : (1, Yes) == (1, Maybe) = false. *)


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

opam install coq-deriving

Install it (it's available from extra-dev opam repository)
and use it to solve some of the above exercise.
*)



(** * Odd and even numbers *)


Structure odd_nat := Odd {
  oval : nat;
  oprop : odd oval
}.
Coercion oval : odd_nat >-> nat.

Check @Odd 3 erefl.
Definition o3 := Odd (erefl (odd 3)).
Compute 2 + o3.

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
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(* Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := @Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Admitted.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Admitted.

Example test_oddS (m : even_nat) :
  odd m.+1.
Proof.
Fail rewrite oddP.
Abort.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)
Definition odd_even (m : even_nat) : odd_nat :=
  @Odd m.+1 (oddS (eprop m)).

Canonical Structure odd_even.

Definition even_odd (m : odd_nat) : even_nat :=
  @Even m.+1 (evenS (oprop m)).

Canonical Structure even_odd.

Print Canonical Projections oval.
(* S ?x <- oval ( odd_even ?en) *)

Example test_oddS (m : even_nat) :
  odd m.+3.
Proof.
  rewrite oddP.
odd (S (S (S m)))
odd (oval ?n)
           ..
         odd_nat
(S (S (S m))) ≡ oval ?n
?x ≡ S (S m)
?n ≡ odd_even ?en
?

Set Printing Coercions.
About oddP.
(* oddP : forall n : odd_nat, odd (oval n) *)

rewrite oddP.
(* oddP : forall n : odd_nat, odd n *)
odd (S m)
odd (oval ?n)
           ..
         odd_nat
S m ≡ oval ?n
?n ≡ odd_even ?m
              ..
              even_nat
?m ≡ m
done.
Qed.

(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)
(*
Canonical even_odd (m : odd_nat) : even_nat :=
  ...
*)

(** Now let's deal with multiplication *)
Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
case: n; case: m=> n on m om.
by rewrite oddM on om.
Qed.

(** Teach Coq that [*] preserves being [odd] *)
(*
Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  ...
 *)

(* It should work now! *)
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
rewrite oddP.
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




