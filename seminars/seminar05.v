From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.



(** * Exercise *)

Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then
    fib n'' + fib n'
  else n.

Arguments fib : simpl nomatch.

Fixpoint fib_iter (n : nat) (f0 f1 : nat) : nat :=
  if n is n'.+1 then
    fib_iter n' f1 (f0 + f1)
  else f0.

Arguments fib_iter : simpl nomatch.

Lemma fib_iterS n f0 f1 :
  fib_iter n.+1 f0 f1 = fib_iter n f1 (f0 + f1).
Proof. by []. Qed.


(** Sometimes instead of a custom induction
    principle we can come up with a different
    formulation of the specification.*)
Lemma fib_iter_spec n f0 f1 :
  fib_iter n.+1 f0 f1 = f0 * fib n + f1 * fib n.+1.
Proof.
Admitted.

Lemma fib_iter_correct' n :
  fib_iter n 0 1 = fib n.
Proof.
Admitted.





(** * Exercise *)
(** Implement a recursive function performing integer division by 2 *)
Fixpoint div2 (n : nat) : nat :=
  replace_with_your_solution_here.


Arguments div2 : simpl nomatch.

(** * Exercise *)
Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
Admitted.

(** Exercise: use [nat_ind2'] to prove the following *)
Lemma div2_le n : div2 n <= n.
Proof.
Admitted.

(** Hints: you might want to use [leqW] view lemma *)

(* Double induction/recursion. *)
Lemma seq_ind2 {S T} (P : seq S -> seq T -> Type) :
  P [::] [::] ->
  (forall x y s t, size s = size t ->
                   P s t -> P (x :: s) (y :: t)) ->
  forall s t, size s = size t -> P s t.
Proof.
Admitted.




(* === Optional exercises === *)

(* due to D.A. Turner, see his "Total Functional
Programming" (2004) paper *)

(** * Optional Exercise *)
Lemma fib_iter_spec' n p :
  fib_iter n (fib p) (fib p.+1) = fib (p + n).
Proof.
Admitted.

(** * Optional Exercise *)
Lemma fib_iter_correct'' n :
  fib_iter n 0 1 = fib n.
Proof.
Admitted.


(** * Optional Exercise *)
Lemma ltn_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
Admitted.
