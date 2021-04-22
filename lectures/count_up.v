From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

(*|
Accessibility predicate on natural numbers
========================================== *)

Section AccFrom.

Variable (p : pred nat).

(*| The `acc_from` predicate lets us count up: we
are not allowed to use `acc_from` to drive
computation (extract information from proofs of
propositions to make computationally relevant
terms), but you can define a recursive function
from a type like this to a type in `Type` and the
*termination checker* is totally (pun intended)
happy with it. We'll see this sort of example at
the end. |*)
Inductive acc_from i : Prop :=
| AccNow of p i
| AccLater of acc_from i.+1.

End AccFrom.

(*| Check out the corresponding induction principle. |*)
About acc_from_ind.


(*|
Simple examples
=============== |*)

Section SimpleExamples.

(*| Let's do a couple of proofs to get the gist of `acc_from` |*)

(*| 1. The property of "being equal to 42" is accessible from 0: |*)
Goal acc_from (fun n => n == 42) 0.
Proof.
do 42 apply: AccLater.
by apply: AccNow.
Qed.


(*| 2. But it's inaccessible from 43: |*)
Goal acc_from (fun n => n == 42) 43 -> False.
Proof.
(*| If you start proving the current goal
directly, you will quickly get stuck because your
goal is too specialised. Clearly, you need
induction over the accessibility predicate, but
`elim` messes up your base case (look at the type
of `acc_from_ind`). |*)
elim.
Show Proof.
(* the first subgoal is unprovable *)
Abort.


(*| We could try and create a more useful
induction principle for our case but we might as
well just use a low-level tactic `fix` which
translates directly to Gallina's fixed-point
combinator. |*)

Goal acc_from (fun n => n == 42) 43 -> False.
Proof.
fix inacc 1.
Show Proof.
(*| To recursively call `inacc` on a structurally
smaller argument we need to case analyse the top
of the goal stack: |*)
case.
(*| The base case is easy now: |*)
- by [].
(*| But here we are stuck. |*)
Abort.


(*| So we generalize the goal to make the proof go
through. |*)
Lemma inacc_from43 :
  forall x, 42 < x -> acc_from (fun n => n == 42) x -> False.
Proof.
fix inacc 3.
Show Proof.
move=> x x_gt42.
case=> [/eqP E|].
- by rewrite E in x_gt42.
apply: inacc.
by apply: (ltn_trans x_gt42).
Qed.

End SimpleExamples.


(*|
Getting a concrete value from an abstract existence proof
========================================================= |*)

Section Find.

Variable p : pred nat.

Lemma find_ex :
  (exists n, p n) -> {m | p m}.
Proof.
move=> exp.

have: acc_from p 0.
(*| `acc_from` lives in `Prop`, so we are allowed
to destruct `exp` in this context, see below. |*)
- case: exp => n.
  rewrite -(addn0 n).
  elim: n 0=> [|n IHn] j.
  - by left.
  rewrite addSnnS.
  right.
  apply: IHn.
  by [].

move: 0.
fix find_ex 2=> m IHm.
case pm: (p m).
- by exists m.
apply: find_ex m.+1 _.
(*| Observe we can only destruct `IHm` at this
point where we are tasked with building a proof
and not a computationally relevant term. |*)
case: IHm.
- by rewrite pm.
by [].
Defined.
