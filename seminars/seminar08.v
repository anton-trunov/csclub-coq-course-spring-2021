From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(*| Insert an element `e` into a sorted list `s` |*)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then
      e :: s
    else
      x :: (insert e s')
  else [:: e].

(*| Sort input list `s` |*)
Fixpoint sort s : seq T :=
  if s is x :: s' then
    insert x (sort s')
  else
    [::].

(** * Exercise *)
Lemma sorted_cons x s :
  sorted leT (x :: s) -> sorted leT s.
Proof.
Admitted.

(** * Exercise *)
Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
Admitted.

End InsertionSort.
End Insertion.



(** * Exercise: implement guarded interleave function *)

(* here is its unguarded version *)
Unset Guard Checking.
Fixpoint interleave_ns {T} (xs ys : seq T)
           {struct xs} : seq T :=
  if xs is (x :: xs') then x :: interleave_ns ys xs'
  else ys.
Set Guard Checking.

(** A simple unit test. *)
Check erefl : interleave_ns [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4].

Fixpoint interleave {T} (xs ys : seq T) : seq T :=
  ...

Lemma interleave_ns_eq_interleave {T} :
  (@interleave_ns T) =2 (@interleave T).
Proof.
Admitted.



(** * Exercise: implement Ackermann's function

It's defined via the following expressions:

  A(0,   n)   = n + 1
  A(m+1, 0)   = A(m, 1)
  A(m+1, n+1) = A(m, A(m+1, n))
*)



(** * Exercise: implement merge function via Program plugin *)
From Coq Require Import Program.
Program Fixpoint merge s t {measure <your-measure>} : seq T :=
  ...
Next Obligation. ... Qed.
Next Obligation. ... Qed.
Next Obligation. ... Qed.


