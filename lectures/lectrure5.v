(** * Lists and structural induction *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq fintype order eqtype div fingraph. 
From mathcomp Require Import seq path.

(** Note that we added [seq] and [path] modules to imports *)

(** [seq] is a Mathcomp's notation for [list] data type *)
Print seq.
Print list.

(**
   Inductive list (A : Type) : Type :=
   | nil : seq A
   | cons : A -> seq A -> seq A
*)

(** A simple example *)
Compute [:: 1; 2; 3] ++ [:: 4; 5].

(** List concatenation *)
Locate "++".
Print cat.

(** * Structural Induction for Lists *)

Section StructuralInduction.

Check list_ind :
forall (A : Type) (P : seq A -> Prop),
  P [::] ->
  (forall (a : A) (l : seq A), P l -> P (a :: l)) ->
  forall l : seq A, P l.

Variable T : Type.

Implicit Types xs ys zs : seq T.

Lemma catA xs ys zs :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
(** Idiomatic solution *)
by elim: xs=> //= x xs ->.
Qed.

End StructuralInduction.


(** * Classical example: list reversal function *)

(** A naive quadratic implementation *)
Fixpoint rev2 {A : Type} (xs : seq A) : seq A :=
  if xs is x::xs' then
    rev2 xs' ++ [:: x]
  else xs.

(** The standard implementation is tail recursive *)
Print rev.
Print catrev.

(** Exercise *)
Lemma rev2_inv A :
  involutive (@rev2 A).
Proof.
Admitted.


(*** [reflect]-predicate *)


Section MotivationalExample.

Variable T : Type.

Variable p : pred T.
Print pred.
Check p : T -> bool.

Lemma all_filter (s : seq T) :
  all p s -> filter p s = s.
Proof.

(* Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C) s) *)

Print filter.
Print all.

elim: s => //= x s IHs.

rewrite /is_true.
move=> /andP.
(* Set Printing Coercions. *)
rewrite /is_true.
move=> [].
move=> ->.
move/IHs.
move=>->.
done.

Search _ (_ == _) bool.

Restart.

by elim: s => //= x s IHs /andP[-> /IHs->].
Qed.

End MotivationalExample.