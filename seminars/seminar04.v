From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* SSReflect tactic practice *)

Section IntLogic.

Variables A B C : Prop.

(** * Exercise *)
Lemma andA :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.

Admitted.


(** * Exercise *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.

Admitted.


(** * Exercise *)
Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.

Admitted.


(** * Exercise *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof.

Admitted.
(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion
principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple
automation. *)


(** * Exercise *)
Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.

Admitted.


(** * Exercise *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.

Admitted.


(** * Exercise *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.

Admitted.


(** * Exercise *)
Lemma LEMisNotFalse :
  ~ ~ (A \/ ~ A).
Proof.

Admitted.
(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)


(** * Exercise *)
Lemma weak_Peirce :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.

Admitted.

End IntLogic.


Section EquationalReasoning.

Variables A B : Type.

(** * Exercise 10 *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof.

Admitted.


(** * Exercise 11 *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.

Admitted.
(** Hint: `rewrite` tactic also works with
universally quantified equalities. I.e. if you
have a hypothesis `eq` of type `forall x, f x = g
x`, you can use `rewrite eq` and Coq will usually
figure out the concrete `x` it needs to specialize
`eq` with, meaning that `rewrite eq` is
essentially `rewrite (eq t)` here. *)


(** * Exercise *)
Lemma eqext_trans (f g h : A -> B) :
  f =1 g -> g =1 h -> f =1 h.
Proof.

Admitted.

End EquationalReasoning.



(** * Exercise *)
Lemma and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.

Admitted.


(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof.

Admitted.


(** * Exercise *)
Lemma false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False.
Proof.

Admitted.


(** * Exercise *)
Lemma addn0 :
  right_id 0 addn.
Proof.

Admitted.


(** * Exercise *)
Lemma addnS :
  forall m n, m + n.+1 = (m + n).+1.
Proof.

Admitted.


(** * Exercise: *)
Lemma addnCA : left_commutative addn.
Proof.

Admitted.


(** * Exercise: *)
Lemma addnC : commutative addn.
Proof.

Admitted.


(** * Exercise (optional): *)
Lemma unit_neq_bool:
  unit <> bool.
Proof.

Admitted.
