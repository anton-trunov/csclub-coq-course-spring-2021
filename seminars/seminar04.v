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

Lemma andA' :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
Admitted.

About andA.

Compute andA.

About andA'.

Compute andA'.


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
Lemma DNE_triple_neg :
  ~ ~ ~ A -> ~ A.
Proof.
Admitted.
(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)

End IntLogic.

(** * Exercise *)
Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
Admitted.
(** Hint: you might want to use a separate lemma here to make progress.
Or, use the `have` tactic: `have: statement` creates a new subgoal and asks
you to prove the statement. This is like a local lemma. *)


(** * Exercise *)
Lemma weak_Peirce (A B : Prop) :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
Admitted.


(** * Exercise *)
(* Prove that having a general fixed-point combinator in Coq would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma fix_inconsistent :
  FIX -> False.
Proof.
Admitted.


Section Boolean.
(** * Exercise *)
Lemma negbNE b : ~~ ~~ b -> b.
Proof.
Admitted.


(** * Exercise *)
Lemma negbK : involutive negb.
Proof.
Admitted.


(** * Exercise *)
Lemma negb_inj : injective negb.
Proof.
Admitted.

End Boolean.

Section EquationalReasoning.

Variables A B : Type.

Locate "_ =1 _".
Print eqfun.

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

(** [==] is the decidable equality operation for types with decidable equality.
    In case of booleans it means [if and only if]. *)
    Fixpoint mostowski_equiv (a : bool) (n : nat) :=
      if n is n'.+1 then mostowski_equiv a n' == a
      else a.
    
    (** The recursive function above encodes the following classical
        propositional formula:
        [((A <-> A ...) <-> A) <-> A]
        For instance, if n equals 3 then the formula look like this
        [((A <-> A) <-> A) <-> A]
        Since we work in the classical propositional fragment
        we can encode the [<->] equivalence with boolean equality [==].
     *)
    Print odd.
    (** Try to come up with a one-line proof *)
Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
Admitted.

(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]).
    See https://en.wikipedia.org/wiki/Tail_call
 *)

Fixpoint add_iter (n m : nat) {struct n}: nat.
  Admitted.

Lemma add_iter_correct n m :
  add_iter n m = n + m.
Proof.
Admitted.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
Admitted.

Lemma nat_3k5m n : exists k m, n + 8 = 3 * k + 5 * m.
Proof. Admitted.