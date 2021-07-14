From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From mathcomp Require Import zify.
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
case.
case.
move=> a b c.
split.
- exact: a.
split.
- exact: b.
exact: c.
Qed.

Lemma andA' :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
by case=> [[a b] c].
Defined.

About andA.

Compute andA.

About andA'.

Compute andA'.


(** * Exercise *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
by case=> [a [b|c]]; [left|right].
Qed.

(** * Exercise *)
Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
by case=> [a|[b c]]; split; left + right.
Qed.

(** * Exercise *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof. by []. Qed.
(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion
principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple
automation. *)


(** * Exercise *)

Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
move=> ab bc a.
move: bc.
apply.
move: ab.
apply.
exact: a.

Restart. Show.

by move=> ab bc /ab.
Qed.


(** * Exercise *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.
apply; exact.
Qed.

(** * Exercise *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.
(* move=> ?; exact: I. *)
by [].
Qed.

(** * Exercise *)
Lemma DNE_triple_neg :
  ~ ~ ~ A -> ~ A.
Proof.
by move=> /[swap] a; do ? apply.
Qed.
(** Hint : use `apply: (identifier)`
to apply a hypothesis from the context to
the goal and keep the hypothesis in the context *)

End IntLogic.

(** * Exercise *)
Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
move=> nana.
by have [nna /nna] : ~ ~ A /\ ~ A by split=> a; apply: nana; left + right.
Qed.
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
Proof. move=> f; exact: (f False id). Qed.


Section Boolean.
(** * Exercise *)
Lemma negbNE b : ~~ ~~ b -> b.
Proof. by case: b. Qed.


(** * Exercise *)
Lemma negbK : involutive negb.
Proof. by case. Qed.

(** * Exercise *)
Lemma negb_inj : injective negb.
Proof. by case=> [][]. Qed.

End Boolean.

Section EquationalReasoning.

Variables A B : Type.

(** * Exercise 10 *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof. by move=> x. Qed.


(** * Exercise 11 *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.
by move=> fg x; rewrite fg.
Qed.
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
by move=> fg gh ?; rewrite fg.
Qed.

End EquationalReasoning.



(** * Exercise *)
Lemma and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B.
Proof.
split=> [][] a b.
- by split.
by exists a.
Qed.

(** * Exercise *)
(* Hint: the `case` tactic understands constructors are injective *)
Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof. by case=>->->. Qed.


(** * Exercise *)
Lemma false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False.
Proof.
by [].
Qed.

(** * Exercise *)
Lemma addn0 :
  right_id 0 addn.
Proof. by elim=> // ?; rewrite addSn=>->. Qed.


(** * Exercise *)
Lemma addnS :
  forall m n, m + n.+1 = (m + n).+1.
Proof. by move=> m n; elim: m=> // ?; rewrite addSn=>->. Qed.

(** * Exercise: *)
Lemma addnCA : left_commutative addn.
Proof. by move=> n m k; elim: m=> // ?; rewrite addSn addnS=>->. Qed.


(** * Exercise: *)
Lemma addnC : commutative addn.
Proof.
by move=> n m; elim: n=> [|? IHn]; rewrite (addn0, addSn) // addnS IHn.
Qed.

(** * Exercise (optional): *)
Lemma unit_neq_bool:
  unit <> bool.
Proof.
move=> ub.
suff/(_ true false): forall a b : bool, a = b by [].
by rewrite -ub=> [[[]]].
Qed.

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
by elim: n a=> [[]//|n IHn [] /=]; rewrite IHn // eqbF_neg.
Qed.

(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]).
    See https://en.wikipedia.org/wiki/Tail_call
 *)

Fixpoint add_iter (n m : nat) {struct n}: nat :=
  if n is n'.+1 then add_iter n' m.+1 else m.

Lemma add_iter_correct n m :
  add_iter n m = n + m.
Proof. by elim: n m=> //= ? IHn ?; rewrite IHn addnS. Qed.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
by elim: n m=> [[]//|? IHn [//|]?]; rewrite !addSn !addnS=> [[/IHn->]].
Qed.

Lemma nat_3k5m n : exists k m, n + 8 = 3 * k + 5 * m.
Proof.
elim: n=> [|n [k1 [m1]]]; first by exists 1, 1.
rewrite addSn=> /[dup] {2}->.
case: m1=> [|n1 _]; last exists k1.+2, n1.
- case: k1; first by case: n.
  (do ? (case; first by rewrite addnC))=> k _.
  by exists k, 2; rewrite !mulnS muln0 ?addn0 [3 * k + _]addnC.
by rewrite !mulnS !addSn -!addnS.
Qed.




