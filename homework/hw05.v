From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Use SSReflect tactics.
    DO NOT use automation like [tauto], [intuition], [firstorder], etc.,
    except for [by], [done], [exact] tactic(al)s. *)


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


(** * Exercise *)
Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
Admitted.
(** Hints:
- use the /= action to simplify your goal: e.g. move=> /=.
- use `Search (<pattern>)` to find a useful lemma about multiplication
*)


(** * Exercise
Prove by it induction: you may re-use the addnS and addSn lemmas only *)
Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
Admitted.
(* This is a harder exercise than the previous ones but
   the tactics you already know are sufficient *)




(** * Optional exercise
    [negb \o odd] means "even".
    The expression here says, informally,
    the sum of two numbers is even if the summands have the same "evenness",
    or, equivalently, "even" is a morphism from [nat] to [bool] with respect
    to addition and equivalence correspondingly.
    Hint: [Unset Printing Notations.] and [rewrite /definition] are your friends :)
 *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
Admitted.


(** * Optional exercise *)
Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Proof.
Admitted.


(** * Optional exercise *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
Search (_ <= _ + _).
Admitted.
(** Hint: this lemmas does not require induction, just look for a couple lemmas *)





(* ================================================ *)

(*
More fun with functions, OPTIONAL
*)

Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

(** * Optional exercise *)
Lemma surj_epic f : surjective f -> epic f.
Proof.
Admitted.

(** * Optional exercise *)
Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Admitted.

(** * Optional exercise *)
Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Admitted.

(** * Optional exercise *)
Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

(** * Optional exercise *)
Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.


(** * Optional exercise *)
Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

(** * Optional exercise *)
Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

(** * Optional exercise *)
Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.
