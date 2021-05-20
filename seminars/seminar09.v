From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.

Section Exercise1.
Definition impl_distr (A B C : Prop) :
  (A -> (B -> C)) <-> ((A -> B) -> (A -> C))
:= replace_with_your_solution_here.
End Exercise1.



Section Exercise2.
Variable DNE : forall A : Prop, ~ ~ A -> A.

Lemma drinker_paradox (P : nat -> Prop) :
  exists x, P x -> forall y, P y.
Proof.
Admitted.
End Exercise2.



Section Exercise3.
Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
Admitted.

End Exercise3.



Section Exercise4.
(** Continuation-passing style list sum function
    See https://en.wikipedia.org/wiki/Continuation-passing_style *)

(** Recursive helper function *)
Fixpoint sumn_cont' {A} (l : seq nat) (k : nat -> A) : A :=
  if l is (x :: xs) then sumn_cont' xs (fun answer => k (x + answer))
  else k 0.

(** The main definition *)
Definition sumn_cont (l : seq nat) : nat :=
  sumn_cont' l (fun x => x).

Lemma sumn_cont'_correct A l (k : nat -> A) :
  sumn_cont' l k = k (sumn l).
Admitted.

(** Prove that the continuation-passing style list sum function is correct w.r.t
    the standard [sumn] function *)
Lemma sumn_cont_correct l :
  sumn_cont l = sumn l.
Proof.
Admitted.

End Exercise4.



Section Exercise5.
(* Prove [8x = 6y + 1] has no solutions in [nat] *)

Lemma no_solution x y :
  8*x != 6*y + 1.
Proof.
Admitted.
End Exercise5.



Section Exercise6.
Lemma exercise n :
  ~~ odd n ->
  (n.-1 %/ 2) = (n %/ 2 - 1).
Proof.
Admitted.

End Exercise6.





(*** Extra topics *)

(** * Strict positivity *)

Unset Positivity Checking.
Inductive prop :=
  RemoveNegation of (prop -> False).
Set Positivity Checking.
Print Assumptions prop.

Definition not_prop (p : prop) : False :=
  let '(RemoveNegation not_p) := p in not_p p.

Check RemoveNegation not_prop : prop.

Definition yet_another_proof_of_False : False :=
  not_prop (RemoveNegation not_prop).

Print Assumptions yet_another_proof_of_False.




(** * Russel's Paradox  in Prop *)

Module RusselInProp.
(* the universe of all sets *)
Inductive U : Prop :=
  set (L : Prop) (i : L -> U) (P : L -> Prop).
(* L -- labels for elements of the universe *)
(* i -- function interpreting labels into sets (the elements of the universe) *)
(* P -- the predicate on labels corresponding to a set we want to define *)


(* Membership relation: x \in A *)
Fail Definition In (x A : U) : Prop :=
  match A with
  | set L i P => exists lx, (x = (i lx)) /\ (P lx)
  end.

End RusselInProp.



(** * Russel's Paradox  in Type (Using Type-In-Type) *)

Module RusselInType.

(* a bit of logic in Type (as opposed to Prop) *)

Inductive And (A B : Type) : Type :=
  and_ : A -> B -> And A B.

Inductive Exists {A : Type} (P : A -> Type) : Type :=
  exists_ : forall (a : A), (P a) -> Exists P.

Inductive Eq {A : Type} (x : A) : A -> Type :=
  eq_refl_ : Eq x x.

Inductive FalseT : Type := .



(* the universe of all sets, now in Type *)
Inductive U : Type :=
  set (L : Type) (i : L -> U) (P : L -> Type).

(* L -- labels for elements of the universe *)
(* i -- function interpreting labels into sets (the elements of the universe) *)
(* P -- the predicate on labels corresponding to a set we want to define *)

(* Membership relation: x \in A *)
(* if an element x belongs to a set A, this means there exists a labels for x,
   such that the interpretation of the label is the same as x and
   the predicate underlying X holds on x *)
(* notice that we work in an essentially untyped setting *)
Definition In (x A : U) : Type :=
  (* if we worked in Prop, we wouldn't be able to pattern-match here
     as large elimination is prohibited for Prop *)
  match A with
  | set L i P => Exists (fun (lx : L) => And (Eq x (i lx)) (P lx))
  end.

Definition proper (X : U) : Type := In X X -> FalseT.

Unset Universe Checking.
Definition ps : U := set U (fun l => l) proper.
Set Universe Checking.

Lemma proper_ps : proper ps.
Proof. by move=> p; case: (p)=> l [<-]; apply. Qed.

Lemma not_proper_ps : proper ps -> FalseT.
Proof. by apply; exists ps; split=>//; apply: proper_ps. Qed.

Lemma inconsistency : FalseT.
Proof. exact: (not_proper_ps proper_ps). Qed.

End RusselInType.
