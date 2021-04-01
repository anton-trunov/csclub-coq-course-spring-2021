From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.



(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= replace_with_your_solution_here.


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= replace_with_your_solution_here.


(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= replace_with_your_solution_here.


(** * Exercise *)
Definition false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False
:= replace_with_your_solution_here.


(** * Exercise *)
Definition addnS :
  forall m n, m + n.+1 = (m + n).+1
:= replace_with_your_solution_here.


(** * Exercise *)
Definition addA : associative addn
:= replace_with_your_solution_here.


(** * Exercise: *)
Definition addnCA : left_commutative addn
:= replace_with_your_solution_here.


(** * Exercise (optional): *)
Definition addnC : commutative addn
:= replace_with_your_solution_here.


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)


(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.

