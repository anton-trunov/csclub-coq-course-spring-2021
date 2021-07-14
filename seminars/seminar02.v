From mathcomp Require Import ssreflect.

Axiom replace_with_your_solution_here : forall {A : Type}, A.

(* Remember function from the first lecture *)

Definition foo := fun (f : bool -> bool) => f true.

(* We can generalize it a bit *)

Definition applyb : bool -> (bool -> bool) -> bool 
  := fun (b : bool) (f : bool -> bool) => f b.


(* implement polymorphic version of the apply funtion *)
(* Say about `forall` erasing *)

(* implement parameterized inductive of prod3 *)

(* Inductive prod3 ... : ... :=
  | triple ... *)


(* Without Coq try to infer `prod3`'s and `triple`'s type *)

(*

Check prod3.
Check triple.

*)

(* Make implicit some `apply`'s and `triple`'s arguments *)
(* Say about alternative way of Implicit's  *)

(* Introduce a haskell like `$` notation *)

Section Haskell.

(* Local Notation .. := .. . *)

End Haskell.

(* Introduce a (a; b; c) notation for triple *)

(* Notation .. := .. *)


(* function composition *)

Definition comp A B C (f : B -> A) (g : C -> B)  : C -> A
:= replace_with_your_solution_here.


(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:= replace_with_your_solution_here.

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:= replace_with_your_solution_here.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:= replace_with_your_solution_here.

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:= replace_with_your_solution_here.

(* Introduce `unit` type (a type with exactly one canonical form) *)

(* () : () *)
Inductive unit : Type :=
  | tt.

Definition unit_initial (A : Type) :
  A -> unit
:= replace_with_your_solution_here.

(* Introduce empty type, call `void` *)

Inductive void : Type := .

Definition void_terminal (A : Type) :
  void -> A
:= replace_with_your_solution_here.


(* Think of some more type signatures involving void, unit, sum, prod *)
