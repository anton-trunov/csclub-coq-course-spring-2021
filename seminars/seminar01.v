From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:=

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:=

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:=

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:=


(* function composition *)
Definition comp A B C (f : B -> A) (g : C -> B) : C -> A
:=


(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* Introduce empty type, call `void` *)

Definition void_terminal (A : Type) :
  void -> A
:=


(* Introduce `unit` type (a type with exactly one canonical form) *)

Definition unit_initial (A : Type) :
  A -> unit
:=


(* Think of some more type signatures involving void, unit, sum, prod *)
