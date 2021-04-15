From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.


(*
Use your solution of Homework 2 and prove correctness of your implementations.
I'm repeating some (partial) definitions here just to make sure
the lemma statements make sense.
*)

(* A language of arithmetic expression *)
Inductive expr : Type :=
| Const of nat
| Plus of expr & expr
| Minus of expr & expr
| Mult of expr & expr.

Fixpoint eval (e : expr) : nat :=
  replace_with_your_solution_here.



(* Stack language *)
Inductive instr := Push (n : nat) | Add | Sub | Mul.

Definition prog := seq instr.
Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  replace_with_your_solution_here.


(* Compiler from the expression language to the stack language *)
Fixpoint compile (e : expr) : prog :=
  replace_with_your_solution_here.


(** Here is a correctness theorem for the compiler: it preserves the
meaning of programs. By "meaning", in this case, we just mean the final
answer computed by the program. For a high-level expression, the answer
is the result of calling [eval]. For stack programs, the answer
is whatever [run] leaves on the top of the stack. The correctness
theorem states that these answers are the same for an expression and
the corresponding compiled program. *)
Theorem compile_correct e :
  run (compile e) [::] = [:: eval e].
Proof.
Admitted.


(* ==== OPTIONAL part: decompiler ==== *)

Definition decompile (p : prog) : option expr :=
  replace_with_your_solution_here.

(** Prove [decompile] cancels [compile]. *)
Lemma decompile_compile e :
  decompile (compile e) = Some e.
Proof.
Admitted.

(* Prove the [compile] function is injective *)
Lemma compile_inj :
  injective compile.
Proof.
Admitted.

