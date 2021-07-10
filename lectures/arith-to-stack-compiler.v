From Coq Require Import Ascii String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Equations Require Import Equations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*|
How to type Unicode notations in this file
------------------------------------------ |*)

(*| To type Unicode notation you might want to use an editor with a LaTeX-like
input mode for Unicode. Emacs supports this out-of-the-box: `M-x
set-input-method` and then enter `TeX` in the prompt. VSCode has a plugin
`Unicode Latex <https://github.com/ojsheikh/unicode-latex>`_ which enables this
functionality. |*)

(*|

.. list-table::
   :widths: 25 25
   :header-rows: 1

   * - Unicode symbol
     - Input sequence
   * - `‴`
     - `\trprime`
   * - `⟦`
     - `\llbracket`
   * - `⟧`
     - `\rrbracket`
   * - `⋅`
     - `\cdot`

|*)


(*|
Expressions
----------- |*)
Module Expr.

(*|
Abstract Syntax Tree
==================== |*)

(*| Abstract Syntax Tree (AST) for arithmetic expressions: we support numerals
(`Const`) and three arithmetic operations: addition (represented with the `Plus`
constructor), truncating subtraction (`Minus`), multiplication (`Mult`). |*)

Inductive aexp : Type :=
| Const of nat
| Plus of aexp & aexp
| Minus of aexp & aexp
| Mult of aexp & aexp.

(*|
Notations
========= |*)

(*| This means we declare `expr` as an identifier referring to a 'notation
entry'. |*)
Declare Custom Entry expr.
Declare Scope expr_scope.
Delimit Scope expr_scope with E.

(*| We let the parser know `expr` is associated with triple quotation marks. |*)
Notation "‴ e ‴" := e%E (at level 0, e custom expr at level 99).

(* Number notation *)
(* parsing *)
Definition of_uint (u : Number.uint) : aexp :=
  Const (Nat.of_num_uint u).
Arguments of_uint u%dec_uint_scope.

(* printing *)
Definition to_uint (e : aexp) : option Number.uint :=
  if e is Const n then Some (Nat.to_num_uint n) else None.
Arguments to_uint e%E.

Number Notation aexp of_uint to_uint : expr_scope.

Notation "( x )" := x
  (in custom expr at level 0, x at level 99) : expr_scope.
Notation "x" := x
  (in custom expr at level 0, x constr at level 0) : expr_scope.
Notation "'#' x" := (Const x)
  (in custom expr at level 30, no associativity) : expr_scope.
Notation "x + y" := (Plus x y)
  (in custom expr at level 50, left associativity) : expr_scope.
Notation "x - y" := (Minus x y)
  (in custom expr at level 50, left associativity) : expr_scope.
Notation "x * y" := (Mult x y)
  (in custom expr at level 40, left associativity) : expr_scope.
(* Unicode notation for mutliplication, just for fun *)
Notation "x ⋅ y" := (Mult x y)
  (in custom expr at level 40, left associativity) : expr_scope.

(*|
Evaluator
========= |*)
Section Evaluator.

(*| Computable big-step semantics for arithmetic expressions: |*)
Equations aeval (e : aexp) : nat :=
  aeval ‴#n‴ => n;
  aeval ‴e1 + e2‴ => aeval e1 + aeval e2;
  aeval ‴e1 - e2‴ => aeval e1 - aeval e2;
  aeval ‴e1 ⋅ e2‴ => aeval e1 * aeval e2.

End Evaluator.

(*| The usual Oxford brackets notation for the evaluator: |*)
Notation "⟦ e ⟧" := (aeval e) (at level 30, no associativity).

(*| Unit and notation tests: |*)
Check erefl : ⟦ ‴40 - 3 - 1‴ ⟧ = 36.
Check erefl : ⟦ ‴40 - (3 - 1)‴ ⟧ = 38.
Check erefl : ⟦ ‴2 + 2 * 2‴ ⟧ = 6.
Check erefl : ⟦ ‴(2 + 2) * 2‴ ⟧ = 8.
End Expr.


(*| A test |*)
Import Expr.
Check erefl : ⟦ ‴40 + 3 - 1‴ ⟧ = 42.
