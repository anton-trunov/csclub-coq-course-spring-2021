(*|
##############################################
 A compiler from expressions to stack machine
##############################################
|*)

(*|

.. contents:: Table of Contents

|*)

From Equations Require Import Equations.
From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify. (* lia *)
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*| By default, the ``Equations`` plugin makes definitions opaque to avoid
spurious unfoldings, but this behavior can be reverted using the following
option. |*)
Set Equations Transparent.

(*|
How to type Unicode notations in this file
|*)

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
   * - `⧐`
     - `\RightTriangleBar`
   * - `⊕`
     - `\oplus`
   * - `⊖`
     - `\ominus`
   * - `⊗`
     - `\otimes`
   * - `⟿`
     - `\longrightsquigarrow`
   * - `⊞`
     - `\boxplus`


|*)


(*|
*******************************
 Simple Arithmetic Expressions
******************************* |*)

Module ArithExpr.

(*|
Expressions
=========== |*)

(*|
Abstract Syntax Tree
-------------------- |*)

(*| Abstract Syntax Tree (AST) for arithmetic expressions: we support numerals
(`Const`) and three arithmetic operations: addition (represented with the `Plus`
constructor), truncating subtraction (`Minus`), multiplication (`Mult`). |*)

Inductive aexp : Type :=
| Const of nat
| Plus of aexp & aexp
| Minus of aexp & aexp
| Mult of aexp & aexp.

(*| QuickChick (see below) comes with a derivation mechanism for random
generators and conversion to strings for a wide class of inductive types. |*)
Derive (Arbitrary, Show) for aexp.

Implicit Types (e : aexp).


(*|
Notations
^^^^^^^^^ |*)

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
Check erefl : ⟦ ‴0 - 4‴ ⟧ = 0.
Check erefl : ⟦ ‴40 - 3 - 1‴ ⟧ = 36.
Check erefl : ⟦ ‴40 - (3 - 1)‴ ⟧ = 38.
Check erefl : ⟦ ‴2 + 2 * 2‴ ⟧ = 6.
Check erefl : ⟦ ‴(2 + 2) * 2‴ ⟧ = 8.
Check erefl : ⟦ ‴40 + 3 - 1‴ ⟧ = 42.


(*|
Simple Stack Machine
==================== |*)

(*|
Abstract Syntax for Simple Stack Machine
---------------------------------------- |*)

(*| The stack machine instructions: |*)
Inductive instr := Push (n : nat) | Add | Sub | Mul.


(*| QuickChick (see below) comes with a derivation mechanism for random
generators and conversion to strings for a wide class of inductive types. |*)
Derive (Arbitrary, Show) for instr.

(*| A program for our stack machine is simply a sequence of instructions: |*)
Definition prog := seq instr.

(*| The stack of our stack machine is represented as a list of natural numbers |*)
Definition stack := seq nat.

Implicit Types (p : prog) (s : stack).

Declare Scope stack_scope.
Delimit Scope stack_scope with S.

Notation "⧐ n" := (Push n)
  (at level 0, no associativity) : stack_scope.
Notation "⊕" := Add
  (at level 0, no associativity) : stack_scope.
Notation "⊖" := Sub
  (at level 0, no associativity) : stack_scope.
Notation "⊗" := Mul
  (at level 0, no associativity) : stack_scope.

Open Scope S.


(*|
Stack Programs Semantics
------------------------ |*)

Equations run p s : stack :=
  run (⧐ n :: p) s := run p (n :: s);
  run (⊕ :: p) (a1 :: a2 :: s) := run p ((a2 + a1) :: s);
  run (⊖ :: p) (a1 :: a2 :: s) := run p ((a2 - a1) :: s);
  run (⊗ :: p) (a1 :: a2 :: s) := run p ((a2 * a1) :: s);
  run (_ :: p) s := run p s;
  run _        s := s.

Arguments run : simpl nomatch.

(*| Unit and notation tests: |*)
Check erefl : run [:: ⧐ 21; ⧐ 21; ⊕] [::] = [:: 42].


(*|
Compiler from Simple Arithmetic Expressions to Stack Machine Language
===================================================================== |*)

Equations compile e : prog :=
  compile ‴#n‴ := [:: ⧐ n];
  compile ‴e1 + e2‴ := compile e1 ++ compile e2 ++ [:: ⊕];
  compile ‴e1 - e2‴ := compile e1 ++ compile e2 ++ [:: ⊖];
  compile ‴e1 ⋅ e2‴ := compile e1 ++ compile e2 ++ [:: ⊗].

Check erefl: run (compile ‴40 + 3 - 1‴) [::] = [:: 42].

(*|
Property-based randomized testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ |*)
(*
+++ Passed 10000 tests (0 discards)
*)

(*|
Compiler correctness: specification and first steps to prove it
--------------------------------------------------------------- |*)

(* TODO: maybe show the non-generalized version first *)


Theorem compile_correct e :
  run (compile e) [::] = [:: ⟦e⟧].
Proof.

(*|
Compiler is not very inefficient
-------------------------------- |*)

(*| Let us show the compiler does not produce very inefficient code: we are
going to assume that the measure of inefficiency in our case is the length of
the code the compiler produces. In our case the length of produced code should
not exceed the number of symbols (operations and constants) in the source
arithmetic expression. In fact, our compiler is efficient in a sense, for
instance, it does not add spurious instructions like `<some-code>; ⧐ 0; ⊕; ...`
but our specification so far does not ensure that. |*)

Equations nsymb (e : aexp) : nat :=
  nsymb ‴#n‴ := 1;
  nsymb ‴e1 + e2‴ := (nsymb e1 + nsymb e2).+1;
  nsymb ‴e1 - e2‴ := (nsymb e1 + nsymb e2).+1;
  nsymb ‴e1 ⋅ e2‴ := (nsymb e1 + nsymb e2).+1.

(*| First, let's check the property holds using QuickChick: |*)

QuickChick (fun e =>
  size (compile e) <= nsymb e).

Lemma compile_is_not_very_inefficient e :
  size (compile e) <= nsymb e.
Proof.
Admitted.

End ArithExpr.