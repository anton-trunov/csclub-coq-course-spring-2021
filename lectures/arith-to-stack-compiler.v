(*|
##############################################
 A compiler from expressions to stack machine
##############################################
|*)

(*|

.. contents:: Table of Contents

|*)

(*|
How to install dependencies for this file:

``$ opam install coq-mathcomp-ssreflect coq-mathcomp-zify coq-equations coq-quickchick coq-deriving``

|*)


From Equations Require Import Equations.
From QuickChick Require Import QuickChick.
Import GenLow GenHigh.
From deriving Require Import deriving.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import zify.
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

(* TODO: prefix instructions with `I` *)

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
  run _ s := s.

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
Compiler correctness: specification and first steps to prove it
--------------------------------------------------------------- |*)

(* TODO: maybe show the non-generalized version first *)

Lemma compile_correct_generalized e s :
  run (compile e) s = ⟦e⟧ :: s.
Proof.
elim: e s => //= e1 IH1 e2 IH2 s.
(* At this point we might be looking for a way to utilize the induction
hypotheses we just got. A lemma like ``run (p1 ++ p2) s = run p2 (run p1 s)``
might seem intuitive, but before trying to prove it, let's see if we can get a
counter-example using property-based randomized testing. *)
Abort.


(*|
Property-based randomized testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ |*)

Definition cat_run'_prop p1 p2 s :=
  run (p1 ++ p2) s == run p2 (run p1 s).

QuickChick cat_run'_prop.
(*
[Sub]
[Push 0]
[]
*** Failed after 9 tests and 2 shrinks. (0 discards)
*)

(*| We got a counter-example right away! |*)

(* We have several design choices here: either the stack-machine interpreter
should signal a failure or we could add a typechecker for our stack language.
Let's go with the latter approach. *)


(*|
Typed stack programs
-------------------- |*)

(* The type of a stack instruction / program *)
Record stype : Type :=
  mk_type {
      (* min number of stack elements that needs be to present on the stack so
      there is always a sufficient number of elements to proceed with
      computation *)
      inp : nat;
      (* the number of elements the stack program produces overall *)
      out : nat;
    }.
(* TODO: better names (notations?) for `inp` and `out` *)

Implicit Type t : stype.

Notation "i ⟿ o" := (mk_type i o) (at level 65, no associativity) : stack_scope.

(*| The types of the stack instructions |*)
Definition instr_type (i : instr) : stype :=
  match i with
  | ⧐ n => 0⟿1
  | ⊕ | ⊖ | ⊗ => 2⟿1
  end.

(* combine (add) types of two consequtive instructions / programs *)
(* Intuitively, `addst` is supposed to be a monoidial operation, see below *)
Definition addst t1 t2 : stype :=
  let: i1 ⟿ o1 := t1 in
  let: i2 ⟿ o2 := t2 in
  i1 + (i2 - o1) ⟿ o2 + (o1 - i2).

Arguments addst : simpl nomatch.

(* Nullary notation *)
Notation "(⊞)" := (addst) : fun_scope.
(* Binary infix notation *)
Notation "s ⊞ t" := (addst s t) (at level 50, left associativity) : stack_scope.

Lemma addtA : associative addst.
Proof. case=> i1 o1 [i2 o2] [i3 o3] /=; congr mk_type; lia. Qed.

Lemma add0t : left_id (0⟿0) addst.
Proof. by case=> i o; rewrite /addst subn0 add0n sub0n addn0. Qed.

Lemma addt0 : right_id (0⟿0) addst.
Proof. by case=> i o; rewrite /addst subn0 add0n sub0n addn0. Qed.

Lemma inpE t i o : inp ((i⟿o) ⊞ t) = i + (inp t - o).
Proof. by case: t=> it ot /=. Qed.

Definition infer (p : prog) : stype :=
  foldr (fun i t => instr_type i ⊞ t) (0 ⟿ 0) p.

Check erefl : infer [:: ⊖; ⊗] = 3⟿1.

Lemma infer_cat : {morph infer : x y / x ++ y >-> x ⊞ y}.
Proof.
elim=> [[|i2 p2]| i1 p1 IHp1 p2] //=; first by rewrite add0t.
by rewrite IHp1 addtA.
Qed.

(*| ``compile`` produces type-correct programs which do not consume any stack
and put exactly one output value on the stack |*)
Lemma infer_compile e :
  infer (compile e) = 0⟿1.
Proof.
by elim: e => //= e1 IHe1 e2 IHe2; rewrite !infer_cat IHe1 IHe2.
Qed.

(*|
Back to property based testing
------------------------------ |*)

(*| Using boolean implication, we can filter out incorrect stack programs when
doing property based testing, let's also see some statistics showing how
(in)efficient this is. |*)

Definition cat_run''_prop (p1 p2 : prog) (s : stack) :=
  (inp (infer p1) <= size s) ==>
  (run (p1 ++ p2) s == run p2 (run p1 s)).

Extract Constant defNumTests => "10000".
QuickChick (fun p1 p2 s =>
  implication
    (inp (infer p1) <= size s)
    (run (p1 ++ p2) s == run p2 (run p1 s))).
(* +++ Passed 10000 tests (1583 discards) *)

(*| This is how one changes the number of QuickChick tests. |*)

Extract Constant defNumTests => "11600".
QuickChick (fun p1 p2 s =>
  collect
    (inp (infer p1) <= size s)
    ((inp (infer p1) <= size s) ==> (run (p1 ++ p2) s == run p2 (run p1 s)))).
(*
7544 : true
4056 : false
+++ Passed 11600 tests (0 discards)
*)

(* TODO: check the semantics of ``implication`` -- the results of
``implication`` and ``collect`` are not in correspondence. Reported here:
https://github.com/QuickChick/QuickChick/issues/228. *)

(* TODO: show how to build a random generator producing type-correct stack programs *)



(*|
Finishing proofs of compiler correctness
---------------------------------------- |*)

Lemma run_cat p1 p2 s :
  inp (infer p1) <= size s ->
  run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
elim: p1 s => // i1 p1 IHp1 s; case: i1=> [n | | |] /=.
- rewrite inpE add0n=> Typ; rewrite IHp1 //=; lia.
- rewrite inpE; case: s=> // e1 [//|e2 s /= T]; rewrite IHp1 //=; lia.
- rewrite inpE; case: s=> // e1 [//|e2 s /= T]; rewrite IHp1 //=; lia.
rewrite inpE; case: s=> // e1 [//|e2 s /= T]; rewrite IHp1 //=; lia.
Qed.

Lemma compile_correct_generalized e s :
  run (compile e) s = ⟦e⟧ :: s.
Proof.
by elim: e s => //= e1 IH1 e2 IH2 s; rewrite !run_cat ?infer_compile // IH1 IH2.
Qed.

(*| The final correctness theorem |*)
Lemma compile_correct e :
  run (compile e) [::] = [:: ⟦e⟧].
Proof. exact: compile_correct_generalized. Qed.


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
Proof. elim: e=> //= e1 IH1 e2 IH2; rewrite !size_cat /=; lia. Qed.

End ArithExpr.



(*|
************************************
 Boolean and Arithmetic Expressions
************************************ |*)

Module BoolArithExpr.

(* Improving derived generator:
https://github.com/QuickChick/QuickChick/issues/229 *)
Inductive binop : Type :=
| Plus
| Minus
| Mult
| And
| Or
| Eq
| Leq.
Derive (Arbitrary, Show) for binop.
(* TODO See if introducing `binop` simplifies some repetetive proofs *)

Inductive exp : Type :=
| Num of nat
| True
| False
| Neg of exp
| BinOp of binop & exp & exp
| If of exp & exp & exp.

(* TODO notations for expressions *)

Derive (Arbitrary, Show) for exp.
Implicit Type e : exp.

(*| The type of values |*)

Inductive val : Type :=
| Nat of nat
| Bool of bool.
Derive (Arbitrary, Show) for val.
Implicit Type v : val.

(*| Derive an instance of decidable equality structure using the *deriving*
package. |*)
Definition val_indDef := [indDef for val_rect].
Canonical val_indType := IndType val val_indDef.
Definition val_eqMixin := [derive eqMixin for val].
Canonical val_eqType := EqType val val_eqMixin.

(*|
Evaluator
========= |*)

Section Evaluator.

(* TODO see if these "v-operations" can be made prettier *)
Definition addv v1 v2 :=
  match v1, v2 with
  | Nat n1, Nat n2 => Nat (n1 + n2)
  | _, _ => Nat 0
  end.

Definition subv v1 v2 :=
  match v1, v2 with
  | Nat n1, Nat n2 => Nat (n1 - n2)
  | _, _ => Nat 0
  end.

Definition mulv v1 v2 :=
  match v1, v2 with
  | Nat n1, Nat n2 => Nat (n1 * n2)
  | _, _ => Nat 0
  end.

Definition andv v1 v2 :=
  match v1, v2 with
  | Bool b1, Bool b2 => Bool (b1 && b2)
  | _, _ => Bool false
  end.

Definition orv v1 v2 :=
  match v1, v2 with
  | Bool b1, Bool b2 => Bool (b1 || b2)
  | _, _ => Bool false
  end.

Definition negv v :=
  match v with
  | Bool b => Bool (~~ b)
  | _ => Bool false
  end.

Definition leqv v1 v2 :=
  match v1, v2 with
  | Nat n1, Nat n2 => Bool (n1 <= n2)
  | _, _ => Bool false
  end.

Definition gtv v1 v2 :=
  match v1, v2 with
  | Nat n1, Nat n2 => Bool (n1 > n2)
  | _, _ => Bool false
  end.

Definition ifv condv thenv elsev :=
  match condv with
  | Bool true => thenv
  | Bool false => elsev
  | _ => Bool false
  end.


(*| Computable big-step semantics for arithmetic expressions: |*)
Equations eval (e : exp) : val :=
  eval (Num n) := Nat n;
  eval (BinOp Plus e1 e2) := addv (eval e1) (eval e2);
  eval (BinOp Minus e1 e2) := subv (eval e1) (eval e2);
  eval (BinOp Mult e1 e2) := mulv (eval e1) (eval e2);
  eval True := Bool true;
  eval False := Bool false;
  eval (BinOp And e1 e2) := andv (eval e1) (eval e2);
  eval (BinOp Or e1 e2) := orv (eval e1) (eval e2);
  eval (Neg e) := negv (eval e);
  eval (BinOp Eq e1 e2) := Bool (eval e1 == eval e2); (* polymorphic equality *)
  eval (BinOp Leq e1 e2) := leqv (eval e1) (eval e2);
  eval (If cond then_ else_) := ifv (eval cond) (eval then_) (eval else_).

End Evaluator.

(*| The usual Oxford brackets notation for the evaluator: |*)
Notation "⟦ e ⟧" := (eval e) (at level 30, no associativity).

(*| Unit and notation tests: |*)
(* Check erefl : ⟦ ‴0 - 4‴ ⟧ = 0. *)
(* Check erefl : ⟦ ‴40 - 3 - 1‴ ⟧ = 36. *)
(* Check erefl : ⟦ ‴40 - (3 - 1)‴ ⟧ = 38. *)
(* Check erefl : ⟦ ‴2 + 2 * 2‴ ⟧ = 6. *)
(* Check erefl : ⟦ ‴(2 + 2) * 2‴ ⟧ = 8. *)
(* Check erefl : ⟦ ‴40 + 3 - 1‴ ⟧ = 42. *)



(*| The stack machine instructions: |*)

(* TODO think about representing all types as numbers in the stack machine *)

Inductive instr : Type :=
| IPush of val | IPop
| IAdd | ISub | IMul | IEq | INeq | ILeq | IGt
| ISkip (offset : nat) | ISkipIf (condition : bool) (offset : nat).
Derive (Arbitrary, Show) for instr.

Definition prog := seq instr.
Definition stack := seq val.
Implicit Types (p : prog) (s : stack).

(* TODO: switch to fold? *)
Equations run p s : stack :=
  run (IPush v :: p) s := run p (v :: s);
  run (IPop :: p) (_ :: s) := run p s;
  run (IAdd :: p) (x :: y :: s) := run p (addv y x :: s);
  run (ISub :: p) (x :: y :: s) := run p (subv y x :: s);
  run (IMul :: p) (x :: y :: s) := run p (mulv y x :: s);
  run (IEq :: p) (x :: y :: s) := run p (Bool (y == x) :: s);
  run (INeq :: p) (x :: y :: s) := run p (Bool (y != x) :: s);
  run (ILeq :: p) (x :: y :: s) := run p (leqv y x :: s);
  run (IGt :: p) (x :: y :: s) := run p (gtv y x :: s);
  run (ISkip n :: p) s := run (drop n p) s;
  run (ISkipIf true n :: p) (Bool true :: s) := run (drop n p) (Bool true :: s);
  run (ISkipIf true n :: p) (Bool false :: s) := run p (Bool false :: s);
  run (ISkipIf false n :: p) (Bool false :: s) := run (drop n p) (Bool false :: s);
  run (ISkipIf false n :: p) (Bool true :: s) := run p (Bool true :: s);
  run _ s := s.

Equations compile e (positive : bool) : prog :=
  compile (Num n) pos := [:: IPush (Nat n)];
  compile (BinOp Plus e1 e2) pos := compile e1 pos ++ compile e2 pos ++ [:: IAdd];
  compile (BinOp Minus e1 e2) pos := compile e1 pos ++ compile e2 pos ++ [:: ISub];
  compile (BinOp Mult e1 e2) pos := compile e1 pos ++ compile e2 pos ++ [:: IMul];
  compile True pos := [:: IPush (Bool pos)];
  compile False pos := [:: IPush (Bool (~~ pos))];
  (* short-circuiting boolean and *)
  compile (BinOp And e1 e2) pos :=
    (* if pos is false then this basically transforms
       `~~ (x && y)` into `~~x || ~~y` *)
    let: p2 := compile e2 pos in
    compile e1 pos ++ (ISkipIf (~~ pos) (size p2).+1) :: IPop :: p2;
  (* short-circuiting boolean or *)
  compile (BinOp Or e1 e2) pos :=
    let: p2 := compile e2 pos in
    compile e1 pos ++ (ISkipIf pos ((size p2).+1) :: IPop :: p2);
  (* transform the expression to Negation Normal Form (NNF) to cut down on
     the number of occurences of the negation instruction *)
  compile (Neg e) pos := compile e (~~ pos);
  (* polymorphic equality *)
  compile (BinOp Eq e1 e2) pos :=
    compile e1 pos ++ compile e2 pos ++ [:: if pos then IEq else INeq];
  compile (BinOp Leq e1 e2) pos :=
    compile e1 pos ++ compile e2 pos ++ [:: if pos then ILeq else IGt];
  compile (If cond then_ else_) pos :=
    let: pthen := compile then_ pos in
    let: pelse := compile else_ pos in
    compile cond true ++
    ISkipIf false (size pthen).+2 :: IPop :: pthen ++ ISkip ((size pelse).+1)
    :: IPop :: pelse.

(* This one definitely needs at least testing :) *)


(*| Before we can start testing / proving our implementation, we need to rule out
malformed expressions: we cannot make any promise about compiler correctness for
meaningless terms. |*)

Inductive typ : Type := TNat | TBool.
Implicit Type (ty : typ).
Definition typ_indDef := [indDef for typ_rect].
Canonical typ_indType := IndType typ typ_indDef.
Definition typ_eqMixin := [derive eqMixin for typ].
Canonical typ_eqType := EqType typ typ_eqMixin.

Definition combine_typs oty1 oty2 : option typ :=
  match oty1, oty2 with
  | Some ty1, Some ty2 => if ty1 == ty2 then Some ty1 else None
  | _, _ => None
  end.

Definition expected_typ oty expected : option typ :=
  match oty with
  | Some ty => if ty == expected then Some ty else None
  | _ => None
  end.

Notation "ty1 ⩲ ty2 ≡ 'any'" :=
  (combine_typs ty1 ty2) (at level 50, no associativity).

Notation "ty1 ⩲ ty2 ≡ expected" :=
  (expected_typ (combine_typs ty1 ty2) expected) (at level 50, no associativity).

(* TODO Maybe use monadic syntax here? And also improve performance (e.g. no
need to typecheck both subexpressions of a binary operation if one of them is
already ill-typed) *)
Fixpoint infer (e : exp) : option typ :=
  match e with
  | Num _ => Some TNat
  | True | False => Some TBool
  | BinOp Plus e1 e2 | BinOp Minus e1 e2 | BinOp Mult e1 e2 =>
      infer e1 ⩲ infer e2 ≡ TNat
  | BinOp And e1 e2 | BinOp Or e1 e2 =>
      infer e1 ⩲ infer e2 ≡ TBool
  | Neg e => infer e ⩲ (Some TBool) ≡ any
  | BinOp Eq e1 e2 =>
      omap (fun=> TBool) (infer e1 ⩲ infer e2 ≡ any)
  | BinOp Leq e1 e2 =>
      omap (fun=> TBool) (infer e1 ⩲ infer e2 ≡ TNat)
  | If cond then_ else_ =>
      if infer cond is Some TBool then
        infer then_ ⩲ infer else_ ≡ any
      else None
  end.


(* TODO Prove `infer` is complete and sound. E.g. if it is incomplete we might
be ruling out correct terms from consideration. *)


(*| Let's test the quality of our expression generator |*)
Extract Constant defNumTests => "10000".
Time QuickChick (fun e =>
  collect
    (isSome (infer e))
    true).
(*
6836 : true
3164 : false
+++ Passed 10000 tests (0 discards)
*)

(*| The 2:1 ratio between well-typed and ill-typed expressions does not look too
bad. |*)

(*| `resize 10` is a workaround, see
https://github.com/QuickChick/QuickChick/issues/228 |*)
Time QuickChick (resize 10 (checker (fun e =>
  implication
    (isSome (infer e))
    ([:: ⟦ e ⟧] == run (compile e true) [::])))).

(* TODO: we can write type-directed random generator to make testing more efficient.
   Observation: it's actually is not that bad in our simple case.
   Maybe we could skip this and do it only if there is extra time,
   or as a project/exercise *)


(* TODO Prove the correctness of the compiler *)

(* TODO add more sections / subsections *)
End BoolArithExpr.


(* TODO Expressions with partial operations *)


(*
 TODO Expressions with variables
 TODO Constant folding for expressions with variables

 Show constant folding is
  - sound (preserves expression's value);
  - complete (i.e. idempotent, a.k.a `f (f x) = f x`);
  - an optimization (results in less computation when compiled).
 *)


(* TODO Extraction

 - generate verified parser from e.g. Menhir or check if this can be done
using CoStar (https://dl.acm.org/doi/pdf/10.1145/3453483.3454053 /
https://github.com/slasser/CoStar)
 - run extracted code in the browser
 *)
