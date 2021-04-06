(*|
======================================================================================================================
Injectivity and disjointness of constructors, large elimination. Convoy pattern. Proofs by induction. `Prop` vs `Type`
======================================================================================================================

:Author: Anton Trunov
:Date: April 1, 2021


====================================================

|*)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*|
Injectivity of constructors
---------------------------
|*)

(*| Constructors of inductive types are injective
functions, i.e. if we have two equal term and
their head symbols are identical constructors,
then we can prove the constructor components are
(propositionally) equal. For example, let us prove
that if the successors of two natural numbers are
equal, then the numbers are equal themselves. |*)

Definition succ_inj (n m : nat) :
  n.+1 = m.+1 -> n = m
:=
  fun Sn_Sm : n.+1 = m.+1 =>
    match
      Sn_Sm in (_ = Sm)
      return (n = Sm.-1)
    with
    | erefl => erefl n
    end.

(*| Since we can only substitute `n.+1` with
`m.+1`, or, with notations unfolded, `S n` with `S
m`, we need to somehow remove the `S` constructor
after substitution, and this is what the
predecessor function does in the snippet above
(`Sm.-1`). |*)

(*| The same mode of reasoning can be applied to
prove, for instance, the `or_introl` constructor
is injective too. |*)

Definition or_introl_inj (A B : Prop) (p1 p2 : A) :
  or_introl p1 = or_introl p2 :> (A \/ B) ->
  p1 = p2
:=
  fun eq =>
    match
      eq in (_ = oil2)
      return (p1 =
              if oil2 is or_introl p2' then p2' else p2)
    with
    | erefl => erefl p1
    end.


(*|
Disjointness of constructors
----------------------------
|*)

(*| For constructors of inductive types living in
the `Type` universe, i.e. the computationally
relevant terms, we can prove that distinct
contructors are not propositionally equal. |*)

Definition false_eq_true_implies_False :
  false = true -> False
:=
  fun     eq :  false = true =>
    match eq in (_    = b)
             return (if b then False else True)
    with
    | erefl => I
    end.

(*| In the snippet above, we formulate the
`return` annotation in a way that ensures we still
prove:

- `False` outside the branch of the
  `match`-expression, because `b` unifies with
  `true` at that point;
- and `True` *inside* the branch. This time `b`
  unifies with `false`. It does not really matter
  if it's `True`, it can be any inhabited proposition.
|*)

(*|
Large elimination
-----------------
|*)

(*| Our prove of disjointness of `true` and
`false` crucially depends on the fact that we can
eliminate a term (`b`) and get a type (`False` or
`True` above) and not just a term, i.e. we get
something of type `Type`. This is called *large
elimination* and if a type theory does not have
this feature it's not possible to prove that
different constructors are not equal.

In Coq, the `Prop` universe drops this feature to
support classical reasoning. We are going to talk
about this a bit more later. |*)

Fail Definition or_introl_inj (A B : Prop) (p1 : A) (p2 : B) :
  or_introl p1 = or_intror p2 -> False
:=
  fun eq =>
    match
      eq in (_ = oil2)
      return (if oil2 is or_intror p2' then False else True)
    with
    | erefl => I
    end.


(*|
Convoy pattern
--------------
|*)

(*| As a preliminary definition let's prove
inequality is irreflexive, i.e. `x <> x -> False`: |*)

(*| First, we make a query on what `<>` means: |*)
Locate "<>".

Definition neq_irrefl A (x : A) :
  x <> x -> False
:=
  fun neq_xx : x = x -> False =>
    neq_xx erefl.

(*| Now we can try and prove that inequality is a
symmetric relation. The type `x <> y -> y <> x`
below means `(x = y -> False) -> y = x -> False`,
so the corresponding term is going to be a
function with two parameters and we are going to
start our first failing attempt by introducing two
parameters: |*)

Fail Definition neq_sym A (x y : A) :
  x <> y -> y <> x
:=
  fun neq_xy : x <> y =>
    fun eq_yx : y = x =>
      match
        eq_yx in (_ = a)
        return False
      with
      | erefl => _
      end.

(*| The problem here is that the `return`
annotation does not contain the index `a` anywhere
(it's just constant `False`), so unification of
`a` with `y` is not going to change anything.

To fix that, we need to pass `neq_xy` through the
`match`-expression, so that we can track the
relationship between the indices of the types of
`neq_xy` and `eq_yx`.

To prove our statement we need to somehow make the
`return` annotation depend on `a`, moreover we
need the type of `neq_xy`, i.e. `x <> y` to play a
role in it, because only then we can get a
contradiction. To do that we are going to have `x
<> y -> False` as our `return`-annotation (modulo
the fact we replace `x` with the corresponding `a`
variable). This means we need to return a function
inside the `match`-expression and to make the
whole expression typecheck, we apply the
`match`-expression to the term of type `x <> y`.

This pattern of re-typechecking a term with
already "pinned" type is usually called the
*convoy pattern*. |*)

Definition neq_sym A (x y : A) :
  x <> y -> y <> x
:=
  fun neq_xy : x <> y =>
    fun eq_yx : y = x =>
      (match
         eq_yx in (_ = a)
         return (a <> y -> False)
       with
       | erefl => fun neq_yy : y <> y => neq_yy erefl
       end) neq_xy.


(*|
Proofs by induction
-------------------
|*)

(*| Now, let's prove some lemmas about truly
inductive types like the `nat` type.

We are going to need a helper lemma `congr1`
expressing that unary functions are compatible
with the propositional equality, so `congr` here
means 'congruence'. |*)

Definition congr1 (A B : Type) :
  forall (f : A -> B) (x y : A),
    x = y -> f x = f y
:=
  fun f x y xy =>
    match
      xy in (_ = b)
         return (f x = f b)
    with
    | erefl => erefl (f x)
    end.

(*| Suppose we'd like to prove that zero is the
right identity w.r.t addition, i.e. `forall n, n +
0 = n`. If we start proving this statement as we
did before by introducing an anonymous function
which maps an arbitrary `n` to the proof of `n +
0` we will soon get stuck: |*)

Fail Definition addn0 :
  forall n : nat, n + 0 = n
:=
  fun (n : nat) =>
    match n as a return (a + 0 = a) with
    | O => erefl 0
    | S n' => congr1 S (_ : n' + 0 = n')
    end.

(*| The reason we got stuck here is that we lack a
proof the same lemma but for the predecessor of
`n`. Well, we can use recursion to get just that.
Here is a new successful attempt:
|*)

Definition addn0 :
  forall n : nat, n + 0 = n
:=
  fix rec (n : nat) : n + 0 = n :=
    match n return (n + 0 = n) with
    | O => erefl 0
    | S n' => congr1 S (rec n')
    end.

(*| Notice that the symmetric lemma does not
require recursion: |*)
Definition add0n :
  forall n : nat, 0 + n = n
:=
  fun n : nat => erefl n.

(*| This is because addition is defined by
recursion on its first parameter, so `0 + n` is
*definitionally* equal to `n`. |*)


(*|
Principle of Mathematical Induction
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)

(*| Usually, a lemma like `addn0` would be proven
using the principle of mathematical induction,
which we are going to formulate now. |*)

Definition nat_ind :
  forall (P : nat -> Prop),
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
:=
  fun P =>
  fun (p0 : P 0) =>
  fun (step : (forall n : nat, P n -> P n.+1)) =>
    fix rec (n : nat) :=
      match n return (P n) with
      | O => p0
      | S n' => step n' (rec n')
      end.

(*| `nat_ind` lets us abstract recursion away and
reduce proofs that require recursion to proving
two subgoals:

- we construct a term of type `P 0`, i.e. we prove
  our property `P` holds for the base case when
  `n` is equal to zero;
- we constructr a term of type
  `forall n : nat, P n -> P n.+1`, i.e. we do
  the inductive step and prove the property `P` holds
  for any successor `n.+1` under the assumption it
  holds for the current `n`.

In type theory induction is just recursion!
|*)


(*| Here is yet another way of proving `addn0`
where we factor out recursion and re-use
`nat_ind`: |*)

Definition addn0' :
  forall n : nat, n + 0 = n
:= @nat_ind
     (fun n => n + 0 = n)
     (erefl 0)
     (fun _ IHn => congr1 S IHn).

(*| In general a principle like `nat_ind` is
called a dependent eliminator (or recursor, or
recursion scheme) and it can have a more general
type like the following one (it's the same
definition as `nat_ind` but `Prop` is changed to
`Type` here, so we are not talking just about
proofs now): |*)

Definition nat_rect :
  forall (P : nat -> Type),
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
  := fun P
         (p0 : P 0)
         (step : (forall n : nat, P n -> P n.+1)) =>
       fix rec (n : nat) :=
       match n return (P n) with
       | O => p0
       | S n' => step n' (rec n')
       end.

(*| Recursors factor out recursion and `nat_rect`
can be used to implement e.g. the addition
function without using explicit recursion, i.e.
`fix`-combinator. |*)
Definition addn' : nat -> nat -> nat :=
  @nat_rect
    (fun _ => nat -> nat)
    id
    (fun _ pn => succn \o pn).

Check erefl : addn' 21 21 = 42.

(*| It can be proved that `addn` and `addn'` are
equivalent, i.e. `addn =2 addn'`, which means
`forall x y, addn x y = addn' x y` |*)

(*| These elimination principles for `Set`, `Prop`
and `Type` Coq generates for you automatically
when you define a new inductive type. Sometimes
those principles are not very useful but it's a
story for a different time.

To see that `nat_rect` is a strict generalization
of `nat_ind` you can try reimplementing the
`addn0'` lemma and the `addn'` function using
`nat_rect` and `nat_ind` respectively and see that
it's not possible to implement `addn'` via the
`nat_ind` principle. This is related to the issue
of large elimination we observed earlier. |*)

(*|
Dependent pairs in `Prop` and `Type`
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)

(*| Because of the issue of large elimination
mentioned above, Coq has a several dependent pair
types with components living in `Prop` or `Type`.
|*)

(*| We have the `ex` type we use to emulate the
existential quantifier. The type `ex` lives in the
`Prop` universe and it is computationally
irrelevant because of this. |*)
Print ex.

(*| There is the `sig` type to emulate elements of
a certain type for which certain property holds:
|*)
Print sig.
(*| Note that `{x : A | P x}` is a notation for
`sig P`. The type `sig` lives in `Type`, i.e.
terms of this type are computationally relevant
and are pairs of elements and proofs that a
certain property holds for these elements. Since
the `P` property is of type `A -> Prop`, it means
the proofs, i.e. the second components of those
pairs are computationally irrelevant and thus can
be ignored at run-time. |*)

(*| There is also the `sigT` type of dependent
pairs of which both components are computationally
relevant. |*)
Print sigT.
(*| Note that `{x : A & P x}` is a notation for
`sigT P`. |*)


(*|
.. code-block:: Coq

   Inductive ex (A : Type) (P : A -> Prop) : Prop :=
     ex_intro : forall x : A, P x -> exists y, P y

   Inductive sig (A : Type) (P : A -> Prop) : Type :=
     exist : forall x : A, P x -> {x : A | P x}

   Inductive sigT (A : Type) (P : A -> Type) : Type :=
     existT : forall x : A, P x -> {x : A & P x}

|*)


(*| Let us see how we can use the `sig` type now. |*)


(*|
Fun with the predecessor function
---------------------------------
|*)

(*| As we mentioned earlier there is a number of
ways we can implement the predecessor function on
the natural numbers. We chose to do it using the
default element but let's look at some other
approaches. |*)

(*| We are going to create a dependently typed version
and return a natural number if the predessor of a number is
defined and a term of type `unit` otherwise. |*)
Definition Pred n := if n is S n' then nat else unit.

Check erefl : Pred 0 = unit.
Check erefl : Pred 42 = nat.

(*| Here is out definition: |*)
Definition predn_dep : forall n, Pred n :=
  fun n => if n is S n' then n' else tt.

Check predn_dep 0 : unit.
Check predn_dep 7 : nat.

Check erefl : predn_dep 0 = tt.
Check erefl : predn_dep 7 = 6.
Fail Check erefl : predn_dep 0 = 0.


(*| Reminder: Type inference for dependent types
is undecidable. |*)
Fail Check (fun n => if n is S n' then n' else tt).


(*| We will talk about `ex`, `sig` and `sigT` in a
greater detail later on in this course. For now
let's just show one simple example for `sig` type.
Below, the notation `{x : T | P x}` stands for
`sig P`. Let's write yet another implementation of
our beloved predecessor function. |*)

Definition pred (n : {x : nat | x != 0}) : nat :=
  match n with
  | exist x proof_x_neq_0 => predn x
  end.

(*| To use `pred` function we must provide a
number and a proof that it's not a zero. |*)
Compute pred (exist (fun x => x != 0) 42 erefl).

(*| Notice that we provide the predicate
expressing that the input number is non-zero
explicitly. Actually, Coq can infer this predicate
if we ask to do it for us using an underscore: |*)
Check erefl : pred (exist _ 42 erefl) = 41.

(*| Let's try and see what happens if we use `ex`
instead of `sig` type |*)
Fail Definition pred_fail (n : exists x, x != 0) : nat :=
  match n with
  | ex_intro x proof_x_neq_0 => predn x
  end.
(*| The error message we get means that we cannot
use proofs to build data. And the reason behind
this exact restriction we will learn later in the
course. |*)
