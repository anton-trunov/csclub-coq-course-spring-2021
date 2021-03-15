(*|
=============================================
The basics of Coq and how to interact with it
=============================================

:Author: Anton Trunov
:Date: March 11, 2021


============================================================

|*)


(*|
Simple types and functions
--------------------------

Let's start making ourselves a system to work in using the few primitives Coq has built-in.

Import some very basic facilities of the Mathcomp library:
|*)
From mathcomp Require Import ssreflect.

(*|
We introduce the following definitions inside a new module
to avoid name clashes with the standard library later.
|*)
Module My.

(*|
Simple types
============
|*)

(*|
The `Inductive` *vernacular* is used to introduce a new type into Coq.
Let's introduce a useful Boolean type with two *constructors*:
|*)
Inductive bool : Type :=
| true
| false.

(*| `Type` is a primitive and its meaning for now is 'the type of all types',
or as sometimes they say 'the universe of types'. |*)
Check false : bool.
Check false.

(*| Now that we have a base type to work with, we can form a new type using the
functional arrow (`->`) type constructor. |*)
Check (bool -> bool) : Type.

(*| Here is an example of a simply-typed anonymous function: |*)
Check (fun b : bool => b).

(*| It is possible to elide the type annotation for the parameter in the above
example, however, in this case Coq's output will contain the so-called
*existential variable* `?T` which is a meta-language feature roughly meaning
"some type `?T` which should be inferrable somehow from the context": |*)
Check fun b => b.

(*| For instance, in the following snipet `?T` is determined to be `bool`
because we apply the unannotated identity function to a Boolean argument: |*)
Check (fun b => b) true.

(*| Now, let's move on and see an example of a higher-order function and its
corresponding type: |*)
Check fun (f : bool -> bool) => f true.

(*| We can ask Coq to calculate for us too *)
Compute (fun b => b) true.


(*|
Definitions
===========
|*)

(*| Of course, there are means to introduce new definitions. By the way,
definitions are not part of Coq's core type theory, it's a meta-linguistic
feature. However, there is interaction between some language features, like
*universe levels*, (which we are going to talk about later in the course) and
definitions.

So, here is the definition of the Boolean identity function: |*)

Definition idb := fun b : bool => b.

(*| As with terms we can typecheck definitions, compute with them, etc. |*)
Check idb.
Check (fun (f : bool -> bool) => f true) idb.
Compute idb false.

(*| The `Fail` vernacular command allows us to assert failure like so: |*)
Fail Check (fun (f : bool -> bool) => f true) false.
(*| By the way, `Fail` is compositional: to express that something is failing
to fail (as expected) one just says: `Fail Fail <something>.` |*)

(*|
Pattern matching (elimination)
==============================
|*)

(*| This time let's write the Boolean negation function because this time it
really has to use or, in other words, *eliminate* its parameter: |*)

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(*| Let's see `negb`'s type: |*)
Check negb.

(*| And we can make sure `negb` does that is intended: |*)
Compute negb false.
Compute negb true.

(*| Hooray, we just kind of proved `negb` works as expected by checking
exhaustively its specification we never wrote down explicitly. |*)

(*| Here is a sequence of reductions of different kinds that happen to arrive at
the result of the last of the two computations above:

.. code-block:: Coq

   negb true

   ~~>δ

   (fun (b : bool) => match b with | true => false | false => true end) true

   ~~>β

   match true with | true => false | false => true end

   ~~>ι

   false

- :math:`\delta`-reduction: unfolding of transparent constants;
- :math:`\beta`-reduction: substitution of the function argument into its body;
- :math:`\iota`-reduction: (1) matching a term agains patterns and calculating
  the corresponding branch with the right substitution for the bound variables,
  (2) reduction of the `fix` and `cofix` primitives that allow one to express recursion and co-recursion (we'll cover recursion soon but co-recursion is going to be out of scope of the course).
|*)

(*| It's possible to replicate the above steps using the `Eval` vernacular
command, of which `Compute` is simply a special case. In what follows, `cbv`
stands for 'call-by-value' and is one of the supported reduction strategies. |*)
Eval cbv delta in negb true.

Eval cbv beta delta in negb true.

Eval cbv beta delta iota in negb true.
(*| Notice that the order of reduction strategies we allow `Eval` to employ is
not important. |*)


(*|
Symbolic computation
====================
|*)

(*| Let's declare a variable `c` which, in contrast with definitions, does not
have a body (please ignore the warning for the moment): |*)
Variable c : bool.

(*| This may come as a surprise but we can compute with variables. |*)
Compute idb c.
(*| Notice the symbol `c` blocks reductions at the :math:`\iota`-reduction
step because it's not a value consisting of constructors -- in other words this
is not a *canonical form* -- hence we cannot expect reduction to go through: |*)
Compute negb c.

(*| We are going to work a lot with mixed concrete/symbolic expressions in our
proofs and it is important to understand their behavior under reduction. For
example, consider the following two definitions of the Boolean conjunction
function. The first function, named `andb`, does pattern-matching on its first
parameter and the second one, named `andb'` does that for its second parameter
instead: |*)
Definition andb (b c : bool) : bool :=
  match b with
  | false => false
  | true => c
  end.

Definition andb' (b c : bool) : bool :=
  match c with
  | false => false
  | true => b
  end.

(*| The `andb` and `andb'` functions are *extensionally* the same, i.e.
these functions have equal outputs for the corresponding equal inputs (formally:
:math:`\forall b\ c.\ andb\ b\ c = andb'\ b\ c`), but that only works for
concrete inputs. Observe the differences in their behavior on symbolic inputs:
|*)
Compute andb  c true.
Compute andb' c true.

Compute andb  c false.
Compute andb' c false.

Compute andb  false c.
Compute andb' false c.


(*|
Inductive types and recursive functions
=======================================
|*)

(*| We are going to define the type of unary natural numbers also known as
'Peano numbers' -- our first truly inductive type. A natural number is either a
zero (`O` below resembles zero graphically), or a successor (`S`) of another
natural number. |*)
Inductive nat : Type :=
| O
| S of nat.

(*| Notice that Coq prints back the `nat` type using an alternative syntax: |*)
Print nat.

(*| Here are the representations of several first natural numbers: 0, 1, 2, 3
correspondingly: |*)
Check O.
Check S O.
Check S (S O).
Check S (S (S O)).

(*| The unary representation is very inefficient computationally but very
convenient for proving. This convenience makes the unary numbers ubiquitous in
proofs and hence there is special notational support which lets us write 0, 1,
2, 3, etc. instead of the terms above. We can get that support once we close the
`My` module and start reusing the standard definition. |*)

(*| Let's implement some basic arithmetic functions and start with the
incrementing function that adds one to its argument. |*)
Definition succn := S.

(*| Of course, we can :math:`\eta`-expand the function and write it as
`Definition succn n := S n.` |*)

(*| Here is a simple unit-test: |*)
Compute succn (S (S O)).

(*|
Totality
^^^^^^^^
|*)
(*| Now, let's go for the predecessor function:

.. code-block:: Coq

   Definition predn (n : nat) : nat :=
     match n with
     | S x => x
     | O => _ (* what do we return here? *)
     end.

Coq being a total language does not allow us to, for instance,
throw an exception here -- we *have to* produce a term of type `nat` here.

So, let's take a step back and see what our options for implementing
the predecessor functions are.

- `pred : nat -> nat` -- in this case we need to provide a default value
  (`0` is a natural choice);
- `pred : nat -> option nat` -- use an optional type to signal a missing value;
- `pred : forall n : nat, (n <> 0) -> nat` -- pass a precondition `n <> 0` to
  have *static* guarantees the function is never called with the wrong argument.

The first option usually works best in practice, hence our final definition of
the predecessor function is as follows.
|*)
Definition predn (n : nat) : nat :=
  match n with
  | S x => x
  | O => O
  end.
(*| The same reasoning applies to the division function in case of division by
zero -- we simply return zero in that case. Contrary to what one can read
sometimes about this solution, it's not going to make our logic inconsistent or
anything like that. It just means we will have add some preconditions to some of
our lemmas. We will see it later in the course. |*)

(*|
Recursion
^^^^^^^^^
|*)
(*| Here goes our first recursive function: addition on natural numbers. |*)
Fixpoint addn (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => S (addn n' m)
  end.
(*| First, let's check that :math:`2 + 2 = 4`: |*)
Compute addn (S (S O)) (S (S O)).

(*| Here we use the `Fixpoint` vernacular command instead of `Definition` to
indicate we are going to use recursion here. Also, notice the `{struct n}`
annotation that tells Coq which parameter we are going to do recursion on. |*)

(*| An alternative idiomatic way to write the `addn` function would be |*)
Fixpoint addn_idiomatic (n m : nat) : nat :=
  if n is S n' then S (addn_idiomatic n' m) else m.
(*| Here we elide the `struct` annotation because Coq infer it in most cases
(but not always!) and use an alternative syntax for pattern-matching on data
types with two constructors of only one can carry information. Notice that
Coq's pretty-printer does not respect this syntactic sugar: try printing
`addn_idiomatic`. |*)

(*| In fact, `Fixpoint` provides some syntactic sugar but it's still a
`Definition` and a new primitive we haven't seen yet under the hood: `fix`. The
`fix` primitive is a fixed-point combinator one can use to write recursive
functions. If you do `Print addn.` you'll see it. So let's define `addn` in
terms of those primitive things: |*)

Definition addn_no_sugar :=
  fix addn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.
(*| Observe that the `addn` identifier after the `fix` keyword is the name we
are supposed to use for recursive calls and it does not have to have anything
related to the identifier in the definition. |*)


(*| Here is yet another alternative implementation but this time we do recursion
on the second parameter |*)
Fixpoint addn' (n m : nat) {struct m} :=
  if m is S m' then S (addn' n m') else n.

(*| As we metioned before, `addn` and `addn'` exhibit different behavior
when calculating with symbolic variables: |*)
Variable z : nat.
Compute addn  O z.
Compute addn' O z.
(*| Later we can prove these functions are equivalent but not the same and this
would show in proofs, making interactive proving less intuitive endeavor than
e.g. regular math. This is in line with the issue of dependent types being not
exactly modular. |*)

(*| One more point before we move on: suppose we made a mistake and called
`addn` on its input parameter and not on its predecessor. In this case
we are going to see an error message from the termination checker preventing us
from using an erroneous definition: |*)
Fail Fixpoint addn_loop (n m : nat) {struct n} : nat :=
  if n is S _ then S (addn_loop n m) else m.

(*|
Mutual Recursion
^^^^^^^^^^^^^^^^
|*)

(*| Here is a classical example of mutual recursion. To introduce one more
mutually recursive function connect use the `with` keyword as follows. |*)
Fixpoint is_even (n : nat) : bool :=
  if n is S n' then is_odd n' else true
with is_odd n :=
  if n is S n' then is_even n' else false.

(*| Our namespace is enriched with both `is_even` and `is_odd` identifiers: |*)
Compute is_even (S (S (S O))).
Compute is_even (S (S O)).
Compute is_odd (S (S (S O))).
Compute is_odd (S (S O)).

End My.

(*| After closing a module, the entities defined in it get prefixed with the
module's name |*)
Check My.nat.
Check My.addn.

(*| Now we can abandon our definitions and switch to the ones defined in
Mathcomp. For that purpose we import the `ssrbool` and `ssrnat` libraries which
contain definitions and proofs (!) about Booleans and natural numbers. |*)

From mathcomp Require Import ssrbool ssrnat.
(*| This import will generate a ton of warnings telling us that some standard
notations of Coq are redefined by Mathcomp. Let's ignore this for now. This
warning can be silenced with `Set Warnings "-notation-overridden".` command
placed right before the imports, or this can be done globally at a project
level. For a "portable" way to do that see
https://github.com/coq-community/lemma-overloading/blob/master/_CoqProject#L3.
|*)

(*| We have now access to standard boolean functions, e.g. here is how exclusive
disjunction (xor) is implemented in the standard library: |*)
Print addb.
(*| It's called `addb` because it is essentially addition modulo 2. |*)

(*| Some interactive queries that helps us explore libraries:
`About` tells you more than `Check` usually: |*)
About nat.
About S.

(*| We have some syntactic sugar like `42` but internally this a pile of 42
`S`'s ending with `O` |*)
Check 42.
(*| Coq displays this back to us as `3` |*)
Check S (S (S O)).

(*| This decimal notation does not work for `My.nat` because it is only
associated with the standard `nat` type. It's possible to implement decimal
notations for our own types but we are not going to discuss it. |*)

(*| Coq lets us control what we see when we do queries.
E.g. here is how to switch off all the syntactic sugar: |*)
Set Printing All.
Check 5 + 4.
Unset Printing All.

(*| To find out what unfamiliar notations mean you can use the `Locate`
vernacular command, although sometimes it can be tricky to understand what is part of the notation and what is not. |*)
Locate ".+".
Locate ".+1".

Variable x : nat.
Check x.+1.

(*| One important difference between notations and definitions is that
definitions represent a semantic barrier and definitions are an essential part
of theories whereas notations are a convenient (and powerful) shorthand. |*)
