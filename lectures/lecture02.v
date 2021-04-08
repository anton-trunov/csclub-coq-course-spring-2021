(*|
==========================================
Polymorphic functions, parameterized types
==========================================

:Author: Anton Trunov
:Date: March 18, 2021


====================================================

|*)


From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.


(*|
Polymorphic functions & Dependent functions
-------------------------------------------
|*)

Module MyNamespace.

(*| Last time we defined an identity function on
the type `bool` as follows. |*)
Definition idb := fun b : bool => b.

(*| Clearly, it would be very inconvenient to
create as many definitions as the number of types
for which we might need an identity function.
Morally, we need a function with a type like
:math:`\alpha \to \alpha`, where :math:`\alpha`
means 'arbitrary type'. Functions of the type
above are called *parametrically polymorphic*.

Coq does not support a typing discipline exactly
like the above. For instance, the following fails:
|*)

Fail Definition id : A -> A := fun x : A => x.

(*| The issue here is that Coq has no idea what
`A` means, as it is neither defined, nor *bound*
anywhere.

But, luckily for us, Coq supports parametric
polymorphism in an *explicit* form, meaning that
we need to tell Coq explicitly `A` is an arbitrary
type. And to do that, we need to be able to name
parameters in *type signatures* (and not just in
function definitions).

Essentially, we want to say something like `id :
(A : Type) -> A -> A` and while this might be a
valid type signature in Coq, it does not mean what
we intend it to mean here. This is usually called
:math:`\Pi`-types in type theory and the right Coq
syntax for what we mean is `forall` *ident* `:`
*term* `,` *term*. So in this case it is |*)

Definition id :
  forall A : Type, A -> A
:=
  fun A : Type => fun x : A => x.

(*| Here is how one would use `id`: |*)
Compute id bool true.
Compute id nat 42.

(*| Notice that our identity function gets two
arguments now to apply `id` to a computationally
relevant terms (`true` and `42` above) we need to
explicitly supply their respective types. We are
going to learn how to deal with this annoyance in
a moment.

Now let's take a pause an appreciate that we just
kind of learned what *dependent types* are: the
*type* of `id`'s result depends on the *value* of
its first parameter and we can check that
interactively: |*)

Check id bool : bool -> bool.
Check id nat : nat -> nat.

(*| Another thing to appreciate is that types in
Coq are terms and as such are first-class citizens
and can be stored in data structures, passed to
functions and returned from functions.

To recaputilate: a function of type like `forall x
: A, B` is called a dependently typed function
from `A` to `B(x)`, where `B(x)` means that `B`
may refer to `x` and `B` is usually called a
*family of types*. |*)

(*| In fact, let us reveal something I've been
hiding from you before: Coq does *not* have an
arrow type `->`, all its functions are dependently
typed and `->` is merely a notation that makes
things more convenient. This can be easily seen if
we use the `Locate` vernacular. |*)

Locate "->".

(*| Locate reveals that `A -> B` means `forall _ :
A, B` so it's a dependent function which cannot
refer to the named parameter in `B` (Coq forbids
that for underscores, `_`), making this a usual
non-dependent function type. |*)

(*| Also, Coq does not forbid us from unneeded naming in type signature, for example, we can write something like this: |*)

Definition id' :
  forall A : Type ,  forall x : A ,  A
:=
     fun A : Type =>    fun x : A => x.


(*|
Product Type
------------
|*)

(*| We can use currying to model functions of any
fixed arity (e.g. addition has arity 2 and we
assign it the type `nat -> nat -> nat`, which when
fully parenthesized is `nat -> (nat -> nat)`). But
what about functions returning multiple results,
e.g. Euclidean division which returns quotient and
reminder? |*)

(*| mention why it is called 'product type' |*)
Inductive prodn : Type := | pairn of nat & nat.

(*| `pairn of nat & nat` means that the `pairn`
constructor holds two natural numbers |*)

(*| Alternative syntax: |*)
Print prodn.

(*| Now it's possible to implement a function like
mentioned above -- it'll have the type `divmod :
nat -> nat -> prodn`. |*)

(*| But here is an issue: it'd be hard to create a
specialized product type for each combination of
types a function might return, e.g. `nat` and
`bool`, `bool` and `nat`, `bool` and `bool`, etc.
|*)

(*|
Parameterized inductive types
-----------------------------
|*)

(*| Instead we can use *parameterized* inductive
types like the following product type: |*)

Inductive prod (A B : Type) : Type :=
  | pair of A & B.

(*| Important: `prod` is not a type, it's a type
constructor! You can check it like so: |*)

Fail Check prod : Type.

(*| But, when speaking informally, people often
say `prod` is a type.

It's only when one applies `prod` to two type
arguments one gets a type. For example, |*)

Check prod nat nat : Type.

(*| By the way, the type `prod nat nat` is
equivalent to our specialized type `prodn`. |*)

(*| Let's discuss `prod`'s only constructor:
`pair`. Informally, the `pair` constructor carries
two components of some types `A` and `B`. What
type should it have? It could *not* be `A -> B ->
prod A B` because `A` and `B` would not be bound.
This is akin to the type of the polymorphic
identity function we discussed earlier.

Let's ask Coq about the type of `pair`: *)
Check pair.

(*| As we can see, `pair` has type `forall A B :
Type, A -> B -> prod A B` which means it actually
carries *four* components, namely the two types
`A` and `B` and two terms of those types
respectively. In other words, data constructors
*explicitly* bind type constructor's parameters.
|*)

(*| To create a pair of two terms like `42` and
`true` we use the `pair` constructor like so,
explicitly providing the types of our terms: |*)
Check pair nat bool 42 true : prod nat bool.

(*|
Implicit Arguments
------------------
|*)

(*| Passing explicitly types can be very annoying,
especially when the system should be able to
*infer* those for us. E.g. Coq knows that `42`'s
type is `nat` and `true`'s type is `bool` so it
could, in principle, help us with that. And
indeed, Coq has the incredibly powerful mechanism
of inferring *implicit arguments*. Here is how we
active it for the identity function `id` and the
`pair` data constructor: |*)

Arguments id [A] _.
Arguments pair [A B] _ _.

(*| `Arguments id [A] _` means that the type `A`
is going to be inferred by the elaborator, so the
user does not have to supply it. The same works
for `pair` but in that case Coq is going to infer
both types `A` and `B`. So there is no need to do
it by hand anymore: |*)

Check id 42.
Compute id 42.

Check pair 42 true.

(*| Notice that `pair nat bool 42 true` does not
typecheck anymore: |*)

Fail Check pair nat bool 42 true : prod nat bool.

(*| Note that it does not mean we just changed the
type of `pair`, no, the underlying formalizm is
still the same and uses explicit binding. It's
just we have an extra layer on top of it to help
us write more concise code in the style of the ML
family of languages.

To forbid Coq from implicitly supplying the
arguments we can use `@` syntax, which locally
switches off inference: *)

Check @pair nat bool 42 true : prod nat bool.

(*| Coq's pretty-printer takes into account the
implicitness information and does not show us the
implicit arguments even if we supplied those by
hand. Sometimes understanding the exact terms
being inferred by Coq is essential for proofs so
one needs a way to make the pretty-printer show
implicit arguments, this can be done like so: *)

Set Printing Implicit.
Check pair 42 true : prod nat bool.
Unset Printing Implicit.

(*| The `Set ...` family of vernacular commands
changes Coq's behavior globally and in our case
its effect needs to be reverted the corresponding
`Unset` command |*)

(*| It can be a bit tedious to explicitly use the
`Arguments` vernacular command for each and every
type or definition we introduce so there is a way
to ask Coq to decide which parameters it can infer
for us: |*)

Set Implicit Arguments.

(*| From now on and until either the end of the
current file or upon encountering the `Unset
Implicit Arguments` vernacular, Coq will try to
figure out which arguments can be made implicit.
|*)

(*|
Notations
---------
|*)

(*| Working with pairs using `prod` and `pair` is
not very common, because people usually prefer
more suggestive notations like `A * B` for the
product type or `(a, b)` for pairs. Coq lets us
introduce our own notations which modify its
parser on-the-fly. Notations in Coq are a complex
beast, so we will only scratch the surface here.
|*)

(*| Here is a notation for the product type. I'll
explain some elements of it below. Note that Coq
will warn us that the new notation is being
redefined, that's because the standard prelude
already has it defined for us. |*)

Notation "A * B" :=
  (prod A B)
  (at level 40, left associativity)
  : type_scope.

(*| So let us break this down: |*)

(*|
 - the `Notation` vernacular tells Coq
   we are going to extend its parser;
 - the notation being defined is usually enclosed
   in double quotes;
 - `A` and `B` (and identifiers in general)
   are automatically bound in the body of
   the notation following after `:=`;
 - the body of the notation which must
   be encloded in parentheses and this is what
   notation means when parsed;
 - then some grammatical information follows
   like the precedence level and associativity
   which we supply for infix binary operations
   like the one above; the lower level the tighter
   it binds;
 - after that an optional notation scope
   might follow;
 - one may provide some formatting info for the
   pretty-printer (not shown here).
|*)


(*|
Notation scopes
===============
|*)

(*| The programmer may reuse the same symbol for
multiple terms. In the notation above we reused
`*` symbol to mean type product. By default `*`
stands for multiplication on natural numbers. |*)

Locate "*".

(*| The term 'default interpretation' in the
output of `Locate` means that when Coq is not sure
about the purpose of `*`, it will assume it is
being used as the multiplication symbol, so the
following fails: |*)

Fail Check nat * bool.

(*| Here we have to give Coq a hint that we mean a
product type, we do this by specifying the
notation scope with `%type`: |*)

Check (nat * nat)%type.

(*| Here is another way of doing that: |*)

Check (nat * bool) : Type.

(*| In this case Coq knows that the term in the
parentheses is supposed to be a type (remember
that in Coq there is almost no difference between
terms/programs and types), so Coq knows how to
interpret `*` as it certainly cannot be
multiplication. |*)

(*| Yet another way of changing the default
meaning of a notation is opening its scope with
the `Open Scope` vernacular. Notation scopes in
Coq can be thought of as a stack of opened scopes
with the scope last opened to become the default
one and have precedence over the rest of them. |*)

Open Scope type_scope.
Locate "*".
Check (nat * nat).

(*| Since notation scopes are modeled with a
stack, closing a notation scope pops it off the
stack and changes the default interpretation to
the previous one. |*)

Close Scope type_scope.
Fail Check (nat * nat).
Locate "*".


(*| Let us mention the role of `left
associativity` in the above notation definition:
to model tuples of sizes more than two one may use
nested pairs. For example, a triple of elements of
types `nat`, `bool`, and `nat` can be modeled
like so: |*)
Check ((nat * bool) * nat)%type.

(*| `left associativity` lets us write drop the
parentheses and write it as |*)

Check (nat * bool * nat)%type.

(*| If we associate parentheses to the right, this
will be a different, although isomorphic, type.
|*)

Check (nat * (bool * nat))%type.

(*| Having introduced notation for the `prod` type
constructor, it would be nice to add notation for
the `pair` data contructor to be able to write
e.g. `(42, true)` instead of `pair 42 true`, which
is, as you already know, a shorthand for `@pair
nat bool 42 true`. |*)

(*| Here is a rather unwieldy approach: |*)
Notation "( p ; q )" := (pair p q).

Check (1; false).

(*| It's unwieldy because the following does not
work: `Check (1; false; 2).` |*)

(*| But we would want to use triples, quadruples,
etc. In this case, recursive notations come to the
rescue. |*)
Notation "( p , q , .. , r )" :=
  (pair .. (pair p q) .. r) : core_scope.

Check (1, false) : nat * bool.
Check (1, false, 3) : nat * bool * nat.
Check (1, false, 3, true) : nat * bool * nat * bool.

(*| Now we are ready to use what we've built so
far to write some simple programs manipulating
pairs. Let's define projections on pairs first.
|*)

Definition fst {A B : Type} : A * B -> A :=
  fun p =>
    match p with
    | (a, _) => a
    end.

(*| For now, let's think of `{A B : Type}` as `[A
B : Type]`, i.e. `A` and `B` are declared as
implicit parameters.

If you are not sure what some notations in a
definition mean, you can ask Coq to print it out
without using notations like so: |*)

Unset Printing Notations.
Print fst.
Set Printing Notations.

(*| The definition of the second projection is
analogous to `fst`. |*)
Definition snd {A B : Type} : A * B -> B :=
  fun p =>
    match p with
    | pair _ b => b
    end.

(*| Let's introduce the standard in SSReflect
notation for projections: |*)
Notation "p .1" := (fst p).
Notation "p .2" := (snd p).

(*| Here is how we can use it: |*)
Compute (42, true).1.
Compute (42, true).2.

(*| Let us define a function which swaps two
components of the input pair: |*)

Definition swap {A B : Type} : A * B -> B * A :=
  fun p =>
    match p with
    | (a, b) => (b, a)
    end.

(*|
Sum Type
--------
|*)

(*| The next important type in functional
programming is the sum type. This is also know as
`Result` type in OCaml or `Maybe` type in Haskell.
|*)

Inductive sum (A B : Type) : Type :=
  | inl of A
  | inr of B.

Notation "A + B" :=
  (sum A B) (at level 50, left associativity)
  : type_scope.

(*| The `sum` type can be used, for instance, to
simulate partial functions: if the function
succeeds and returns a valid result it computes to
`inl result` and if it fails then it reports a
failure explanation `inr explanation`. For
example, a parser might have type `String -> AST +
Error` so it either parses its input successfully
and returns a value of the `AST` type wrapped in
`inl`data constructor, or it fails to parse and
reports this as a value of a specialized `Error`
type wrapped into `inr` data constructor. |*)

(*| Here is a simple example of using the `sum`
typeaking to the `swap` function for the product
type: |*)
Definition swap_sum {A B : Type} :
  A + B -> B + A :=
  fun s =>
    match s with
    | inl a => inr B a
    | inr b => inl A b
    end.


End MyNamespace.

(*|
Summary
------- |*)

(*|
Vernacular summary
================== |*)

(*|

- `Set Printing Notations`: TODO

|*)
