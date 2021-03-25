(*|
===========================================
Logic, equality, dependent pattern matching
===========================================

:Author: Anton Trunov
:Date: March 25, 2021


====================================================

|*)


(*|
Intuitionistic logic
--------------------
|*)

(*| To be able to write program specifications we
need to build ourselves a logic in which we are
going to express the usual connectives like 'and',
'or', 'not', etc., and also, quantifiers using the
natural deduction style.

Logic we are going to emulate in type theory can
be classified intuitionistic higher-order logic.
Sometimes peopla also use the terms 'constructive'
and 'intuitionistic' interchangeably, and, strictly
speaking, it's not correct but we are not going to
be too pedantic about it.

In the constructive setting we demonstrate the
existence of mathematical objects by providing a
method (algorithm) for creating the object. In
type theory the methods are going to be terms.

There is a correspondence between terms and types
on one side and proofs and propositions on the
other. Type theory not only lets us emulate
higher-order logic but it also lets us manipulate
proofs as first-class objects, i.e. pass those to
functions, pack them into data structures, return
from functions, etc. This creates a powerful
framework to do mathematical reasoning and program
verification. |*)

From mathcomp Require Import ssreflect ssrfun.
Set Implicit Arguments.

Module MyNamespace.

(*|
Implication
===========
|*)

(*| Implication corresponds to the function type.
Having a proof of '`A` implies `B`', amounts to
having a function of type `A -> B` which
transforms a proof of proposition `A` into a proof
of proposition `B`.

Here is a proof that `A` implies `A`. This
corresponds to the identity function, as we have
already seen. |*)

Definition A_implies_A (A : Prop) :
  A -> A
:= fun proof_of_A : A => proof_of_A.

(*| You can read the above definition as a *lemma*
named `A_imlpies_A` stating that for any
proposition `A`, `A` implies `A` and the proof of
the lemma is the term `fun proof_of_A : A =>
proof_of_A`.

We are using the `Prop` universe which is yet
another primitive of Coq which we are going to
talk in some depth a bit later. For now we just
need to know that `A : Prop` means '`A` is a
proposition'. |*)

(*| Yet another example: |*)
Definition A_implies_B_implies_A (A B : Prop) :
  A -> B -> A
:= fun proof_A => fun proof_B => proof_A.

(*| This corresponds to the well-known `const` function. |*)

(*| And here is the internalized 'modus ponens' rule
in our setting: |*)

Definition modus_ponens (A B : Prop) :
  A -> (A -> B) -> B
:= fun pA pAimpliesB => pAimpliesB pA.

(*| As you can see, the modus ponens rule is
nothing more but a simple function application.
|*)


(*|
Conjunction
===========
|*)

(*| A constructive proof of a conjunction :math:`A
\cap B` is a pair of a proof :math:`A` and a proof
of :math:`B`. This suggests the following
definition of conjunction: |*)

Inductive and (A B : Prop) : Prop :=
  | conj of A & B.

Notation "A /\ B" := (and A B) : type_scope.

(*| Notice the strong resemblance between [and]
and [prod]:

.. code-block:: Coq

   Inductive prod (A B : Type) : Type :=
     | pair of A & B.
|*)

(*| Let's prove that conjunction is commutative |*)

Definition andC (A B : Prop) :
  A /\ B -> B /\ A :=
  fun pAandB =>
    match pAandB with
    | conj pA pB => conj pB pA
    end.

(*| Have you noticed that the proof of `A /\ B ->
B /\ A` looks the same (modulo contructor names)
as the function that swaps the two components of a
pair? |*)

(*|
Disjunction
===========
|*)

(*| A constructive proof of a disjunction :math:`A
\cup B` is either a proof of :math:`A` or a proof
of :math:`B` and a mark telling us precisely what
a proof of which proposition we are dealing with.
This suggests the following definition of
disjunction: |*)
Inductive or (A B : Prop) : Prop :=
  | or_introl of A
  | or_intror of B.

Notation "A \/ B" := (or A B) : type_scope.
Arguments or_introl [A] B _, [A B] _.
Arguments or_intror [A] B _, [A B] _.

(*| Again, notice the strong resemblance between [or]
and [sum] types:

.. code-block:: Coq

   Inductive sum (A B : Type) : Type :=
     | inl of A
     | inr of B.

The only real difference is that `or` lives in
the `Prop` universe and `sum` inhabits `Type`. |*)

Definition and_or_distr (A B C : Prop) :
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C)
:= fun '(conj paob pc) =>
     match paob with
     | or_introl pa => or_introl (conj pa pc)
     | or_intror pb => or_intror (conj pb pc)
     end.


(*|
The true proposition
====================
|*)

(*| The trivially true proposition does not hold
any information and its proof should be trivial as
well. This suggests the true proposition is
basically a unit type that lives in the `Prop`
universe. It has exactly one constructor named `I`
for historical reasons. |*)
Inductive True : Prop :=
  | I.

(*| A couple simple examples |*)
Definition anything_implies_True (A : Prop) :
  A -> True
:= fun _ => I.

Definition True_and_True :
  True /\ True
:= conj I I.

(*|
Falsehood
=========
|*)

(*| This is an empty type that lives in
the `Prop` universe: it has no constructors. |*)
Inductive False : Prop := .

(*| Because `False` has no constructors it is not
possible to prove it without using any
assumptions, i.e. in the empty context, provided
the proof assistant's implementation does not have
critical bugs. Usually, however, proof assistants
*have* critical bugs. For instance, Coq's team
documents those here:
https://github.com/coq/coq/blob/master/dev/doc/critical-bugs

Also, because `False` does not have any
constructors, a term of type `False` enjoys
peculiar pattern matching shape: one has to
provide a term for each branch of a pattern
matching expression and since there are no
branches one can form a term of any type because
there is no need to provide any terms. This is
known in logic as the 'principle of explosion' or
'ex falso quodlibet'. Here is an example showing
that falsehood implies anything: |*)

Definition exfalso_quodlibet {A : Prop} :
  False -> A
:= fun pF : False => match pF with end. (* no branches *)

(*| One more simple example: |*)
Definition a_or_false_implies_a (A : Prop) :
  A \/ False -> A
:= fun paof =>
     match paof with
     | or_introl pa => pa
     | or_intror pf => exfalso_quodlibet pf
     end.

(*|
Negation
========
|*)

(*| In principle, it is possible to introduce
logical negation as a first-class connective,
however, this is rarely done in practice and we
understand `not A` (with the corresponding
notation `~ A`) as just a shorthand for the
implication `A -> False`. |*)

Definition not (A : Prop) := A -> False.
Notation "~ A" := (not A) : type_scope.

(*| To prove `A -> ~ ~ A` one needs to keep in
mind the statement means `A -> ((A -> False) ->
False`): |*)
Definition double_negation_introduction (A : Prop) :
   A -> ~ ~ A
:= fun pa : A => fun pna : ~ A => pna pa.

(*| The logic defined in this style is called
'intuitionistic' and it is known that, in general,
it's not possible to prove the classical double
negation elimination principle in it, i.e. it's
impossible to provide a proof term for the type `~
~ A -> A`, where `A` is an arbitrary proposition.
|*)


(*|
Equivalence (biimplication)
===========================
|*)

(*| Just as negation, logical equivalence is not a
first-class connective in Coq: there is a
definition `iff` which stands for a conjunction of
two implications and the corresponding `<->`
notation. |*)

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) : type_scope.

(*| We'll see some examples with the logical
equivalence a bit later. |*)


(*|
Universal quantifier
====================
|*)

(*| Universal quantifier is just the dependent
function type. Under the constructivist's
interpretation, a proof of a univerally quantified
proposition :math:`\forall x. P(x)` transforms an
individual :math:`t` into a proof of :math:`P(t)`,
which is what a dependently typed function does in
type theory. In this case we cannot build our own
piece of logic and rely on the Coq's primitive.
Also, notice that we are working in a typed
setting, so we would write the above proposition
as `forall x : T, P x`, where `P : T -> Prop` is a
predicate, i.e. a function from some type into
`Prop`.

Here is a simple example: |*)

Definition forall_andD (A : Type) (P Q : A -> Prop) :
  (forall x, P x /\ Q x) ->
  (forall x, P x) /\ (forall x, Q x)
:= fun all_pq =>
     conj
       (fun x => match all_pq x with conj px _ => px end)
       (fun x => match all_pq x with conj _ qx => qx end).

(*|
Existential quantifier
======================
|*)

(*| Existential quantifier is the type of
*dependent* pairs. Under the constructivist's
interpretation, a proof of an existentially
quantified proposition :math:`\exists x. P(x)`
consists of two components: an individual
:math:`t` and a proof that the property :math:`P`
holds for it. In this case we introduce a type
which generalizes conjunction: now the type of the
second component may depend on the *value* of the
first component. |*)

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  | ex_intro (x : A) (proof : P x).

(*| Simplified notation |*)
Notation "’exists’ x : A , P" :=
  (ex (fun x : A => P))
    (at level 200, right associativity).

(*| Full-blown notation: multiple binders |*)
Notation "'exists' x .. y , p" :=
  (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(*| Here is a simple example of reasoning with the
existential quantifier: |*)
Definition exists_not_forall A (P : A -> Prop) :
  (exists x, P x) -> ~ (forall x, ~ P x)
:=
  fun x_px : exists x, P x =>
    fun all_npx : forall x, ~ P x =>
      match x_px with
      | ex_intro x px => all_npx x px
      end.

(*| Currying for dependent pairs: |*)
Definition curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q)
:=
  fun f : (exists x, P x) -> Q =>
    fun x : A =>
      fun px : P x =>
        f (ex_intro P x px).


(*|
Equality
========
|*)

(*| Equality is one of the main topics of type
theory and it has a hierarchy of notions of
equality / equivalence there. |*)

(*|
Definitional equality
^^^^^^^^^^^^^^^^^^^^^
|*)

(*| There is a builtin notion of equality between
terms which lives at the meta-level. It's called
*definitional* or judgemental equality and it says
that any two *convertible* terms are
non-distinguishable. Convertible here means you
can transform the terms into each other by
computation. It's important that the user cannot
*prove* that two terms are definitionally equal
because there cannot be any evidence of
definitional equality in the language, i.e. one
cannot build a proof artefact stating that two
terms are definitionally equal. |*)

(*|
Propositional equality
^^^^^^^^^^^^^^^^^^^^^^
|*)

(*| We can internalize definitional equality into
our language using the notion of propositional
equality. This is going to be our first encounter
of *indexed* types. |*)

Inductive eq (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq x x.

(*| The only notion of equality we are putting in
is *reflexivity*.

In the definition above the unnamed type parameter
`A` after the colon is called an *index*. The `x`
identifier is called a *parameter*. There is a
crucial difference between parameters and indices:
parameters of an inductive type must stay constant
for all constructors and indices are allowed to
vary between constructors. In this case there is
no variation because there is just one constructor
and there are no other terms of type `A` except
`x`. But the way pattern matching works for such
*type families* as `eq` lets us simulate equality.
|*)

(*| First, let us define a convenient notation for
the `eq` type. |*)
Notation "x = y" := (eq x y) : type_scope.

Arguments eq_refl {A x}, {A} x.

(*| We are going to use `eq_refl` as the proof
(witness) of propositions stating that two terms
are equal. For example, we can check that terms
that are equal modulo :math:`\beta`- and
:math:`\iota`- reduction are propositionally equal
(because those are equal definitionally too). |*)

Check eq_refl 0 : 0 = 0.
Check eq_refl : 0 = 0.
Check eq_refl : (fun _ => 0) 42 = 0.
Check eq_refl : 2 + 2 = 4.

(*| The following does not work because here one
can either build terms like `eq_refl 0` (or type
`0 = 0`) or `eq_refl 1` (of type `1`) |*)
Fail Check eq_refl : 0 = 1.

(*| So what terms are considered definitionally
equal? The `eq_refl` constructor lets us check
that. Let's see some examples for functions: |*)

Variables A B : Type.
Variable f : A -> B.

(*| Syntactically equal functions are
definitionally equal |*)
Check eq_refl : f = f.

(*| :math:`\alpha`-renaming |*)
Check eq_refl : (fun x => x) = (fun y => y).

(*| :math:`\eta`-expansion: this equality is called the
uniqueness principle in this case it means 'every
element of a function type is a function'. |*)
Check eq_refl : (fun x => f x) = f.


(*| Let's prove propositional equality is an
equivalence relation, i.e. reflexive, symmetric
and transitive. |*)

(*| The reflexivity case is trivial because we
already defined our equality relation to be
reflexive: |*)
Definition eq_reflexive A (x : A) :
  x = x
:=
  eq_refl x.

(*|
Dependent pattern matching
^^^^^^^^^^^^^^^^^^^^^^^^^^
|*)

(*| To prove symmetry, we need to use dependent
pattern matching which lets us utilize the difference between parameters and indices: |*)
Definition eq_sym_unannotated A (x y : A) :
  x = y -> y = x
:= fun (pf : x = y) =>
   (match pf with
    | eq_refl => (eq_refl x : x = x)  (* notice the type here *)
    end) : y = x.                     (* and here *)

(*| To understand the magic above one needs to use
the fully annotated version of the
`match`-expression. This time we need to add the
`in` annotation which lets us reinterpret the type
of the matchee and the `return` annotation which
lets us specify the return type of the
`match`-expression. What's important here is that
the `in` annotation lets one bind *indices* to
fresh variables with the intention those bind
variables are going to be rewritten in the
branches of `match`-expressions according to the
definition of the (indexed) inductive type. |*)

Definition eq_sym A (x y : A) :
  x = y -> y = x
:= fun (pf  : x = y) =>
     match
       pf in (_ = b)
       return (b = x)
     with
     | eq_refl => eq_refl x
     end.

(*| Using the annotated version of the `match`-expression we can prove `eq` is transitive. Thus, we have established `eq` is an equivalence relation |*)
Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
:=
  fun pf_xy : x = y =>
    match
      pf_xy in (_ = b)
      return (b = z -> x = z)
    with
    | eq_refl => fun (pf_xz : x = z) => pf_xz
    end.

End MyNamespace.
