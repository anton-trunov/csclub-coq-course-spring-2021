From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*|
=============================
The SSReflect tactic language
=============================

:Author: Anton Trunov
:Date: April 8, 2021


====================================================

|*)

(*| During the first part of the course we saw how
to build proof terms by hand. It turns out it is
quite tedious to do that for less trivial
developments than the examples we have. There is a
number of meta-languages called *tactic languages*
to help us build (proof) terms. Tactic languages
provide a user interface allowing us to perform
proof steps resembling logical *rules of
inference* more than functional programming we did
so far. But in the end tactic languages produce
proof terms and that is it, there is no magic it,
except that tactic languages can automate some
mundane steps making the overall process of
proving more pleasant.

Let's see some concrete examples and learn one
such tactic language, called SSReflect. We are
going to learn SSReflect by example, so you'd like
a more formal approach then I can refer you to the
reference manual:
https://coq.github.io/doc/master/refman/proof-engine/ssreflect-proof-language.html.
|*)

(*|
Basic tactics
-------------
*)

(*| Here is an example of using the SSReflct
tactic language to prove a simple lemma: |*)
Lemma A_implies_A :
  forall (A : Prop), A -> A.
Proof.
move=> A.
move=> proof_A.
exact: proof_A.
Qed.

(*| Let's break the example above down.

.. code-block:: Coq

   Lemma A_implies_A : forall (A : Prop), A -> A.

The type `forall (A : Prop), A -> A` is the
statement of a lemma named `A_implies_A`. The
`Lemma` vernacular essentially means `Definition`.
But in this case, instead of providing the body of
the definition after the `:=` syntax we finish the
statement with a dot (`.`).

So, after that dot Coq switches us into its proof
mode where it shows us our current proof goal in a
window (or in a terminal) and waits for our input.

After the lemma statement it is customary to put
an optional `Proof` vernacular which does nothing
semantically but it suggests we are going to start
a new proof. |*)

(*|
.. code-block:: Coq

   move=> A.
   move=> proof_A.
   exact: proof_A.
|*)

(*| This piece of code is an example of using
tactics to build a proof term. The tactics between
between `Proof` and `Qed` are commonly referred to
as "proof". But from the theoretical point of view
it is, of course, not a proof but a *recipe* to
build a proof. Each tactic invocation build the
underlying proof term *incrementally*. And since
SSReflect proof scripts alone (without using
interactive theorem proving) don't show you the
intermediate proofs steps, people often say it has
imperative flavor to it: you see some commands to
change the known part of the proof term but not
the term itsel. We are going to manually
instrument the proof to see how the underlying
term gets build incrementally.

The first tactic call `move=> A` means "assume `A`
is an arbitrary proposition". The `move=> proof_A`
incantation means "assume we have `A` as our
assumption". Having all that we can finish our
proof by providing the exact solution with `exact:
proof_A`.

The proof is finished with the `Qed` vernacular
which triggers re-typechecking of the proof term
and also seals the proof, i.e. it makes the body
of the lemma definition opaque which helps with
speeding up typechecking because the typechecker
does not need to unfold the body of the lemma
since it is computationally irrelevant and all we
care about is that we have a name and its type
now. One can check if a given definition is
transparent or opaque using the `About`
vernacular.

To understand better what is going on here, first
of all, let us note that the proof goal `forall (A
: Prop), A -> A` can be seen as a *stack* of
variables and assumtions, where the top of the
stack in our case is the variable `A`, the next
stack element is an assumption that we have a
proof of `A` and the last stack element is called
*conclusion*, which is again `A` in our case.

The double arrow (`=>`) is a *tactical*, it takes
a tactic (to its left) and a list of "actions",
`tac=> act1 act2 ... act_n`. First, Coq applies
the tactic `tac` to the top of the goal stack, And
then it executes actions from left to right. If an
action happens to be an identifier then it gets
introduced to the proof context which keeps the
knowledge available to us w.r.t. the current
proof. The proof context is visually represented
as the area located just above the bar (`=======`)
in the "goals" response from Coq.

The `move` tactic is like a no-operation tactic we
put mostly because `=>` needs a tactic to the left
of itself.

(Note: actually `move` can convert the goal to the
head normal form, but let us ignore this for now.)

The `exact` tactic tells Coq the exact solution of
the current subgoal. (I'm actually cheating right
now because `:` is a tactical as well and I'd like
to postpone its discussion a bit).

 |*)

(*| Now let's run the intrumented version and see
what is going on under the hood. We are going to
use the `Show Proof` vernacular command to display
the current (incomplete) proof term. Identifiers
prefixed with question marks stand for proof
"holes", i.e. some yet to be defined term. For
instance, `?Goal` stands for the current proof
goal Coq displays. |*)
Lemma A_implies_A' :
  forall (A : Prop), A -> A.
Proof.
move=> A.
Show Proof.
move=> proof_A.
Show Proof.
exact: proof_A.
Show Proof.
Unset Printing Notations.
Show Proof.
Set Printing Notations.
Qed.

(*| Let's see some more proofs and some new
tactics and tacticals. By the way, we have already
done the following proofs earlier by providing
explicit proof terms. |*)

Lemma A_implies_B_implies_A (A B : Prop) :
  A -> B -> A.
Proof.
move=> a.
move=> _.  (* ignore an assumption *)
exact: a.
Qed.

(*| Let's introduce the `apply` tactic which
applies the top of the goal stack to the
conclusion and might ask the user to prove an
assumption needed to do this. This tactic
facilitates the so-called backward reasoning: we
start with the goals conclusion and work our way
up by proving assumtions needed to finish the
proof. |*)

Lemma modus_ponens (A B : Prop) :
  A -> (A -> B) -> B.
Proof.
move=> a.
apply. (* backward reasoning *)
exact: a.
Qed.

(*| To take apart terms of inductive types, i.e.
to use the tactic-level analogue of pattern
matching, one can use the `case` tactic.

The `case` tactic, as many SSReflect tactics,
applies to the top of the goal stack, and
translates into pattern-matching at the term
level. E.g. if the top of the goal stack is a
conjunction then the top gets removed and two new
conjuncts get pushed on the goal stack. If the top
of the goal stack is a disjunction then the top of
the stack gets consumed and Coq generates two
subgoals corresponding to the left and right
disjuncts.

Let us see how to apply it to a conjunctive
hypothesis.

In the proof below we could use two tactis `move=>
a. move=> b.` to move two assumptions into the
proof context but it's easier to combined the two
commands into just one `move=> a b.`. And, by the
way, if you don't need an assumption then you can
use an underscore (`_`) after the double arrow to
clean it from the goal stack. |*)

Definition and1 (A B : Prop) :
  A /\ B -> A.
Proof.
case.         (* take apart conjunction *)
move=> a _.   (* move two assumptions in one go *)
exact: a.
Qed.

(*| On the other hand, to prove conjunctive goals
one needs the `split` tactic which allows one to
prove the two conjuncts as separate subgoals. |*)
Definition andC (A B : Prop) :
  A /\ B -> B /\ A.
Proof.
case.
move=> a b.
(* prove conjunction: creates one more subgoal *)
split.
(* 1st subgoal marked with a bullet and indented *)
- exact: b.
exact: a.
Qed.

(*| Now, let's see how to use `case` for
disjunctive assumptions and also how to use the
`left` and `right` tactics to prove disjunctive
goals.

The `left` tactic tells Coq that we are going to
prove the disjunctive goal at hand by proving the
left disjunct. The `right` tactics does the same
but for the right disjunct. |*)

Definition orC (A B : Prop) :
  A \/ B -> B \/ A.
Proof.
case.
- move=> a.
  right.       (* prove right disjunct *)
  exact: a.
move=> b.
left.          (* prove left disjunct *)
exact: b.
Qed.

(*| Let's put to work all the above together and
prove a lemma with a bit more involved proof. |*)
Lemma or_and_distr A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move=> a c.
  left.
  split.
  - exact: a.
  exact: c.
move=> b c.
right.
split.
- exact: b.
exact: c.
Qed.

(*| The lemma statement above can be considered as
trivial by experienced proof engineers, so more
than 10 LoC proof looks a bit large for a trivial
statement. And, indeed, we can make it much more
concise. Let us try it again on the same lemma. |*)

Lemma or_and_distr1 A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case=> [a|b] c.
- by left.
by right.
Qed.

(*| We have used several important features of the
SSReflect proof language:

  - intro-patterns, and
  - [by] tactical.
|*)

(*| Remember that the `=>` tactical can be
prepended by a number of tactics (but not all of
them), including the `case` tactic. In the example
above we split the conjunctive assumption first
and then case analyse on the disjunction using the
`case=> [act1 | act2 | ...]` syntax to perform
some actions on the top of the goal stack in each
generated *subgoal*. In our case

.. code-block:: Coq

   case=> [a|b].

sort of means

.. code-block:: Coq

   case.
   - move=> a. (* 1st active subgoal *)
   move=> b.   (* 2nd active subgoal *)

but we still have both subgoals to process.

The ``[act1 | act2 | ...]`` syntax is an instance
of intro-patterns. |*)

(*| The `by` tactical takes a list of tactics (or
a single tactic), applies it to the goal and then
tries to finish the proof using some simple proof
automation. E.g. `by []` means "the proof of the
goal is trivial", because Coq does not need any
hints from the user. This is equivalent to using
the `done` tactic. And, for instance, the `by
left` tactic means "we are going to the left
conjunct but it's proof is trivial". The local
proof automation we use here is sufficiently smart
to split conjunctive goals into several subgoals
but it won't try more advanced forms of proof
search like trying to prove the left disjunct and
if it does not work out then backtrack and try
proving the right disjunct.

The `by`, `exact` and `done` tactics/tacticals are
called *terminators* because if these do not solve
the goal completely, the user gets an error
message and the goal state gets restored. It is
recommended to put the terminators to mark where
the current subgoal is proven completely. This
helps fixing proofs when they break due to, for
instance, changes in the definitions of the
project. |*)

(*| An even terser version of the proof of our
current example can be written using one more
instance of intro-patterns: `[act1 act2 ...]`
which is used to break a conjunction-like
assumption and execute each of the actions on each
component, as in `[[a|b] c]` below.

One can also use the semicolon (`;`) tactical:
`tac1; tac2` means "execute the `tac1` tactic and
then execute the `tac2` tactic on each of the
generated by `tac1` subgoals". This can be
extended to `tac; [tac1 | tac2 | ...]` which means
"execute `tac` and then execute `tac`:math:`_i` on
the :math:`i`-th subgoal".

If there is a mismatch between the number of
subgoals and the number of supplied tactics you'll
see an error message. The user is allowed to skip
some tactics (or all of them), but the
corresponding pipe (`|`) symbols must be provided,
i.e. `tac; [| tac2 |]` gets executed like so:
first `tac` gets applied to the goal and generates
3 subgoals, then `tac2` gets applied to the second
subgoal.

Here is the resulting one-line proof we get after
combining the features we discussed so far. |*)
Lemma or_and_distr2 A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof. by case=> [[a|b] c]; [left | right]. Qed.

(*| There is one missing puzzle piece for us: we
can introduce hypotheses to the proof context but
cannot move them back to the top of the goal stack
and this is something that we need frequently when
proving lemmas in SSReflect.

The colon (`:`) tactical solves precisely this
problem: `move: foo` in a sense is a reversal of
`move=> foo`.

Let's illustrate the usage of the colon tactical
with the following example. |*)

Lemma HilbertSaxiom A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
move: abc.
apply.
- by [].
move: ab.
apply.
done.
Qed.

(*| Since `:` is a tactical we can combine it not
only with `move` but other tactics as well, for
example, with the `apply` tactic. The invocation
`apply: foo` can be read as "apply the lemma (or
hypothesis) `foo`" to the goal. But actually what
we do here is we move `foo` to the top of the goal
stack and apply it to the rest of the goal stack.

Moving a hypothesis back to the goal stack makes
it disappear from the proof context. If you need
to apply a hypothesis to the goal and still keep
it in the context, use parentheses around the
hypothesis name: `apply: (foo)`.

We can simplify the proof of the lemma above as
follows. |*)

Lemma HilbertSaxiom1 A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
apply: abc.
- by [].
by apply: ab.
Qed.

(*| Notice that the proof above contains a
trivially provable subgoal? To handle cases like
this one there is a special action `//` meaning
"try solving the new trivial subgoal and do not
change a subgoal if it's not trivial". This action
can be integrated into a tactic call using the
double arrow tactical, see the example below. |*)

Lemma HilbertSaxiom2 A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab a.
apply: abc=> //.
by apply: ab.
Qed.


(*|
`rewrite` tactic and `->` action
--------------------------------
*)

(*| The `rewrite` tactic lets us use equations. If
`eq : x = y` then `rewrite eq` changes `x`'s in
the goal to `y`'s. And `rewrite -eq` does
rewriting in the opposite direction. *)

Section RewriteTactic.

Variable A : Type.
Implicit Types x y z : A.

Lemma esym x y :
  x = y -> y = x.
Proof.
move=> x_eq_y.
rewrite x_eq_y.
by [].
Qed.

(*| `move=> eq; rewrite eq` is a frequent pattern
so there is an abbreviation for it introduced as
an action `->` which can be combined with the `=>`
tactical.

This action uses the top of the goal stack (which
must be an equation) and does rewriting. There is
also the symmetrical `<-` action. |*)

Lemma eq_sym_shorter x y :
  x = y -> y = x.
Proof.
move=> ->.
done.
Qed.

Lemma eq_trans x y z :
  x = y -> y = z -> x = z.
Proof.
move=> ->.
done.
Qed.

End RewriteTactic.


(*|
Induction
---------
*)

Lemma addnA :
  associative addn.
Proof.
rewrite /associative. (* unfold definition *)
move=> x y z.
(* But the above solution if not idiomatic, the
experienced user knows what `associative` looks
like, and the `=>` tactical can look inside of
definitions *)
Restart.
Show.
move=> x y z.
(* Proving this lemma needs induction which we can
ask Coq to use with `elim` tactic. We'd like to do
induction on the variable `x`. But, as usual,
`elim` operates on the top of the goal stack, so
we need to put back `x` into the goal: *)
move: x.
elim.   (* induction over `x` in this case *)
Show Proof.
Check nat_ind.
(* Notice that `elim` uses the `nat_ind` induction
principle under the hood. *)
- (* the base case *)
  (* `0 + (y + z)` reduces into `y + z` and
     `0 + y` reduces to `y`, hence
     the goal is equivalent to `y + z = y + z`,
     i.e. it can be solved trivially. *)
  by [].
(* inductive step *)
(* [IH] stands for "induction hypothesis" *)
move=> x IHx.
Fail rewrite IHx.
(* To use `IHx` we need to change the goal to
   contain `x + (y + z)`. To achieve this we need
   to use a lemma which lets us simplify `x.+1 +
   y` into `(x + y).+1`. Let's use the `Search`
   mechanism to find such a lemma: *)
Search (_.+1 + _).
(* This query returns a list of lemmas and a
brief examination shows `addSn` is the lemma we
are looking for *)
rewrite addSn.
(* Now we can use the induction hypothesis *)
rewrite IHx.
done.

Restart.
(* The proof can be simplified into: *)
by move=> x y z; elim: x=> // x IHx; rewrite addSn IHx.
Qed.


(*|
Summary
------- |*)

(*| See this great `cheatsheet
<http://www-sop.inria.fr/teams/marelle/advanced-coq-17/cheatsheet.pdf>`_
on SSReflect tactic, notations and even more
things. |*)

(*|
Tactic/tactical summary
======================= |*)

(*|

- The introduction tactical `=>`: the (simplified)
  grammar is `tac=> act` and it means "perform the
  tactic `tac` and then do the action `act`". If
  `act` is an identifier `ident`, then it is
  interpreted as "move the top of the goal stack
  to the proof context and give it a name
  `ident`".

- `move` tactic: think of it as a placeholder for
  tacticals for now. For instance, `=>` needs a
  tactic to the left of it, so if you don't need
  to call any tactic, just use `move`.

- `exact` tactic: works like `by apply`.

- `apply` tactic applies the top of the goal stack
  to the conclusion and might ask the user to prove
  an assumption needed to do this. This tactic
  facilitates the so-called backward reasoning.

- `case` tactic translates to pattern matching
  and can be used to destruct conjunctions into
  proof components or do proof by case analysis
  for disjunctive assumptions.

- `split` tactic lets us prove conjunctive goals
  by proving its components as separate subgoals.

- `left` tactic to prove left disjuncts.

- `right` tactic to prove right disjuncts.
|*)

(*|
Actions / intro-patterns
======================== |*)

(*|

 - *identifier*: refers to the top of the goal
   stack or a hypothesis in the context.

 - `[act1 act2 ...]`: destruct conjunction-like
   assumptions.

 - `[act1 | act2 | ...]`: case analysis.

 - `->`: rewrite in the goal with the top of the
   goal stack (from left to right).

 - `<-`: rewrite in the goal with the top of the
   goal stack (from right to left).

|*)


(*|
Vernacular summary
================== |*)

(*|

- `Lemma`: think of it as a synonym for `Definition`.

- `Proof`: an optional command which marks the
  beginning of a proof.

- `Qed`: a vernacular which finishes a proof and
  makes the lemma body opaque.

- `Show Proof`: a vernacular which displays the
  current (possibly unfinished) proof term.

- `Section`: groups several related definitions
  and/or theorems together and lets the user
  define common variables / hypotheses for the
  section definitions.

- `Variable`: declare a section variable which is
  going to be abstracted over at the end of the
  current section.

- `Implicit Types`: declare the types of section
  variables to reduce boilerplate and make
  typechecking faster in some cases.

- `Restart`: restart the current proof.

- `Show`: display the current proof goal.
 |*)

