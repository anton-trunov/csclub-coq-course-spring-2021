From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*|
===============================================
Views. `reflect`-predicate. Multi-rewrite rules
===============================================

:Author: Anton Trunov
:Date: April 22, 2021


====================================================

|*)


(*|
`reflect`-predicate
------------------- |*)

(*| As we mentioned earlier, the SSReflect proof
methodology is based on having logical and
symbolic (e.g. boolean) representations intermixed
in a goal, so that the user can switch between
those to drive the proof process.

The SSReflect methodology, thus, favors computable
predicates and relations.

Let's see an example now. |*)

(*|
Motivational example
==================== |*)

Lemma all_filter T (p : pred T) (s : seq T) :
  all p s -> filter p s = s.
Proof.

(*| First of all, let's try and understand the
goal we see here. There are several things:

- `p : pred T` means `p` is a *computable* predicate
  over type `T`, i.e. `pred T` is `T -> bool`;
- `all p s` means all elements of sequence `s`
  satisfy predicate `p`;
- `[seq x <- s | p x]` notation stands for
  `filter (fun x => p x) s`.

We can check all the above bullet points with
the following three simple commands:
 |*)


Print pred. (* .unfold .no-goals *)
Check all.  (* .unfold .no-goals *)
Locate "[ seq _ <- _ | _ ]". (* .unfold .no-goals *)


(*| But wait a minute, how come we can have a term
of type `bool` as an assumption in our goal? |*)

Check all p s : bool.

(*| And why the following works at all? |*)

Check all p s : Type.

(*| This works because of the mechanism of
*implicit coercions* Coq uses to make sense of
goals like the current one. To see clearly what is
going on here, use the following vernacular: |*)

Set Printing Coercions.

(*| Now we can see Coq inserted the corcion
`is_true` around `all p s` so the goal would
actually make sense. |*)

Print is_true. (* .unfold .no-goals *)

(*| If `eq^~ true` does not really make sense for
you: |*)
Locate "^~".   (* .unfold .no-goals *)

(*| Another approach would be to unfold `is_true`:
|*)
rewrite /is_true.
(*| Given the above, `is_true b` means `b = true`
-- this is one way to embed booleans into `Prop`.
|*)

Unset Printing Coercions.

(*| Now that we understand the goal we can prove
it by induction on `s`: |*)
elim: s => //= x s IHs.

(*| In our top assumption we have both `p x` which
is needed to simplify the `if`-expression in the
goal conclusion and `all p s` which is needed to
apply the induction hypothesis. So, at this point
we need to transform an assumption from its
symbolic form `?x && ?y = true` into its logical
form `?x = true /\ ?y = true`.

To do this we are going to use the mechanism of
*views* supported by SSReflect. |*)

move=> /andP.

(*| We already know the `/lemma` syntax as we saw
how it works for lemmas which are implications. In
this case it's something like this as well,
although there is some implicit machinery at work
too. The mechanism is called *view hints* and we
are going to cover it later. The rest of the proof
is very straightforward. |*)

case.
move=> ->.
move/IHs.
move=>->.
done.

(*| Let us refactor the proof above into something
more idiomatic |*)
Restart.

by elim: s=> //= x s IHs /andP[-> /IHs->].
Qed.

(*|
`reflect`-predicate: definition
=============================== |*)

(*| So, what is `reflect` in the type of `andP`
from above? |*)

About andP. (* .unfold *)

Print reflect. (* .unfold *)
Print Bool.reflect. (* .unfold *)

(*| The `reflect` type family (or indexed type, in
other words) connects a *decidable* proposition to
the corresponding boolean expression. This is not
the first time we come across an indexed type but
it's the first time we run into an indexed type
with two constructors where we can clearly see the
difference between *parameters* (which have to be
fixed across constructors, `P` here is a
parameter) and *indices* (which can vary between
constructors). In this case, type-level boolean
term indicates which constructor has been used to
construct a term of type `reflect P b`, e.g. when
one has a term of type `reflect P true` they know
the `ReflectT` constructor has been used to
construct the term which means we have a proof of
`P` we can get by pattern-matching on a term of
type `reflect P true`. (And pattern-matching on a
term of type `reflect P false` yields a refutation
of `P`.) |*)

Goal forall P, reflect P true -> P.
move=> P.
exact: (
  fun r : reflect P true =>
    match
      r in reflect _ b
      return (b = true -> P)
    with
    | ReflectT p => fun E => p
    | ReflectF np => fun E => ltac:(done)
    end erefl).

Undo.
case.

(*| `case` actually leads to unprovable goals
here. It's not intelligent enough to solve this
goal which requires *dependent* pattern matching.
We need to use a special version of `case` for
type families. Here is the syntax we need to solve
this. |*)

Undo.

move=> R.
case E: true / R.

(*| To the right of `/` we put a term (`R` in this
case) we are going to case analyse -- this needs
to be a type family. And to the left of `/` we put
the indices of the type family we'd like to get
substituted. Notice that we need to keep the
relation between the original value of the index
`true` and its values inside the branches of the
underlying `match`-expression and this is what `E`
in `case: E` is for. |*)
- done.
done.

Restart.

(*| Instead of `move=> R; case E: true / R` we can
use a shorhand: |*)
by move=> P; case E: true /.

Restart.

(*| Moreover, SSReflect can figure out the indices
on its own: |*)
by move=> P; case E: _/.
Qed.

(*| A lemma like `reflect P false -> ~ P` can be
proved analogously. |*)


(*| To reinforce what has been said already, let
us formally prove several lemmas about `reflect`.
For instance, we can show `P` if and only if `b =
true` as two separate lemmas. |*)

Lemma introT_my (P : Prop) (b : bool) :
  reflect P b -> (P -> b).
Proof.
case.
(*| The index `b` here works as a rewrite rule. |*)
- done.
by move=> /[apply].
Qed.

(*| The other direction is left as an exercise for
the reader. |*)
Lemma elimT_my (P : Prop) (b : bool) :
  reflect P b -> (b -> P).
Admitted.

(*| Essentially, we have shown `reflect P b -> (b
<-> P)`, i.e. `reflect P b` connects a decidable
proposition `P` to its decision procedure (the
boolean expression `b`). |*)

(*| For example, we can show `reflect P b` lets us
use classical reasoning (exercise): |*)
Lemma reflect_lem P b :
  reflect P b -> P \/ ~ P.
Admitted.

(*| Lets look at how to build `reflect`-predicates
for a couple of standard connectives. |*)

Lemma andP_my (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
case: b.
- case: c.
  - constructor.
    done.
  - constructor.
    by case.
- constructor.

Restart.

(*| An idiomatic solution would look something
like so: |*)
by case: b; case: c; constructor=> //; case.
Qed.

Lemma nandP_my b c :
  reflect (~~ b \/ ~~ c) (~~ (b && c)).
Proof.
case: b; case: c; constructor.
- by case.
- by right.
- by left.
by left.

Restart.

(*| This seems to be a rare opportunity for an
automatic tactic to fill in the blanks for us: the
`intuition` tactic can take care of the subgoals
generated by our brute force approach. |*)

by case: b; case: c; constructor; intuition.
Qed.

(*| Sometimes we will need to use `reflect b b` as
a placeholder. This is an easy exercise. |*)
Lemma idP_my (b : bool) :
  reflect b b.
Admitted.


(*|
Using reflection views on assumptions
===================================== |*)

(*| Let's continue figuring out how and why `andP`
works. |*)

Lemma special_support_for_reflect_predicates b c :
  b && c -> b /\ c.
Proof.
move/andP.
Show Proof.

(*| We see `andP` in a context of `elimTF`, let's
see what it is. |*)
About elimTF.

(*| `elimTF` is a generalization of `elimT` we proved above. |*)

Restart.

(*| Let us see what is going on when we say
`move/andP`: |*)
move=> Hb.
Check @elimTF (b /\ c) (b && c) true (@andP b c) Hb.
move: Hb.
move/(@elimTF (b /\ c) (b && c) true (@andP b c)).

(*| But where `elimTF` comes from? SSReflect uses
the mechanism of view hints which provide some
wrapping lemmas such as `elimTF` above. The user
can add a new view hint using the `Hint View`
vernacular `Hint View for move/ elimTF|3`.

Here `elimTF` is declared as a view hint for
the `move/` command. The (optional) number `3`
specifies the number of implicit arguments
to be considered for the declared hint view lemma.
|*)

(*| The `ssrbool.v` module already declares a
numbers of view hints, so adding new ones should
be justified. For instance, one might need to do
it if one defines a new logical connective. |*)

exact: id.
Qed.

(*| But why is `elimTF`'s type so complex? Because
it's applicable not only in the case the goal's
top assumtion is of the form `b && c`, but it also
works for `b && c = false`. |*)

Lemma special_support_for_reflect_predicates' b c :
  (b && c) = false -> ~ (b /\ c).
Proof.
move/andP.
Show Proof.

Restart.
move=> Hb.
Check @elimTF (b /\ c) (b && c) false (@andP b c) Hb.

exact: @elimTF (b /\ c) (b && c) false (@andP b c) Hb.
Qed.


(*| Reflection views usually work in both
directions |*)
Lemma special_support_for_reflect_predicates'' (b c : bool) :
  b /\ c -> b && c.
Proof.
move=> /andP.
Show Proof.
About introT.

(*| `introT` view hint gets implicitly inserted
because it is also declared with `Hint View`
command. |*)

done.
Qed.

(*|
Switching views at the goal
===========================
|*)

Lemma special_support_for_reflect_predicates''' (b c : bool) :
  b /\ c -> b && c.
Proof.
move=> bc.
(*| If we'd like, instead of the assumption,
change the goal, we can use `apply/` tactic: |*)
apply/andP.

Show Proof.

(*| In this case the `introTF` view hint gets
inserted because the `ssrbool` module introduces
the correspoding view hint: `Hint View for apply/ introTF|3` |*)

About introTF.
done.
Qed.

(*| Again, `introTF` is a general lemma to
accomodate goals of the form `_ = false`. |*)

Lemma special_support_for_reflect_predicates'''' (b c : bool) :
  ~ (b /\ c) -> b && c = false.
Proof.
move=> ab.
apply/andP.
Show Proof.
About introTF.
done.
Qed.


(*| Let's look at some more machinery to work with
specifiations for decision procedures. We are
going to look at the `eqn` -- the decision
procedure for equality on the `nat` type. |*)
Lemma eqnP_my (n m : nat) :
  reflect (n = m) (eqn n m).
Proof.
(*| One way to prove this is to turn [reflect]
into a bi-implication and prove the two directions
by induction separately. An idiomatic way to do
that is as follows: |*)

apply: (iffP idP).

About iffP.

(*| We need the trivial reflection view `idP` here
to convert the boolean expression `eqn n m` to the
proposition `eqn n m = true` (you don't see the `=
true` part in the subgoals because of the
`is_true` coercion). |*)

(*| The rest of the proof should be trivial at
this point. |*)
- by elim: n m => [|n IHn] [|m] //= /IHn->.
by move=> ->; elim: m.
Qed.


(*| Here is an example of using `iffP` with a
non-`idP` argument. Here we use `eqType` -- a type
with decidable equality and some machinery
associated with it, like `eqP`. |*)
Lemma nseqP (T : eqType) n (x y : T) :
  reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
rewrite mem_nseq.
rewrite andbC.
apply: (iffP andP).
- case.
  move/eqP.
  About eqP.
  move=>->.
  done.
case=> ->->.
rewrite eq_refl.
done.

(*| A more idiomatic solution |*)
Restart.

rewrite mem_nseq andbC; apply: (iffP andP) => [[/eqP]|[/eqP]].

(*| There is some code duplication here which can
be reduced using `-[   ]` syntax: |*)
Restart.
by rewrite mem_nseq andbC; apply: (iffP andP)=> -[/eqP].
(*| We cannot say just `[/eqP]` because Coq
expects us to provide tactics for both subgoals
and not just one. To bypass this restriction we
use the `-` syntax. |*)
Qed.

(*|
Rewriting with `reflect` predicates
=================================== |*)

(*| One can rewrite with view lemmas if those
represent equations, like `maxn_idPl`. |*)
About maxn_idPl.

(*| Let's see an example: |*)
Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
case/orP: (leq_total n2 n1) => [le_n21 | le_n12].
About leq_total.
- Search (maxn ?n1 ?n2 = ?n1).
  rewrite (maxn_idPl le_n21).

(*| Why does this trick work? |*)
Check (maxn_idPl le_n21).

(*| OK, this is an ordinary equation, no wonder
`rewrite` works. The view lemma [maxn_idPl] is
*not* a function but behaves like one here. Let us
check coercions! |*)
Set Printing Coercions.
Check (maxn_idPl le_n21).
(*| No magic: `elimT` get implicitly inserted. |*)
Unset Printing Coercions.

About elimT.

(*| `elimT` is a coercion from `reflect` to
`Funclass`, which means it gets inserted when one
uses a view lemma as a function. |*)

(*| Essentially we invoke the following tactic: |*)

Undo.
rewrite (elimT maxn_idPl le_n21).

(*| One can easily finish the proof, but let's
simplify it first. |*)
Restart.

(*| We remove the symmetrical case first: |*)
without loss le_n21: n1 n2 / n2 <= n1.
- by case/orP: (leq_total n2 n1) => le; last rewrite maxnC orbC; apply.
rewrite (maxn_idPl le_n21).
(*| The rest is an exercise |*)
Abort.


(*|
A specification example
======================= |*)

About allP.

(*| Check out some other specs in the `seq` and
`ssrnat` modules! |*)

Search reflect inside seq.
Search reflect inside ssrnat.

(*| The `inside` syntax lets one look for lemmas
inside a particular module only. |*)


(*|
Specs as rewrite mutli-rules
---------------------------- |*)

(*| We have seen `reflect`-predicates being able
to rewrite boolean expressions corresponding to
its index. We can take this approach even further.
Let's see an example of a mutli-rule. |*)

Example for_ltngtP m n :
  (m <= n) && (n <= m) ->
  (m == n) || (m > n) || (m + n == 0).
Proof.
by case: ltngtP.

(*| That was quick! |*)

About ltngtP.
About compare_nat.

Restart.

(*| `case: ltngtP` performs case analysis: it
generates three subgoals corresponding to thee
three cases, strictly less, equal, strictly
greater. |*)
case: ltngtP.
(*| Notice that a lot of boolean expressions got
replaced with `true` or `false` depending on a
concrete case we are covering. The `ltngtP` also
works as a rewrite rule. |*)
- done.
- done.
move=>/=.
done.
Qed.


(*| Let's see how one can implement this combined
lemma. |*)
Module Trichotomy.

(*| First, we define a type family (indexed type)
with indices corresponding to expressions we want
to rewrite in subgoals. We use the `Variant`
vernacular here which is exactly like `Inductive`
but the type cannot refer to itself in its
definition, in other words it's a non-recursive
inductive type. |*)
Variant compare_nat m n :
   bool -> bool -> bool -> bool -> bool -> bool -> Type :=
| CompareNatLt of m < n :
   compare_nat m n false false false true false true
| CompareNatGt of m > n :
   compare_nat m n false false true false true false
| CompareNatEq of m = n :
   compare_nat m n true true true true false false.

(*| Next, we define a specification lemma which
connect the type family above with concrete
expressions we want to rewrite. |*)
Lemma ltngtP m n :
  compare_nat m n (n == m) (m == n) (n <= m)
                  (m <= n) (n < m) (m < n).
Proof.
rewrite !ltn_neqAle [_ == n]eq_sym; case: ltnP => [nm|].
- by rewrite ltnW // gtn_eqF //; constructor.
rewrite leq_eqVlt; case: ltnP; rewrite ?(orbT, orbF) => //= lt_mn eq_nm.
- by rewrite ltn_eqF //; constructor.
by rewrite eq_nm; constructor; apply/esym/eqP.
Qed.
End Trichotomy.

(*| We can take this proof apart during a seminar
but here are things to observe here:

 - The `rewrite` tactic support a language of
   patterns to focus rewriting on a particular
   part of the goal, e.g. in this case rewrite
   will only happen in a subterm corresponding to
   the `_ == n` pattern.

 - The `ltnP` spec lemma which is like `ltngtP`
   but simpler.

 - Just like one can do chained transformations of
   the top of the goal stack, one can do it for
   the conclusion: `apply/esym/eqP`. |*)



(*|
Summary
------- |*)

(*|
Vernacular
========== |*)

(*|

- `Set Printing Coercions`: turn on printing of
  implicit coercions -- very useful to better
  understand goals.

- `Search <pattern> inside <module>`: narrow the
  scope of searching to a particular `module`.

|*)

(*|
Tactic/tactical summary
======================= |*)

(*|

- `-` action: can be used to connect unrelated
  views (`move=> /V1 - /V2`) or to force the
  interpretation of `[]` as *case splitting* when
  multiple subgoals are generated; `-[/eqP]`.

- `case ident: term`: case analyse on `term` and
  keep the corresponding equation in the context
  under the name of `ident`.

- `case: index_pattern / type_family`: case
  analyse on a term of indexed type and perform
  substitutions of its indices according to
  `index_pattern`.

- `constructor`: try to pick a data constructor
  automatically.

- `intuition`: a solver for propositional
  intuitionistic logic.

- `without loss` or `wlog`: "without loss of
  generality"-style reasoning.

- `apply/view_lemma`: use the view mechanism on
  the conclusion of the goal. Can be chained
  together like `apply/VL1/VL2/VL3`.

- `rewrite` tactic supports patterns: `rewrite
  [<pattern>]<equation>`.

|*)
