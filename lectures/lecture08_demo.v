(* Demo accompanying slides *)

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat seq bigop.
Import Monoid.

Print Monoid.Law.
Print Canonical Projections operator.
About mulmA.

Lemma foo m n p q r :
  m + (n + p * (q * r)) = m + n + p * q * r.
Proof.
by rewrite !mulmA /=.
Qed.

(*

Here is some information which should
help you understand how exactly `rewrite mulmA` works
when it rewrites in the goal for the first time.

mulmA : forall [T : Type] [idm : T] (mul : law idm), associative mul

Or, unfolding `associative`:
mulmA : forall [T : Type] [idm : T] (mul : law idm) (x y z : T),
          mul x (mul y z) = mul (mul x y) z

Let's define a short-hand:
O := @operator

The goal (we focus on its left-hand side, LHS):
m + (n + p * (q * r)) = ...

Unfold notations in the goal:
addn             m  (addn              n (muln p (muln q r))) = ...

LHS of `mulmA` lemma:
mul              ?x (mul               ?y ?z                 )

LHS of `mulmA` lemma with inserted coercions:
(O ?T ?idm ?mul) ?x ((O ?T ?idm ?mul)  ?y ?z                 )

Let's unify the goal with the LHS of `mulmA` equation:
addn             m  (addn              n (muln p (muln q r))) = ...
(O ?T ?idm ?mul) ?x ((O ?T ?idm ?mul)  ?y ?z                 )

The head symbol get us
addn ≡ @operator ?T ?idm ?mul

We have the canonical instance!
addn <- operator ( addn_monoid )

Hence,
addn ≡ @operator ?T ?idm addn_monoid

And `?T` and `?idm` can be deduced from the type of `addn_monoid`:
addn ≡ @operator ?T ?idm addn_monoid
                           ..
                        @law ?T ?idm ≡ @law nat 0

So, these unify:
addn ≡ operator nat 0 addn_monoid

End of inference.

This is why after the first rewrite we get the following goal:
Lemma foo m n p q r :
  m + (n + p * (q * r)) = m + n + p * q * r.
Proof.
rewrite mulmA.
Set Printing Coercions.
Set Printing Implicit.

@operator nat 0 addn_monoid (@operator nat 0 addn_monoid m n) (p * (q * r)) =
  m + n + p * q * r
*)
