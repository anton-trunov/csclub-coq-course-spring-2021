From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Exercise *)
Lemma elimT_my (P : Prop) (b : bool) :
  reflect P b -> (b -> P).
Admitted.


(** * Exercise *)
Lemma reflect_lem P b :
  reflect P b -> P \/ ~ P.
Admitted.


(** * Exercise *)
Lemma orP_my (b c : bool) :
  reflect (b \/ c) (b || c).
Proof.
Admitted.


(** * Exercise *)
Lemma idP_my (b : bool) :
  reflect b b.
Admitted.


(** * OPTIONAL Exercise *)
Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
Admitted.



(** * Exercise (use `case: ltngtP` at some point to solve it) *)
Lemma maxnC : commutative maxn.
Proof.
Admitted.



(**  * Exercise *)
(* Take apart and understand this proof *)
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


(** * Exercise *)
Variant max_min_multirule (m n : nat) :
   nat -> nat -> nat -> nat -> Set :=
  | MaxMinNatLe of m <= n : max_min_multirule m n m m n n
  | MaxMinNatGe of m >= n : max_min_multirule m n n n m m.

Lemma maxminP m n : max_min_multirule m n (minn n m) (minn m n)
                                          (maxn n m) (maxn m n).
Admitted.

(** Use [case: maxminP] to prove the following *)
Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Admitted.

