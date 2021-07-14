Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:= fun '(conj pa pb) => pa.

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:= fun aIb bIc pa => bIc (aIb pa).

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:= fun aIbIc aIb pa => aIbIc pa (aIb pa).

Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
:= fun nnna pa => nnna (fun na => na pa).

Definition or_comm :
  A \/ B -> B \/ A
:= fun aVb =>
  match aVb with
  | or_introl a => or_intror a
  | or_intror b => or_introl b
  end.

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:= conj
  (fun all_pq => fun x => match all_pq x with | conj p q  => conj q p end)
  (fun all_qp => fun x => match all_qp x with | conj q p  => conj p q end).

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:= conj
  (fun all_pq => fun x => or_comm (P x) (Q x) (all_pq x))
  (fun all_pq => fun x => or_comm (Q x) (P x) (all_pq x)).

Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:= fun n_ex_px => fun x px => n_ex_px (ex_intro P x px).

Definition exists_forall_not_ :
(exists x, A -> P x) -> (forall x, ~P x) -> ~A 
:= fun '(ex_intro _ x a_px) n_x_px a => (n_x_px x (a_px a)).

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2.
Admitted.

End Quantifiers.





Section Equality.

(** exercise: *)
Definition f_congr {A B} (f : A -> B) {x y : A} :
  x = y  ->  f x = f y
:= fun 'eq_refl => eq_refl.

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:= fun 'eq_refl 'eq_refl => eq_refl.

(** extra exercise *)
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p. Admitted.

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun e => conj (f_congr fst e) (f_congr snd e).

End Equality.

From mathcomp Require Import ssrfun.

Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= eq_refl.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f x => eq_refl.

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f g fEg x => 
  match fEg x with | eq_refl => eq_refl end.

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h fEg gEh x =>
  match gEh x with 
  | eq_refl => fEg x
  end.

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:= fun f g h fEg x => f_congr h (fEg x).

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:= fun f g h fEg x => fEg (h x).

End ExtensionalEqualityAndComposition.


From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= fun a b =>
  match a, b with
  | true, true   => erefl
  | true, fasle  => erefl
  | false, true  => erefl
  | false, false => erefl
  end.

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:= fun b =>
  match b with 
  | true  => id
  | false => id
  end.