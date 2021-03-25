Section PropositionalLogic.

Variables A B C : Prop.

Definition anb1 :
  A /\ B -> A
:=

Definition impl_trans :
  (A -> B) -> (B -> C) -> A -> C
:=

Definition HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C
:=

Definition DNE_triple_neg :
  ~ ~ ~ A -> ~ A
:=

Definition or_comm :
  A \/ B -> B \/ A
:=

End PropositionalLogic.



Section Quantifiers.

Variable T : Type.
Variable A : Prop.
Variable P Q : T -> Prop.
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:=

Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:=

Definition not_exists_forall_not :
  ~(exists x, P x) -> forall x, ~P x
:=

Definition exists_forall_not_ :
(exists x, A -> P x) -> (forall x, ~P x) -> ~A.

(** Extra exercise (feel free to skip): the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:=

End Quantifiers.





Section Equality.

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:=

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:=

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:=

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=

(** extra exercise *)
Definition congId A {x y : A} (p : x = y) :
  f_congr (fun x => x) p = p :=

(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=

End Equality.



Section ExtensionalEqualityAndComposition.

Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:=


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:=

(** Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=

(** Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=

(** Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=

(** Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=

End ExtensionalEqualityAndComposition.



