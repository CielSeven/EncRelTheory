Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.

Definition f_eq {A B : Type} (f g : A -> B) : Prop :=
  forall x, f x = g x.

#[export] Instance f_eq_refl (A B : Type) :
  Reflexive (@f_eq A B).
Proof.
  unfold Reflexive, f_eq.
  intros. reflexivity.
Qed.

#[export] Instance f_eq_symm (A B : Type) :
  Symmetric (@f_eq A B).
Proof.
  unfold Symmetric, f_eq.
  intros. symmetry. apply H.
Qed.

#[export] Instance f_eq_trans (A B : Type) :
  Transitive (@f_eq A B).
Proof.
  unfold Transitive, f_eq.
  intros. transitivity (y x0).
  - apply H.
  - apply H0.
Qed.

#[export] Instance f_eq_equiv (A B : Type) :
  Equivalence (@f_eq A B).
Proof.
  intros. split.
  - apply f_eq_refl.
  - apply f_eq_symm.
  - apply f_eq_trans.
Qed.
