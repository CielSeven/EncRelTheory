Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Import SetsNotation.
From FP Require Import SetsFixedpoints PartialOrder_Setoid.
From MonadLib.SetMonad Require Export Monad.
Local Open Scope sets.
Local Open Scope nat.

Import MonadNotation.
Local Open Scope monad.

(** Set Monad *)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => Sets.singleton a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

Notation program := SetMonad.M.

Ltac unfold_monad := 
  unfold bind, ret; simpl; 
  unfold SetMonad.bind, SetMonad.ret; simpl.

Ltac unfold_monad_in H := 
  unfold bind, ret in H; simpl in H; 
  unfold SetMonad.bind, SetMonad.ret in H; simpl in H.

Tactic Notation "unfold_monad" "in" hyp(H) :=
  unfold_monad_in H.

Import SetMonad.

Definition choice {A: Type} (f g: program A):
  program A := f ∪ g.

Definition test (P: Prop): program unit :=
  fun _ => P.

Notation "'assume' P" := (test P) (at level 50).

Definition any (A: Type): program A :=
  Sets.full.


Import Monad.
Module SetMonadExamples.

(** return an arbitrary even number *)
Example arbitrary_even: program Z :=
  x <- any Z;; ret (2 * x)%Z. 

Example compute_abs (z: Z): program Z :=
  choice
    (assume (z >= 0)%Z;; ret z)
    (assume (z <= 0)%Z;; ret (-z)%Z).

Example any_prime: program nat :=
  x <- any nat;;
  assume (~ exists (m n: nat), m > 1 /\ n > 1 /\ x = m * n);;
  ret x.

End SetMonadExamples.


Lemma bind_union_distr_l:
  forall A B (f: program A) (g1 g2: A -> program B),
    bind f (g1 ∪ g2) == bind f g1 ∪ bind f g2.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [? [? | ?]]]; [left | right]; exists a0; tauto.
  + intros [[a0 ?] | [a0 ?]]; exists a0; tauto.
Qed.

Lemma bind_union_distr_r:
  forall A B (f1 f2: program A) (g: A -> program B),
    bind (f1 ∪ f2) g == bind f1 g ∪ bind f2 g.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[? | ?] ?]]; [left | right]; exists a0; tauto.
  + intros [[a0 ?] | [a0 ?]]; exists a0; tauto.
Qed.

Lemma bind_choice_equiv {A B: Type}: 
  forall (c0 c1: program A) (c2: A -> program B),
    x <- (choice c0 c1);; c2 x == choice (x <- c0;; c2 x) (x <- c1;; c2 x).
Proof.
  intros.
  unfold choice.
  apply bind_union_distr_r.
Qed.

Lemma bind_indexed_union_distr_l:
  forall A B I (f: program A) (g: I -> A -> program B),
    bind f (⋃ g) == ⋃ (fun i: I => bind f (g i)).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [? [i ?]]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [| exists i]; tauto.
Qed.

Lemma bind_indexed_union_distr_r:
  forall A B I (f: I -> program A) (g: A -> program B),
    bind (⋃ f) g == ⋃ (fun i: I => bind (f i) g).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[i ?] ?]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [exists i |]; tauto.
Qed.

Lemma bind_assoc:
  forall (A B C: Type)
         (f: program A)
         (g: A -> program B)
         (h: B -> program C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Proof.
  intros; simpl.
  unfold SetMonad.bind; sets_unfold; split; intros.
  + destruct H as [a2 [H H0]].
    destruct H as [a3 [H1 H2]].
    exists a3; split; auto.
    exists a2; tauto.
  + destruct H as [a2 [H0 H]].
    destruct H as [a3 [H1 H2]].
    exists a3; split; auto.
    exists a2; tauto.
Qed.

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> program B),
  bind (ret a) f == f a.
Proof.
  intros.
  unfold bind, ret; simpl.
  unfold SetMonad.bind, SetMonad.ret.
  sets_unfold.
  intros b.
  split; intros.
  - destruct H as (? & ? & ?).
    subst; tauto.
  - do 2 eexists; eauto.
Qed. 

Lemma bind_ret_r:
  forall (A: Type)
         (f: program A),
  bind f ret == f.
Proof.
  intros.
  unfold bind, ret; simpl.
  unfold SetMonad.bind, SetMonad.ret.
  sets_unfold.
  intros b.
  split; intros.
  - destruct H as (? & ? & ?).
    subst; tauto.
  - do 2 eexists; eauto.
Qed. 


#[export] Instance bind_mono (A B: Type):
  Proper (Sets.included ==> Sets.included ==> Sets.included)
    (@SetMonad.bind A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b [a ?]; exists a.
  specialize (Hf a); specialize (Hg a b).
  tauto.
Qed.

#[export] Instance bind_congr (A B: Type):
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@SetMonad.bind A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b; split; intros [a ?]; exists a.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
Qed.

#[export] Instance choice_equiv_Proper {A: Type}:
  Proper (Sets.equiv ==> Sets.equiv  ==> Sets.equiv) (@choice A).
Proof.
  unfold Proper, respectful; intros.
  unfold choice.
  rewrite H, H0.
  reflexivity.
Qed.

(** Below, the repeat loop is defined using a fixed point. *)

Definition repeat_break_f
             {A B: Type}
             (body: A -> program (CntOrBrk A B))
             (W: A -> program B)
             (a: A): program B :=
  x <- body a;;
  match x with
  | by_continue a' => W a'
  | by_break b => ret b
  end.

Definition repeat_break
             {A B: Type}
             (body: A -> program (CntOrBrk A B)):
  A -> program B :=
  Lfix (repeat_break_f body).

(** We also define the 'continue' and 'break' statements within the loop body. *)

Definition continue {A B: Type} (a: A):
  program (CntOrBrk A B) :=
  ret (by_continue a).

Definition break {A B: Type} (b: B):
  program (CntOrBrk A B) :=
  ret (by_break b).

(** loops with range iterator *)
Definition range_iter_f {A: Type} (hi: nat)
  (body: nat -> A -> program A) (W: (nat * A) -> program A) :=
  fun '(i, a) =>
    choice
    (assume (i < hi);;
     a' <- body i a;;
     W(i+1, a'))
    (assume (i >= hi);;
     ret a).

Definition range_iter {A: Type} (lo hi: nat)
  (body: nat -> A -> program A) :=
  fun a => Lfix (range_iter_f hi body) (lo, a).

(** range-iterator loops with break *)
Definition range_iter_break_f
  {A B: Type} (hi: nat)
  (body: nat -> A -> program (CntOrBrk A B))
  (W: (nat * A) -> program (CntOrBrk A B)) :=
  fun '(i, a) =>
    choice
     (assume (i < hi);;
      res <- body i a;;
      match res with
      | by_continue a' => W (i+1, a') 
      | by_break b => break b
      end)
     (assume (i >= hi);;
     continue a).

Definition range_iter_break
  {A B: Type} (lo hi: nat)
  (body: nat -> A -> program (CntOrBrk A B)) :=
  fun a => Lfix (range_iter_break_f hi body) (lo, a).

Module SetMonadExamples'.
Local Open Scope Z.

(** * Set Monad example 1: 3x + 1 *)

Definition body_3x1 (x: Z): program (CntOrBrk Z Z) :=
  choice
    (assume (x <= 1);; break x)
    (assume (x > 1);;
     choice
      (assume (exists k, x = 2 * k);;
       continue (x / 2))
      (assume (exists k, x = 2 * k + 1);;
       continue (3 * x + 1))).

Definition run_3x1: Z -> program Z :=
  repeat_break body_3x1.

(** * Set Monad example 2: Binary search *)

Definition body_binary_search (P: Z -> Prop):
  Z * Z -> program (CntOrBrk (Z * Z) Z) :=
  fun '(lo, hi) =>
  choice
    (assume (lo + 1 = hi);; break lo)
    (assume (lo + 1 < hi);;
     let mid := (lo + hi) / 2 in
     choice
       (assume (P mid);; continue (mid, hi))
       (assume (~ P mid);; continue (lo, mid))).

Definition binary_search (P: Z -> Prop) (lo hi: Z):
  program Z :=
  repeat_break (body_binary_search P) (lo, hi).

End SetMonadExamples'.
