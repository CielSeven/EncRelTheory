Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Require Import MonadLib.StateRelMonad.StateRelMonad.
From EncRelSeq.Basics Require Import basicasrt relasrt.
From EncRelSeq Require Export semantics errsem.

Local Open Scope sets_scope.

Module ConfigReineStatreRelMonad.

(* Configuration Refinement *)
Definition config_refinement {Σ A: Type} (g1 g2: (Σ * program Σ A)%type ) : Prop :=
  let '(σ1, c1) := g1 in
  let '(σ2, c2) := g2 in
  (forall r σ₃, c2 σ2 r σ₃ -> c1 σ1 r σ₃).

Arguments config_refinement: simpl never.
Notation " g1 '↪' g2 " := (config_refinement g1 g2) (at level 28, left associativity).

#[export] Instance configrefine_reflexivity {Σ A: Type}: Reflexive (@config_refinement Σ A).
Proof.
  hnf. unfold config_refinement. intros. intuition eauto. Qed. 
#[export] Instance configrefine_refinement_transivity {Σ A: Type}: Transitive (@config_refinement Σ A).
Proof.
  hnf. unfold config_refinement. intros [? ?] [? ?] [? ?]. intuition eauto. Qed. 


Section config_refinement_rules.
  Context {Σ A B: Type}.

  Import MonadNotation.
  Local Open Scope monad.

  Lemma config_refinement_ret : forall (c: program Σ A) (σ1 σ2: Σ) a,
    c σ1 a σ2 <->
    ( σ1, c ) ↪ ( σ2, ret a).
  Proof.
    intros; unfold config_refinement; simpl; unfold_monad; sets_unfold; intros.
    split;intros;auto.
    destruct H0. subst.
    subst;auto.
  Qed.

  Lemma config_refinement_bind : forall (c1 :program Σ A) (c2: A -> program Σ B) (σ1 σ2: Σ) a ,
    c1 σ1 a σ2 ->
    (σ1, bind c1 c2 ) ↪ ( σ2, c2 a).
  Proof.
    intros; unfold config_refinement; unfold_monad; simpl; sets_unfold; intros.
    eexists;eauto.
  Qed.
  
  Theorem configrefine_decompose (c1 c2: program Σ A) (st1 st2: Σ):
    (st1, c1) ↪  (st2, c2) <->
    (forall X, st1 ∈ weakestpre c1 X -> st2 ∈ weakestpre c2 X).
  Proof.
    split;intros.
    - unfold config_refinement, weakestpre in *.
      sets_unfold. sets_unfold in H0.
      intros. eapply H0;auto.
    - specialize (H (fun r st3 => c1 st1 r st3)).
      unfold config_refinement, weakestpre in *.
      sets_unfold in H.
      intros. apply H;auto.
  Qed. 

End config_refinement_rules.
End ConfigReineStatreRelMonad.


Module RelHoareNormalDenoAsbMonad.
Export ConfigReineStatreRelMonad.
Export normaldeno.

Definition valid_quadruples {Σₗ Σₕ A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem) (cₕ: program Σₕ A) (Q: A -> @binasrt Σₗ Σₕ) :=
  forall st1 st1', P (st1, st1') -> 
  forall st2, cₗ.(nrm) st1 st2 -> 
  (exists st2' a, cₕ st1' a st2' /\ Q a (st2, st2') ).

(* Alternative Definition of Relational Hoare Triples *)
Definition valid_RelTriples {Σₗ Σₕ A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: @denosem Σₗ) (Q: @relasrt Σₗ Σₕ (program Σₕ A)) :=
  forall st1 st1' (cₕ: (program Σₕ A)) , P (st1, st1', cₕ) -> 
  forall st2, cₗ.(nrm) st1 st2 -> ( exists st2' cₕ', ( st1', cₕ ) ↪ ( st2', cₕ' ) /\ Q (st2, st2', cₕ')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).


Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import MonadNotation.
  Local Open Scope monad.
  Local Open Scope asrt_scope.

Lemma quadruple2reltriple {A: Type}: forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ ↑ P && [ₕ cₕ ]ₕ ⟩ cₗ ⟨ EX r : A, ↑ (Q r) && [ₕ ret r ]ₕ  ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      unfold lift, exp, andp, Aspec.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & a & Hheval & HQ).
      do 2 eexists.
      split;eauto.
      unfold config_refinement.
      intros.
      unfold ret in H. destruct H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      unfold lift, exp, andp, Aspec.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & Hheval & a &  HQ & ?).
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      unfold_monad.  auto.
  Qed.

End reltriple_correct.

End RelHoareNormalDenoAsbMonad.



(* low -level use part of practical deno *)
Module RelHoareNormalDenoAsbMonad2.
Export ConfigReineStatreRelMonad.
Export practicaldeno.

Definition valid_quadruples {Σₗ Σₕ A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem) (cₕ: program Σₕ A) (Q: A -> @binasrt Σₗ Σₕ) :=
  forall st1 st1', P (st1, st1') -> 
  forall st2, cₗ.(nrm) st1 st2 -> 
  (exists st2' a, cₕ st1' a st2' /\ Q a (st2, st2') ).

(* Alternative Definition of Relational Hoare Triples *)
Definition valid_RelTriples {Σₗ Σₕ A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: @denosem Σₗ) (Q: @relasrt Σₗ Σₕ (program Σₕ A)) :=
  forall st1 st1' (cₕ: (program Σₕ A)) , P (st1, st1', cₕ) -> 
  forall st2, cₗ.(nrm) st1 st2 -> ( exists st2' cₕ', ( st1', cₕ ) ↪ ( st2', cₕ' ) /\ Q (st2, st2', cₕ')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).


Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import MonadNotation.
  Local Open Scope monad.
  Local Open Scope asrt_scope.

Lemma quadruple2reltriple {A: Type}: forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ ↑ P && [ₕ cₕ ]ₕ ⟩ cₗ ⟨ EX r : A, ↑ (Q r) && [ₕ ret r ]ₕ  ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      unfold lift, exp, andp, Aspec.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & a & Hheval & HQ).
      do 2 eexists.
      split;eauto.
      unfold config_refinement.
      intros.
      unfold ret in H. destruct H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      unfold lift, exp, andp, Aspec.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & Hheval & a &  HQ & ?).
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      unfold_monad.  auto.
  Qed.

End reltriple_correct.

End RelHoareNormalDenoAsbMonad2.
