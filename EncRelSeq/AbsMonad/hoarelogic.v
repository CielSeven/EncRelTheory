 
From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From EncRelSeq.Basics Require Import basicasrt.
From EncRelSeq.Basics Require Export semantics hoarelogic.

(*************************************************************************************************************)
(**************** rel hoare logic based on normal semantics                    *******************************)
(*************************************************************************************************************)
Module RelHoareNormalDenoAsbMonad.
Export HoareNormalDeno.

Definition valid_quadruples {Σ₁ Σ₂: Type}  {A: Type} 
                            (P: @binasrt Σ₁ Σ₂) (c₁: denosem) (c₂: program Σ₂ A) (Q: A -> @binasrt Σ₁ Σ₂) :=
  forall st1 st1', P (st1, st1') -> 
  forall st2, c₁.(nrm) st1 st2 -> (exists st2' r, c₂ st1' r st2' /\ Q r (st2, st2') ).


Definition sem_eval {Σₕ A: Type} (σ₁ : Σₕ) (c₁: program Σₕ A) (σ₂ : Σₕ) (c₂: program Σₕ A): Prop :=
  (forall r σ₃, c₂ σ₂ r σ₃ -> c₁ σ₁ r σ₃).

Notation " '(-' x , y '-)' '↪' '(-' u , z '-)' " := (sem_eval x y u z) (at level 70, no associativity).



Definition valid_RelTriples {Σ₁ Σ₂: Type} {A: Type}  
                            (P: @relasrt Σ₁ Σ₂ (program Σ₂ A)) (c₁: denosem) (Q: @relasrt Σ₁ Σ₂ (program Σ₂ A)) :=
  forall st1 st1' (c₂: (program Σ₂ A)) , P (st1, st1', c₂) ->
  forall st2, c₁.(nrm) st1 st2 ->(exists st2' c₂',  (-st1', c₂ -) ↪ (-st2', c₂' -)  /\ Q (st2, st2', c₂')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).


Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import MonadNotation.
  Local Open Scope monad.
  Local Open Scope asrt_scope.
Lemma quadruple2reltriple {A: Type}: forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ EX r : A, lift (Q r) (return r) ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & a & Hheval & HQ).
      unfold lift, exp.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      intros.
      unfold ret in H. destruct H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
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



(*************************************************************************************************************)
(**************** rel hoare logic based on practical semantics                  *******************************)
(*************************************************************************************************************)
Module HoarePracticalDeno2.


Export practicaldeno.

Definition valid_triple {Σ: Type}: @HT_validity Σ (@denosem Σ) :=
  fun P c Q =>
  forall st1, P st1 -> 
  forall st2, c.(nrm) st1 st2 -> Q st2.

Local Open Scope asrt_scope.  
Lemma hoare_conseq {Σ: Type}: forall c (P P' Q Q': @asrt Σ),
P |-- P' ->
Q' |-- Q ->
valid_triple P' c Q' ->
valid_triple P c Q.
Proof.
  unfold valid_triple. simpl. intros * HP' HQ' HT.
  intros * HP.
  specialize (HT _ (HP' _ HP)) as HT.
  intros * Heval.
  specialize (HT _ Heval).
  eapply HQ';eauto.
Qed.

Notation " '⊢∀' '{{' P '}}' c {{ Q '}}'" := (valid_triple P c  Q) (at level 71, no associativity).
End HoarePracticalDeno2.


Module RelHoareNormalDenoAsbMonad2.
Export HoarePracticalDeno2.



Definition valid_quadruples {Σ₁ Σ₂: Type}  {A: Type} 
                            (P: @binasrt Σ₁ Σ₂) (c₁: denosem) (c₂: program Σ₂ A) (Q: A -> @binasrt Σ₁ Σ₂) :=
  forall st1 st1', P (st1, st1') -> 
  forall st2, c₁.(nrm) st1 st2 -> (exists st2' r, c₂ st1' r st2' /\ Q r (st2, st2') ).


Definition sem_eval {Σₕ A: Type} (σ₁ : Σₕ) (c₁: program Σₕ A) (σ₂ : Σₕ) (c₂: program Σₕ A): Prop :=
  (forall r σ₃, c₂ σ₂ r σ₃ -> c₁ σ₁ r σ₃).

Notation " '(-' x , y '-)' '↪' '(-' u , z '-)' " := (sem_eval x y u z) (at level 70, no associativity).



Definition valid_RelTriples {Σ₁ Σ₂: Type} {A: Type}  
                            (P: @relasrt Σ₁ Σ₂ (program Σ₂ A)) (c₁: denosem) (Q: @relasrt Σ₁ Σ₂ (program Σ₂ A)) :=
  forall st1 st1' (c₂: (program Σ₂ A)) , P (st1, st1', c₂) ->
  forall st2, c₁.(nrm) st1 st2 ->(exists st2' c₂',  (-st1', c₂ -) ↪ (-st2', c₂' -)  /\ Q (st2, st2', c₂')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).


Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import MonadNotation.
  Local Open Scope monad.
  Local Open Scope asrt_scope.
Lemma quadruple2reltriple {A: Type}: forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ EX r : A, lift (Q r) (return r) ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & a & Hheval & HQ).
      unfold lift, exp.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      intros.
      unfold ret in H. destruct H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & Hheval & a &  HQ & ?).
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      unfold_monad. auto.
  Qed.

End reltriple_correct.

End RelHoareNormalDenoAsbMonad2.

