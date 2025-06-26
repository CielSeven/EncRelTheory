 
From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonadErr.
From EncRelSeq.Basics Require Import semantics basicasrt.
From EncRelSeq.Basics Require Export hoarelogic.

Ltac any_nrm x ::=
  match type of x with
  | practicaldeno.denosem => exact (practicaldeno.nrm x)
  | program _ _ => exact (MonadErr.nrm x)
  end.



Ltac any_err x ::=
  match type of x with
  | practicaldeno.denosem => exact (practicaldeno.err x)
  | program _ _ => exact (MonadErr.err x)
  end.


Module RelHoarePracticalDenoAsbMonad.
Import practicaldeno.

Export HoarePracticalDeno.


Definition valid_quadruples {Σ₁ Σ₂: Type}  {A: Type} 
                            (P: @binasrt Σ₁ Σ₂) (c₁: denosem) (c₂: program Σ₂ A) (Q: A -> @binasrt Σ₁ Σ₂) :=
  forall st1 st1', P (st1, st1') -> (c₁.(err) st1 -> c₂.(err) st1') /\
  forall st2, c₁.(nrm) st1 st2 -> (c₂.(err) st1' \/ exists st2' r, c₂.(nrm) st1' r st2' /\ Q r (st2, st2') ).


Definition sem_eval {Σₕ A: Type} (σ₁ : Σₕ) (c₁: program Σₕ A) (σ₂ : Σₕ) (c₂: program Σₕ A): Prop :=
  (forall r σ₃, c₂.(nrm) σ₂ r σ₃ -> c₁.(nrm) σ₁ r σ₃) /\ 
  (c₂.(err) σ₂ -> c₁.(err) σ₁).

Notation " '(-' x , y '-)' '↪' '(-' u , z '-)' " := (sem_eval x y u z) (at level 70, no associativity).



Definition valid_RelTriples {Σ₁ Σ₂: Type} {A: Type}  
                            (P: @relasrt Σ₁ Σ₂ (program Σ₂ A)) (c₁: denosem) (Q: @relasrt Σ₁ Σ₂ (program Σ₂ A)) :=
  forall st1 st1' (c₂: (program Σ₂ A)) , P (st1, st1', c₂) -> (c₁.(err) st1 -> c₂.(err) st1') /\
  forall st2, c₁.(nrm) st1 st2 -> (c₂.(err) st1' \/ 
                            exists st2' c₂',  (-st1', c₂ -) ↪ (-st2', c₂' -)  /\ Q (st2, st2', c₂')).

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
      specialize (HQ _ _ HP) as [HQerr HQnrm].
      split;[auto | ].
      intros lst2 Hleval.
      specialize (HQnrm _ Hleval) as [ | (hst2 & a & Hheval & HQ)];[auto | right].
      unfold lift, exp.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      split.
      { intros.
      unfold ret in H. destruct H. subst.
      auto. }
      intros.
      unfold ret in H. cbn in H. sets_unfold in H. contradiction.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      specialize (HT lst1 hst1 _ (ltac:(split;auto))) as [HTerr HTnrm].
      split;[auto | ].
      intros lst2 Hleval.
      specialize (HTnrm _ Hleval) as [ | (hst2 & ? & Hheval & a &  HQ & ?)];[auto | right].
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      unfold ret. cbn. auto.
  Qed.

End reltriple_correct.

End RelHoarePracticalDenoAsbMonad.

