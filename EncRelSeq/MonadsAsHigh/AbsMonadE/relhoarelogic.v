Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadErr.StateRelMonadErr.
From EncRelSeq.Basics Require Import basicasrt relasrt.
From EncRelSeq Require Export semantics errsem.

Local Open Scope sets_scope.

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

Module ConfigReineStatreRelMonadErr.

(* Configuration Refinement *)
Definition config_refinement {Σ A: Type} (g1 g2: (Σ * program Σ A)%type ) : Prop :=
  let '(σ1, c1) := g1 in
  let '(σ2, c2) := g2 in
  (forall r σ₃, c2.(nrm) σ2 r σ₃ -> c1.(nrm) σ1 r σ₃) /\ 
  (c2.(err) σ2 -> c1.(err) σ1 ).

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
    c.(nrm) σ1 a σ2 <->
    ( σ1, c ) ↪ ( σ2, ret a).
  Proof.
    intros; unfold config_refinement; simpl; unfold_monad; sets_unfold; intros.
    split;intros.
    - split. intros. destruct H0. subst;auto.
      tauto.
    - destruct H. auto.
  Qed.

  Lemma config_refinement_bind : forall (c1 :program Σ A) (c2: A -> program Σ B) (σ1 σ2: Σ) a ,
    c1.(nrm) σ1 a σ2 ->
    (σ1, bind c1 c2 ) ↪ ( σ2, c2 a).
  Proof.
    intros; unfold config_refinement; unfold_monad; simpl; sets_unfold; intros.
    split;intros.
    - eexists;eauto.
    - right.
    eexists;eauto.
  Qed.
  
End config_refinement_rules.
End ConfigReineStatreRelMonadErr.


Module RelHoarePracticalDenoAsbMonad.
Export ConfigReineStatreRelMonadErr.
Export practicaldeno.



Definition valid_quadruples {Σₗ Σₕ A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem) (cₕ: program Σₕ A) (Q: A -> @binasrt Σₗ Σₕ) :=
  forall st1 st1', P (st1, st1') -> (cₗ.(err) st1 -> cₕ.(err) st1')  /\
  forall st2, cₗ.(nrm) st1 st2 -> (cₕ.(err) st1' \/ 
  (exists st2' a, cₕ.(nrm) st1' a st2' /\ Q a (st2, st2') )).

(* Alternative Definition of Relational Hoare Triples *)
Definition valid_RelTriples {Σₗ Σₕ A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: @denosem Σₗ) (Q: @relasrt Σₗ Σₕ (program Σₕ A)) :=
  forall st1 st1' (cₕ: (program Σₕ A)) , P (st1, st1', cₕ) ->  (cₗ.(err) st1 -> cₕ.(err) st1') /\
  forall st2, cₗ.(nrm) st1 st2 -> (cₕ.(err) st1' \/ ( exists st2' cₕ', ( st1', cₕ ) ↪ ( st2', cₕ' ) /\ Q (st2, st2', cₕ'))).

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
      specialize (HQ _ _ HP) as [HQerr HQnrm].
      split;[auto | ].
      intros lst2 Hleval.
      specialize (HQnrm _ Hleval) as [ | (hst2 & a & Hheval & HQ)];[auto | right].
      unfold lift, exp.
      do 2 eexists.
      split;eauto.
      unfold config_refinement.
      split.
      { intros.
      unfold ret in H. destruct H. subst.
      auto. }
      intros.
      unfold ret in H. cbn in H. sets_unfold in H. contradiction.
    - unfold valid_RelTriples, valid_quadruples, lift.
      unfold lift, exp, andp, Aspec.
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

