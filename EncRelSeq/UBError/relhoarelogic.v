(**
 * @file relhoarelogic.v
 * @import core semantics and basic assertions.
 * @brief Provides definitions and rules related to relational Hoare logic for reasoning about imperative programs equipped with a relational denotational semantics with error handling.
**)
Require Import Coq.Classes.RelationClasses.
From FP Require Import SetsFixedpoints.
From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt.
From EncRelSeq.UBError Require Import errsem hoarelogic.

Module ConfigReinePracticalDeno.
Export practicaldeno.
(* Configuration Refinement *)
Definition config_refinement {Σ: Type} (g1 g2: (Σ * @denosem Σ)%type ) : Prop :=
  let '(σ1, c1) := g1 in
  let '(σ2, c2) := g2 in
  (forall σ₃, c2.(nrm) σ2 σ₃ -> c1.(nrm) σ1 σ₃) /\ 
  (c2.(err) σ2 -> c1.(err) σ1 ).

Arguments config_refinement: simpl never.

Notation " g1 '↪' g2 " := (config_refinement g1 g2) (at level 28, left associativity).

#[export] Instance configrefine_reflexivity {Σ: Type}: Reflexive (@config_refinement Σ).
Proof.
  hnf. unfold config_refinement. intros [? ?]. intuition eauto. Qed. 
#[export] Instance configrefine_refinement_transivity {Σ: Type}: Transitive (@config_refinement Σ).
Proof.
  hnf. unfold config_refinement. intros [? ?] [? ?] [? ?]. intuition eauto. Qed. 


Section config_refinement_rules.
  Context {Σ: Type}.
  Import  PracticalDenoConstructs. 

  Lemma config_refinement_skip : forall (c: @denosem Σ) (σ1 σ2: Σ),
    (c.(nrm) σ1 σ2) <->
    ( σ1, c ) ↪ ( σ2, skip ).
  Proof.
    intros; unfold config_refinement, skip; simpl; sets_unfold; intros.
    split;intros.
    - split. intros. subst;auto.
      tauto.
    - destruct H. auto.
  Qed.

  Lemma config_refinement_seq : forall (c1 c2: @denosem Σ) (σ1 σ2: Σ),
    c1.(nrm) σ1 σ2 ->
    ( σ1, seq c1 c2 ) ↪ ( σ2, c2 ).
  Proof.
    intros; unfold config_refinement, seq; simpl;sets_unfold; intros.
    split;intros.
    - eexists;eauto.
    - right.
    eexists;eauto.
  Qed.
  
End config_refinement_rules.
End ConfigReinePracticalDeno.

(* Relational Hoare Logic for Normal Deno Semantics *)

Module RelHoarePracticalDeno.
Export ConfigReinePracticalDeno.

Definition valid_quadruples {Σₗ Σₕ: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem) (cₕ: denosem) (Q: @binasrt Σₗ Σₕ) :=
  forall st1 st1', P (st1, st1') -> (cₗ.(err) st1 -> cₕ.(err) st1') /\
  forall st2, cₗ.(nrm) st1 st2 -> (cₕ.(err) st1' \/ 
  exists st2', cₕ.(nrm) st1' st2' /\ Q (st2, st2') ).

(* Alternative Definition of Relational Hoare Triples *)
Definition valid_RelTriples {Σₗ Σₕ: Type} (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: @denosem Σₗ) (Q: @relasrt Σₗ Σₕ (@denosem Σₕ)) :=
  forall st1 st1' (cₕ: (@denosem Σₕ)) , P (st1, st1', cₕ) -> (cₗ.(err) st1 -> cₕ.(err) st1') /\
  forall st2, cₗ.(nrm) st1 st2 -> ( cₕ.(err) st1' \/ exists st2' cₕ', ( st1', cₕ ) ↪ ( st2', cₕ' ) /\ Q (st2, st2', cₕ')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).

Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import PracticalDenoConstructs.
  Local Open Scope asrt_scope.
  Lemma quadruple2reltriple : forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: @denosem Σₕ )  (Q :  @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ ↑ P && [ₕ cₕ ]ₕ ⟩ cₗ ⟨ ↑ Q && [ₕ skip ]ₕ ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      unfold andp,lift,Aspec in *.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      specialize (HQ _ _ HP) as [HQerr HQnrm].
      split;auto.
      intros lst2 Hleval.
      specialize (HQnrm _ Hleval) as [ | (hst2 & Hheval & HQ)];auto.
      right.
      unfold lift.
      do 2 eexists.
      split;eauto.
      unfold config_refinement.
      split.
      + intros.
        cbn in H.
        sets_unfold in H. subst.
        auto.
      + cbn. sets_unfold. tauto.  
    - unfold valid_RelTriples, valid_quadruples, lift, andp, Aspec.
      intros HT lst1 hst1 HP.
      specialize (HT lst1 hst1 _ (ltac:(split;auto))) as [HTerr HTnrm].
      split;auto.
      intros lst2 Hleval.
      specialize (HTnrm _ Hleval) as [ | (hst2 & ? & Hheval & HQ & ?)];[auto | right].
      subst.
      eexists.
      split;eauto.
      eapply Hheval.
      cbn. sets_unfold. auto.
  Qed.

End reltriple_correct.

End RelHoarePracticalDeno. 

Module RelHoarePracticalDenoRules.

Import HoarePracticalDeno.
Import RelHoarePracticalDeno.
  
Local Open Scope asrt_scope.

Section relhoarerules.

  Context {Σₗ Σₕ: Type}.

  Ltac destructs H := rel_destruct  Σₗ Σₕ (@denosem Σₕ) (@denosem Σₗ) H.

  Lemma relhoare_conseq: forall  (cₗ: @denosem Σₗ) (P P' Q Q':  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    P |-- P' ->
    Q' |-- Q ->
    ⊢ ⟨ P' ⟩ cₗ ⟨ Q' ⟩ ->
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP.
    specialize (H _ HP).
    specialize (H1 st1 st1' _ H) as [? H1].
    split;auto. 
    intros st2 Hleval.
    specialize (H1 _ Hleval) as [ | (st2' & cₕ' & Hheval & HQ)].
    left;auto.
    right.
    do 2 eexists. split;eauto.
  Qed.

  Lemma relhoare_conseq_pre: forall  (cₗ: @denosem Σₗ) (P P' Q:  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    P |-- P' ->
    ⊢ ⟨ P' ⟩ cₗ ⟨ Q ⟩ ->
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    eapply relhoare_conseq;[ | | eauto].
    auto.
    reflexivity.
  Qed.

  Lemma relhoare_conseq_post: forall  (cₗ: @denosem Σₗ) (P Q Q':  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    Q' |-- Q ->
    ⊢ ⟨ P ⟩ cₗ ⟨ Q' ⟩ ->
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    eapply relhoare_conseq;[ | | eauto].
    reflexivity.
    auto.
  Qed.

  (* Rht-ExIntro *)
  Lemma relhoare_exists_intro {A:Type}: forall (P: A -> @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: @denosem Σₗ) (Q:  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    (forall a, ⊢ ⟨ P a ⟩ cₗ ⟨ Q ⟩) ->
    ⊢ ⟨EX a,  P a ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP.
    destruct HP as [a HP].
    specialize (H a st1 st1' _ HP). auto.
  Qed.

  Import PracticalDenoConstructs.

  (* rule Rel-Seq *)
  Lemma relhoare_seq : forall (cₗ1 cₗ2: @denosem Σₗ) (P R Q:  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P ⟩ cₗ1 ⟨ R ⟩ ->
    ⊢ ⟨ R ⟩ cₗ2 ⟨ Q ⟩ ->
    ⊢ ⟨ P ⟩ (seq cₗ1 cₗ2) ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP. 
    specialize (H st1 st1' _ HP) as [? H].
    split.
    - intros Hlerr.
      cbn in Hlerr. sets_unfold in Hlerr. 
      destruct Hlerr as [ | (st2 & Hleval & Hlerr)];[ auto | ].
      specialize (H _ Hleval) as [ | (st2' & cₕ' & Hheval & HQ)];[auto | ].
      specialize (H0 _ _ _ HQ) as [? _].
      apply Hheval;auto.
    - intros st2 Hleval.
      destruct Hleval as [st3 [Hleval1 Hleval2] ].
      sets_unfold in Hleval1. sets_unfold in Hleval2.
      specialize (H st3 Hleval1) as [ | (st2' &  cₕ' & Hheval & HQ)];[auto | ].
      specialize (H0 _ _ _ HQ) as [? H0].
      specialize (H0 st2 Hleval2) as [ | (st3' &  cₕ'' & Hheval' & HQ')];[ left;apply Hheval;auto | ].
      right.
      do 2 eexists. split;[ | eauto].
      etransitivity; eauto.
  Qed.

  (* rule High-Focus *)
  Lemma relhoare_high_focus : forall (cₗ: @denosem Σₗ) (cₕ1 cₕ2: @denosem Σₕ) F P R Q,
    ⊢∃ {{P}} cₕ1 {{R}}  ->
    ⊢ ⟨ ⌊ F ⌋ && ⌈ R ⌉ && [ₕ cₕ2 ]ₕ ⟩ cₗ ⟨ Q ⟩ ->
    ⊢ ⟨ ⌊ F ⌋ && ⌈ P ⌉ && [ₕ seq cₕ1 cₕ2 ]ₕ ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP.
    apply decomposed_sat in HP.
    destruct HP as [HP1 [HP2 HP3]]. subst.
    specialize (H _ HP2) as [st3 [Hheval HR]].
    specialize (H0 st1 st3 _ (ltac:(apply decomposed_sat;auto))) as [? H0].
    split;auto.
    - intros. eapply seq_err2;eauto.
    - intros st2 Hleval.
      specialize (H0 _ Hleval) as [| ( st2' &  cₕ' & Hheval' & HQ)].
      + left.
        eapply seq_err2;eauto.
      + right.
        do 2 eexists. split;[ | eauto].
        etransitivity; eauto.
        apply config_refinement_seq;auto.
  Qed.

   (* rule Low-Focus *)
  Lemma relhoare_low_focus : forall (cₗ1 cₗ2: @denosem Σₗ) (cₕ: @denosem Σₕ) F P R Q,
    ⊢∀ {{P}} cₗ1 {{R}} ->
    ⊢ ⟨ ⌊ R ⌋ && ⌈ F ⌉ && [ₕ cₕ ]ₕ ⟩ cₗ2 ⟨ Q ⟩ ->
    ⊢ ⟨ ⌊ P ⌋ && ⌈ F ⌉ && [ₕ cₕ ]ₕ ⟩ (seq cₗ1 cₗ2) ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' ? HP. 
    apply decomposed_sat in HP.
    destruct HP as [HP1 [HP2 HP3]]. subst.
    specialize (H _ HP1) as [? H].
    split.
    - intros Hlerr.
      cbn in Hlerr. sets_unfold in Hlerr.
      destruct Hlerr as [ | (st2 & Hleval & Hlerr)];[contradiction |].
      specialize (H _ Hleval).
      specialize (H0 st2 st1' _ (ltac:(apply decomposed_sat;auto))) as [? H0].
      auto.
    - intros st2 Hleval. 
      destruct Hleval as [st3 [Hleval1 Hleval2] ].
      sets_unfold in Hleval1. sets_unfold in Hleval2.
      specialize (H _ Hleval1).
      specialize (H0 st3 st1' _ (ltac:(apply decomposed_sat;auto))) as [? H0].
      specialize (H0 st2 Hleval2) as [ | (st2' &  cₕ' & Hheval' & HQ)];[tauto | right;eauto].
  Qed.

  (* rule Rel-Wh *)
  Lemma relhoare_while : forall B (cₗ: @denosem Σₗ) (P: @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P && ⌊ B ⌋ ⟩ cₗ ⟨ P ⟩ ->
    ⊢ ⟨ P ⟩ (while B cₗ) ⟨ P && ⌊ notB B ⌋ ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *;intros.
    split.
    - unfold while; sets_unfold.
      unfold Lfix; cbn [nrm err];
      sets_unfold; unfold not;
      intros.
      destruct H1 as [n ?].
      revert st1 st1' cₕ H0 H1.
      induction n;intros.
      + contradiction.
      + simpl in H1. destructs H1.
        { subst.
          specialize (H st1 st1' cₕ (ltac:(unfold andp, Alst;split;auto))) as [Herr H].
          specialize (H _ H2) as [ | (st2' & cₕ' & ? & ?)];[auto | ].
          specialize (IHn σₗ0 _ cₕ' H3 H4).
          apply H. auto. }
        { subst.
          specialize (H st1 st1' cₕ (ltac:(unfold andp, Alst;split;auto))) as [Herr H].
          auto. }
    - unfold while; sets_unfold.
      unfold Lfix; cbn [nrm];
      sets_unfold; unfold not;
      intros.
      destruct H1 as [n ?].
      revert st1 st1' cₕ H0 H1.
      induction n;intros.
      + contradiction.
      + simpl in H1. destructs H1.
        { subst.
          specialize (H st1 st1' cₕ (ltac:(unfold andp, Alst;split;auto))) as [Herr H].
          specialize (H _ H2) as  [ | (st2' & cₕ' & ? & ?)];[tauto | ].
          specialize (IHn σₗ0 _ cₕ' H3 H4) as [? | (st3' & cₕ'' & ? & ?)].
          { left. apply H. auto. }
          { right.
            do 2 eexists.
            split;[ | eauto].
            etransitivity; eauto. } }
        { subst.
          right.
          exists st1', cₕ.
          split;[reflexivity |].
          cbv.
          auto. }
    Qed.


  End relhoarerules.

End RelHoarePracticalDenoRules.



