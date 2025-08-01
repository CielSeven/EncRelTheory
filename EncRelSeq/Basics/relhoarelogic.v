(**
  * @file relhoarelogic.v
  * @brief Defines and proves rules for relational Hoare logic based on relational denotational semantics.
  *
  * @details
  *   - config_refinement: Defines refinement relationn between configurations.
  *   - valid_quadruples: Direct definition of relational Hoare quadruples.
  *   - valid_RelTriples: An defintion of relational Hoare triples using configuration refinement.
  *   - Proves equivalence between the two formulations of relational judgements.
  *   - Includes proof rules for relational triples, including 
  *     consequence, sequencing, focusing (high/low), and while loops
  *)

Require Import Coq.Classes.RelationClasses.
From FP Require Import SetsFixedpoints.
From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt hoarelogic relasrt.

Local Open Scope sets_scope.

Module ConfigReineNormalDeno.
Export normaldeno.
(* Configuration Refinement *)
Definition config_refinement {Σ: Type} (g1 g2: (Σ * @denosem Σ)%type ) : Prop :=
  let '(σ1, c1) := g1 in
  let '(σ2, c2) := g2 in
  (forall σ₃, c2.(nrm) σ2 σ₃ -> c1.(nrm) σ1 σ₃).

Arguments config_refinement: simpl never.
Notation " g1 '↪' g2 " := (config_refinement g1 g2) (at level 28, left associativity).

#[export] Instance configrefine_reflexivity {Σ: Type}: Reflexive (@config_refinement Σ).
Proof.
  hnf. unfold config_refinement. intros. intuition eauto. Qed. 
#[export] Instance configrefine_refinement_transivity {Σ: Type}: Transitive (@config_refinement Σ).
Proof.
  hnf. unfold config_refinement. intros [? ?] [? ?] [? ?]. intuition eauto. Qed. 


Section config_refinement_rules.
  Context {Σ: Type}.
  Import  NormalDenoConstructs.

  Lemma config_refinement_skip : forall (c: @denosem Σ) (σ1 σ2: Σ),
    c.(nrm) σ1 σ2 <->
    ( σ1, c ) ↪ ( σ2, skip ).
  Proof.
    intros; unfold config_refinement, skip; simpl; sets_unfold; intros.
    split;intros;auto.
    subst;auto.
  Qed.

  Lemma config_refinement_seq : forall (c1 c2: @denosem Σ) (σ1 σ2: Σ),
    c1.(nrm) σ1 σ2 ->
    ( σ1, seq c1 c2 ) ↪ ( σ2, c2 ).
  Proof.
    intros; unfold config_refinement, seq; simpl;sets_unfold; intros.
    eexists;eauto.
  Qed.
  
  Import HoareNormalDeno.
  Theorem configrefine_decompose (c1 c2: @denosem Σ) (st1 st2: Σ):
    (st1, c1) ↪  (st2, c2) <->
    (forall X, st1 ∈ weakestpre c1 X -> st2 ∈ weakestpre c2 X).
  Proof.
    split;intros.
    - unfold config_refinement, weakestpre in *.
      sets_unfold. sets_unfold in H0.
      intros. eapply H0;auto.
    - specialize (H (fun st3 => c1.(nrm) st1 st3)).
      unfold config_refinement, weakestpre in *.
      sets_unfold in H.
      intros. apply H;auto.
  Qed. 

End config_refinement_rules.
End ConfigReineNormalDeno.

(* Relational Hoare Logic for Normal Deno Semantics *)

Module RelHoareNormalDeno.
Export ConfigReineNormalDeno.

Definition valid_quadruples {Σₗ Σₕ: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem) (cₕ: denosem) (Q: @binasrt Σₗ Σₕ) :=
  forall st1 st1', P (st1, st1') -> 
  forall st2, cₗ.(nrm) st1 st2 -> 
  (exists st2', cₕ.(nrm) st1' st2' /\ Q (st2, st2') ).

(* Alternative Definition of Relational Hoare Triples *)
Definition valid_RelTriples {Σₗ Σₕ: Type} (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: @denosem Σₗ) (Q: @relasrt Σₗ Σₕ (@denosem Σₕ)) :=
  forall st1 st1' (cₕ: (@denosem Σₕ)) , P (st1, st1', cₕ) -> 
  forall st2, cₗ.(nrm) st1 st2 -> ( exists st2' cₕ', ( st1', cₕ ) ↪ ( st2', cₕ' ) /\ Q (st2, st2', cₕ')).

Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).

Section reltriple_correct.
  Context {Σₗ Σₕ: Type}.
  Import NormalDenoConstructs.
  Local Open Scope asrt_scope.
  Lemma quadruple2reltriple : forall (P: @binasrt Σₗ Σₕ ) (cₗ: (@denosem Σₗ))  (cₕ: @denosem Σₕ )  (Q :  @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ ↑ P && [cₕ ]ₕ ⟩ cₗ ⟨ ↑ Q && [skip ]ₕ ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      unfold lift, Aspec, andp in *.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & Hheval & HQ).
      do 2 eexists.
      split;eauto.
      unfold config_refinement.
      intros.
      cbn in H.
      sets_unfold in H. subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      unfold lift, Aspec, andp in *.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & Hheval & HQ & ?).
      subst.
      eexists.
      split;eauto.
      eapply Hheval.
      cbn. sets_unfold. auto.
  Qed.

End reltriple_correct.

End RelHoareNormalDeno. 

Module RelHoareNormalDenoRules.


Import HoareNormalDeno.
Import RelHoareNormalDeno.
  
Local Open Scope asrt_scope.

Section relhoarerules.

  Context {Σₗ Σₕ: Type}.

  Ltac destructs H := rel_destruct  Σₗ Σₕ (@denosem Σₕ) (@denosem Σₗ) H.

  (* Define the base rules for low and high languages *)


  Lemma relhoare_conseq: forall  (cₗ: @denosem Σₗ) (P P' Q Q':  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    P |-- P' ->
    Q' |-- Q ->
    ⊢ ⟨ P' ⟩ cₗ ⟨ Q' ⟩ ->
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP st2 Hleval.
    specialize (H _ HP).
    specialize (H1 st1 st1' _ H st2 Hleval) as (st2' &  cₕ' & Hheval & HQ).
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
    intros st1 st1' cₕ HP st2 Hleval.
    destruct HP as [a HP].
    specialize (H a st1 st1' _ HP st2 Hleval) as (st2' &  cₕ' & Hheval & HQ).
    do 2 eexists. split;eauto.
  Qed.

  Import NormalDenoConstructs.

  (* rule Rel-Seq *)
  Lemma relhoare_seq : forall (cₗ1 cₗ2: @denosem Σₗ) (P R Q:  @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P ⟩ cₗ1 ⟨ R ⟩ ->
    ⊢ ⟨ R ⟩ cₗ2 ⟨ Q ⟩ ->
    ⊢ ⟨ P ⟩ (seq cₗ1 cₗ2) ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP st2 Hleval.
    destruct Hleval as [st3 [Hleval1 Hleval2] ].
    specialize (H st1 st1' _ HP st3 Hleval1) as (st2' &  cₕ' & Hheval & HQ).
    specialize (H0 st3 st2' _ HQ st2 Hleval2) as (st3' &  cₕ'' & Hheval' & HQ').
    do 2 eexists. split;[ | eauto].
    etransitivity; eauto.
  Qed.

  (* rule High-Focus *)
  Lemma relhoare_high_focus : forall (cₗ: @denosem Σₗ) (cₕ1 cₕ2: @denosem Σₕ) F P R Q,
    ⊢∃ {{P}} cₕ1 {{R}}  ->
    ⊢ ⟨ ⌊ F ⌋ && ⌈ R ⌉ && [cₕ2]ₕ ⟩ cₗ ⟨ Q ⟩ ->
    ⊢ ⟨ ⌊ F ⌋ && ⌈ P ⌉ && [seq cₕ1 cₕ2]ₕ ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' cₕ HP st2 Hleval.
    apply decomposed_sat in HP.
    destruct HP as [HP1 [HP2 HP3]]. subst.
    specialize (H _ HP2) as [st3 [Hheval HR]].
    specialize (H0 st1 st3 _ (ltac:(apply decomposed_sat;auto)) st2 Hleval) as (st2' &  cₕ' & Hheval' & HQ).
    do 2 eexists. split;[ | eauto].
    etransitivity; eauto.
    apply config_refinement_seq;auto.
  Qed.

   (* rule Low-Focus *)
  Lemma relhoare_low_focus : forall (cₗ1 cₗ2: @denosem Σₗ) (cₕ: @denosem Σₕ) F P R Q,
    ⊢∀ {{P}} cₗ1 {{R}} ->
    ⊢ ⟨ ⌊ R ⌋ && ⌈ F ⌉ && [cₕ ]ₕ ⟩ cₗ2 ⟨ Q ⟩ ->
    ⊢ ⟨ ⌊ P ⌋ && ⌈ F ⌉ && [cₕ ]ₕ ⟩ (seq cₗ1 cₗ2) ⟨ Q ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 st1' ? HP st2 Hleval.
    apply decomposed_sat in HP.
    destruct HP as [HP1 [HP2 HP3]]. subst.
    destruct Hleval as [st3 [Hleval1 Hleval2] ].
    sets_unfold in Hleval1. sets_unfold in Hleval2.
    specialize (H _ HP1 _ Hleval1).
    specialize (H0 st3 st1' _ (ltac:(apply decomposed_sat;auto)) st2 Hleval2) as (st2' &  cₕ' & Hheval' & HQ).
    do 2 eexists. split; eauto.
  Qed.

  (* rule Rel-Wh *)
  Lemma relhoare_while : forall B (cₗ: @denosem Σₗ) (P: @relasrt Σₗ Σₕ (@denosem Σₕ)),
    ⊢ ⟨ P && ⌊ B ⌋ ⟩ cₗ ⟨ P ⟩ ->
    ⊢ ⟨ P ⟩ (while B cₗ) ⟨ P && ⌊ notB B ⌋ ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *;intros.
    revert H1.
    unfold while; sets_unfold.
    unfold Lfix; cbn [nrm];
    sets_unfold; unfold not;
    intros.
    destruct H1 as [n ?].
    revert st1 st1' cₕ H0 H1.
    induction n;intros.
    + contradiction.
    + simpl in H1. destructs H1.
      { subst.
        specialize (H st1 st1' cₕ (ltac:(unfold andp, Alst;split;auto)) _ H2) as (st2' & cₕ' & ? & ?).
        specialize (IHn σₗ0 _ cₕ' H3 H4) as (st3' & cₕ'' & ? & ?).
        do 2 eexists.
        split;[ | eauto].
        etransitivity; eauto.  }
      { subst.
        exists st1', cₕ.
        split;[reflexivity |].
        cbv.
        auto. }
  Qed.

  Lemma vertical_composition_functional_correctness: forall
    (P: @binasrt Σₗ Σₕ) (cₗ: denosem) (cₕ: denosem) (Q:  @binasrt Σₗ Σₕ) (Pₕ Qₕ: @asrt Σₕ),
    ⊢ ⟨ ↑ P && [cₕ ]ₕ ⟩ cₗ ⟨ ↑ Q && [skip ]ₕ ⟩ ->
    ⊢∀ {{ Pₕ }} cₕ {{ Qₕ }} ->
    ⊢∀ {{ P ⋈_π Pₕ }} cₗ {{ Q ⋈_π Qₕ }}.
  Proof.
    intros.
    unfold valid_RelTriples, valid_triple in *.
    intros st1 HP.
    destruct HP as [hst1 [? [HP [? HPH]]]]. subst x.
    specialize (H st1 hst1 cₕ (ltac:(unfold lift, Aspec, andp;split;auto))).
    intros st2 Hleval.
    specialize (H _ Hleval) as (hst2 & cₕ' & Hheval & HQ).
    unfold lift, Aspec, andp in HQ. destruct HQ as [HQ ?]. subst.
    apply config_refinement_skip in Hheval.
    specialize (H0 _ HPH _ Hheval).
    exists hst2, hst2.
    cbv. auto.
  Qed.

  Lemma vertical_composition_refinement {Σ₁ Σ₂ Σ₃: Type}: forall
    (c₁: denosem) (c₂: denosem) (c₃:denosem) (P1 Q1: @binasrt Σ₁ Σ₂) (P2 Q2: @binasrt Σ₂ Σ₃) ,
    ⊢ ⟨ ↑ P1 && [c₂ ]ₕ ⟩ c₁ ⟨ ↑ Q1 && [skip ]ₕ ⟩ ->
    ⊢ ⟨ ↑ P2 && [c₃ ]ₕ ⟩ c₂ ⟨ ↑ Q2 && [skip ]ₕ ⟩ ->
    ⊢ ⟨ ↑ (P1 ⋈ P2) && [c₃ ]ₕ ⟩ c₁ ⟨ ↑ (Q1 ⋈ Q2) && [skip ]ₕ ⟩.
  Proof.
    intros.
    unfold valid_RelTriples in *.
    intros st1 hst1 ? HP.
    unfold comp, lift, andp, Aspec in HP.
    destruct HP as [[mst1 [HP1 HP2]] ?]. subst.
    specialize (H st1 mst1 c₂ (ltac:(unfold lift, Aspec, andp;split;auto))).
    intros st2 Hleval.
    specialize (H _ Hleval) as (mst2 & ? & Hmeval & HQ1).
    unfold lift, Aspec, andp in HQ1. destruct HQ1 as [HQ1 ?]. subst.
    apply config_refinement_skip in Hmeval.
    specialize (H0 mst1 hst1 c₃ (ltac:(unfold lift, Aspec, andp;split;auto))).
    specialize (H0 _ Hmeval) as (hst2 & ? & Hheval & HQ2).
    unfold lift, Aspec, andp in HQ2. destruct HQ2 as [HQ2 ?]. subst.
    exists hst2, skip.
    split;auto.
    unfold andp, lift, Aspec. split;auto.
    exists mst2. auto.
  Qed.

End relhoarerules.  
End RelHoareNormalDenoRules.



