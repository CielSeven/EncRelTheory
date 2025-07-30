From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt hoarelogic relhoarelogic 
                                     encdefs safeexec_lib encrel.


Module NormalDenoEncRules.
Import normaldeno.
Import EncNormalDeno.

Local Open Scope asrt_scope. 

(**********************************************************************************)
(*   encoded hoare rules                                                          *)
(**********************************************************************************)

Import HoareNormalDeno NormalDenoConstructs.
Import HoareNormalDenoRules.
Import RelHoareNormalDeno.
Import RelHoareNormalDenoRules.


  Section  encrules.
  Context {Σₗ Σₕ: Type}.
  Ltac destructs H := rel_destruct Σₗ Σₕ (@denosem Σₕ) (@denosem Σₗ) H.



(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)

  Lemma  reltriple_triple_equiv1 : forall (P: @asrt Σₗ) Ps (s: @denosem Σₕ) c Q,
    ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ s ]ₕ ⟩ c ⟨ Q ⟩ <->
    (forall X, ⊢∀ {{!! Exec Ps s X && P}} c {{[|Q|](X)}}).
  Proof.
    intros;split.
    - intros. apply encoding_correctness in H.
    specialize (H X). simpl_ldefs.
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_2 (encode_decomposed X P Ps s)).
    cbv. auto.
    - intros. apply encoding_correctness.
      unfold valid_reltriple, valid_relT; intros.
      specialize (H X).
      eapply hoare_conseq;eauto.
      apply (logic_equiv_derivable1_1 (encode_decomposed X P Ps s)).
      cbv. auto.
  Qed.

  Lemma  reltriple_triple_equiv {A: Type}: forall (P: @asrt Σₗ) Ps (s: @denosem Σₕ) c B Q Ps',
    ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ s ]ₕ ⟩ c ⟨EX (a:A), !! (B a) && ⌊ Q a ⌋ && ⌈ Ps' a⌉ && [ skip ]ₕ ⟩ <->
    (forall X : Σₕ -> Prop,
    ⊢∀ {{!! Exec Ps s X && P}} c {{EX a, !! Exec (Ps' a) skip X && !! (B a) && (Q a)}}).
  Proof.
    intros;split.
    - intros.
      apply encoding_correctness in H.
    specialize (H X).  simpl_ldefs. 
    eapply hoare_conseq;eauto.
    eapply (logic_equiv_derivable1_2 (encode_decomposed X P Ps s)).
    apply logic_equiv_derivable1_1.
    apply encode_normal_form.
    - intros. apply encoding_correctness.
      unfold valid_reltriple, valid_relT; intros.
      specialize (H X). 
      eapply hoare_conseq;eauto.
      apply (logic_equiv_derivable1_1 (encode_decomposed X P Ps s)).
      apply logic_equiv_derivable1_2.
      apply encode_normal_form.
  Qed.

  Lemma high_focus_as_conseqpre (cₗ: @denosem Σₗ) (cₕ1 cₕ2: @denosem Σₕ) F P R Q:
    forall X,
    ⊢∃ {{P}} cₕ1 {{R}}  ->
    ⊢∀ {{!! Exec R cₕ2 X && F}} cₗ {{[|Q|](X)}} ->
    ⊢∀ {{!! Exec P (seq cₕ1 cₕ2) X && F}} cₗ {{[|Q|](X)}}.
  Proof.
    intros.
    eapply hoare_conseq_pre;[ | eauto].
    apply derivable1_andp_mono;[ | reflexivity].
    apply coq_prop_imply.
    eapply highstepseq_derive;eauto.
  Qed.

  Lemma low_focus_as_seq (cₗ1 cₗ2: @denosem Σₗ) (cₕ: @denosem Σₕ) F P R Q:
    forall X,
    ⊢∀ {{P}} cₗ1 {{R}}  ->
    ⊢∀ {{!! Exec F cₕ X && R}} cₗ2 {{[|Q|](X)}} ->
    ⊢∀ {{!! Exec F cₕ X && P}} (seq cₗ1 cₗ2) {{[|Q|](X)}}.
  Proof.
    intros.
    eapply hoare_Seq;eauto.
    eapply hoare_coqprop_preintro.
    intros.
    eapply hoare_coqprop_postintro;auto.
  Qed.

End encrules.


Section composition_rules.

Lemma comp_fc_as_conseq {Σₗ Σₕ: Type}:forall 
  (P: @binasrt Σₗ Σₕ) (cₗ: denosem) (cₕ: denosem) (Q:  @binasrt Σₗ Σₕ) (Pₕ Qₕ: @asrt Σₕ),
  ((forall X, ⊢∀ {{ [|↑ P && [cₕ ]ₕ|](X) }} cₗ {{ [|↑ Q && [skip ]ₕ|](X) }})) -> 
  ⊢∀ {{ Pₕ }} cₕ {{ Qₕ }} ->
  ⊢∀ {{ P ⋈_π Pₕ }} cₗ {{ Q ⋈_π Qₕ }}.
Proof.
  intros * HRT HHT.
  eapply hoare_conseq_pre.  
  { apply (logic_equiv_derivable1_2 (comp_proj_equiv _ _ )). }
  eapply hoare_exists_intro; intros σₕ.
  eapply hoare_coqprop_preintro. intros HPH.
  specialize (HRT (fun (x: Σₕ) => (nrm cₕ) σₕ x)).
  eapply hoare_conseq;eauto.
  - intros st1 ?.
    unfold encode_asrt, lift, basicasrt.andp, Aspec. simpl.
    do 2 eexists. split;[ | eauto].
    unfold weakestpre. sets_unfold. 
    intros. auto.
  - intros st1 HQ.
    unfold encode_asrt, lift, basicasrt.andp, Aspec in HQ.
    destruct HQ as [σₕ' [cₕ' [? [? ?]]]]. subst. simpl_hdefs.
    rewrite weakestpre_skip in H. sets_unfold  in H.
    specialize (HHT _ HPH _ H).
    do 2 eexists. cbv. split;eauto.
Qed. 
Lemma comp_fc_as_conseq_convenient {Σₗ Σₕ U V: Type}:forall 
  (storeLowPre: U -> @asrt Σₗ) (storeHighPre: U -> @asrt Σₕ) (cₗ: denosem) (cₕ: denosem) 
  (storeLowPost: V -> @asrt Σₗ) (storeHighPost: V -> @asrt Σₕ) 
  (B1: U -> Prop) (B2: V -> Prop),
  ((forall X, ⊢∀ {{ EX u, !! (Exec (storeHighPre u) cₕ X) && (storeLowPre u) }} 
                cₗ {{ EX v, !! (Exec (storeHighPost v) (skip) X) && (storeLowPost v) }})) -> 
  ⊢∀ {{ EX u, !! (B1 u) && (storeHighPre u) }} cₕ 
      {{(fun st => forall v, storeHighPost v st -> B2 v)}} ->
  (forall u, (B1 u) -> exists σₕ, (storeHighPre u σₕ)) ->
  ⊢∀ {{ EX u, !! (B1 u) && (storeLowPre u)}} cₗ {{ EX v, !! (B2 v) && (storeLowPost v) }}.
Proof.
  intros * HRT HHT Hinhabitant.
  eapply hoare_exists_intro; intros u.
  eapply hoare_coqprop_preintro. intros HPH.
  specialize (Hinhabitant u HPH) as [σₕ HHpre].
  specialize (HRT (fun (x: Σₕ) => (nrm cₕ) σₕ x)).
  eapply hoare_conseq;eauto.
  - intros st1 ?.
    unfold basicasrt.andp, basicasrt.exp, basicasrt.coq_prop, Exec. simpl.
    eexists. split;[ | eauto].
    unfold weakestpre. sets_unfold.
    eexists. split; eauto. 
  - intros st1 HQ.
    unfold basicasrt.andp, basicasrt.exp, basicasrt.coq_prop, Exec in HQ. simpl in HQ.
    destruct HQ as [v [HHQ HQ]]. 
    destruct HHQ as [σₕ' [? ?]].
    rewrite weakestpre_skip in H0. sets_unfold  in H0.
    assert ((EX u : U, !! B1 u && storeHighPre u) σₕ).
    { unfold basicasrt.andp, basicasrt.exp, basicasrt.coq_prop. eexists. eauto.  }
    specialize (HHT _ H1 _ H0).
    exists v.
    specialize (HHT _ H).
    cbv. split;auto.
Qed.

Lemma comp_refine_as_conseq  {Σ₁ Σ₂ Σ₃: Type}: forall
    (c₁: denosem) (c₂: denosem) (c₃:denosem) (P1 Q1: @binasrt Σ₁ Σ₂) (P2 Q2: @binasrt Σ₂ Σ₃) ,
    (forall X, ⊢∀ {{[|↑ P1 && [c₂ ]ₕ|](X)}} c₁ {{[|↑ Q1 && [skip ]ₕ|](X)}}) ->
    (forall X, ⊢∀ {{[|↑ P2 && [c₃ ]ₕ|](X)}} c₂ {{[|↑ Q2 && [skip ]ₕ|](X)}}) ->
    forall X, ⊢∀ {{[|↑ (P1 ⋈ P2) && [c₃ ]ₕ|](X)}} c₁ {{[|↑ (Q1 ⋈ Q2) && [skip ]ₕ|](X)}}.
Proof.
  intros * Hr Hr0 X.
  eapply hoare_conseq_pre with (P':= (EX σ₂, (fun σₗ : Σ₁ =>
    exists (σₕ : Σ₃) (cₕ : denosem), safe σₕ cₕ X /\
    (P1 (σₗ, σ₂) /\ P2 (σ₂, σₕ)) /\ cₕ = c₃))).
  { unfold lift ,encode_asrt, comp, Aspec, derivable1, exp. simpl_hdefs. 
    intros σ₁ H. destruct H as (? & ? & ? &  (? & ? & ?) & ?). 
    do 3 eexists. split;eauto. }
  apply hoare_exists_intro.
  intros σ₂.
  specialize (Hr0 X).
  pose proof (comp_fc_as_conseq _ _ _ _ _ _ Hr Hr0).
  eapply hoare_conseq;eauto.
  - (* pre *)
    unfold lift, Aspec, andp, encode_asrt, comp_proj, comp, derivable1, proj1. simpl.
    intros.
    destruct H0 as (? & ? & ? &  (? & ?) & ?).
    subst x0.
    unfold safe in H0. simpl_hdefs. sets_unfold in H0. sets_unfold. 
    do 2 eexists.
    split;eauto.
    split;eauto.
  - (* post *)
    unfold lift, Aspec, andp, encode_asrt, comp_proj, comp, derivable1, proj1. 
    intros.
    destruct H0 as (? & ? & (? & ? & ? & ? & ? & ? & ?)).
    subst x0 x2. simpl_hdefs. 
    do 2 eexists.
    split;eauto.
Qed.


End  composition_rules.
End NormalDenoEncRules.
