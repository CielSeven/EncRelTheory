From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt hoarelogic encdefs encrel.
From EncRelSeq.UBError Require Import errsem hoarelogic encrel.
From EncRelSeq.MonadsAsHigh.AbsMonad Require Import relhoarelogic.


Module EncNormalDenoAbsMonad.
Import normaldeno.
Import HoareNormalDeno.
Import RelHoareNormalDenoAsbMonad.

Definition valid_reltriple {Σₗ Σₕ A: Type}:= valid_relT Σₗ Σₕ (@denosem Σₗ) (program Σₕ A) (A -> Σₕ -> Prop).

Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).

(*************************************************************************************************************)
(*******************************     soundness proof for valid_reltriple    **********************************)
(*************************************************************************************************************)

Import MonadNotation.
Local Open Scope monad.
Local Open Scope asrt_scope.
Section normal_validity_soundness.
  Context {Σₗ Σₕ: Type}.

  Theorem encoding_correctness : forall {A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: denosem)  (Q :  @relasrt Σₗ Σₕ (program Σₕ A)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    unfold valid_reltriple, valid_relT; simpl_ldefs;simpl_hdefs.
    intros;split.
    - unfold valid_RelTriples, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *. simpl_hdefs.
      destruct HP as (σₕ & cₕ &  Hhnrm & HP).
      specialize (HT _ _ _ HP) as Hnrm.
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as (σₕ' & cₕ' & Hheval  & HQ).
      do 2 eexists. split;[ | eauto].
      unfold StateRelHoare.weakestpre in *.
      sets_unfold. sets_unfold in Hhnrm. 
      intros.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun r x => cₕ σₕ r x) st1).
        intros st2 Heval.
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ σₕ r x)) st1).
        { unfold encode_asrt. simpl_hdefs.
          do 2 eexists. split;[ | eauto].
          unfold StateRelHoare.weakestpre; sets_unfold. auto. 
        }
        specialize (HT H _ Heval). clear H.
        unfold encode_asrt in *. simpl_hdefs. unfold StateRelHoare.weakestpre in *. sets_unfold in HT.
        destruct HT as [σₕ' [cₕ' [? ?]]];subst.
        do 2 eexists.
        split;eauto.
  Qed. 

  Theorem quadruple_conrrectness : forall {A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ ↑ P && [cₕ ]ₕ ⟩ cₗ ⟨ EX r : A, ↑ (Q r) && [ret r]ₕ ⟩.
  Proof.
    intros.
    split;intros.
    eapply encoding_correctness.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    apply encoding_correctness;auto.
  Qed.

  Section absnoret.
     Lemma quadruple2reltriple_noret : forall  (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ unit)  (Q :  @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{fun _ => Q}} <-> ⊢ₑ ⟨ ↑ P && [cₕ ]ₕ ⟩ cₗ ⟨ ↑ (Q) && [ret tt]ₕ ⟩.
  Proof.
    intros.
    etransitivity.
    apply quadruple_conrrectness.
    unfold valid_reltriple, valid_relT; simpl_ldefs;simpl_hdefs.
    split;intros.
    - eapply hoare_conseq_post;eauto.
      apply encode_derives.
      apply shallow_exp_left.
      intros x. destruct x.
      reflexivity.
    - eapply hoare_conseq_post;eauto.
      apply encode_derives.
      eapply shallow_exp_right.
      reflexivity.
  Qed.
    
  End absnoret.
  
End normal_validity_soundness.


End  EncNormalDenoAbsMonad.

Module NormalDenoAbsMonadEncRules.

Import normaldeno.
Import EncNormalDenoAbsMonad.

Local Open Scope asrt_scope. 

(**********************************************************************************)
(*   encoded hoare rules                                                          *)
(**********************************************************************************)

Import HoareNormalDeno NormalDenoConstructs.
Import HoareNormalDenoRules.
Import RelHoareNormalDenoAsbMonad.


  Section  encrules.
  Context {Σₗ Σₕ: Type}.
  Ltac destructs H := rel_destruct Σₗ Σₕ (@denosem Σₕ) (@denosem Σₗ) H.



(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)

  Lemma  reltriple_triple_equiv1 {A:Type}: forall (P: @asrt Σₗ) Ps (s: program Σₕ A) c Q,
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

  Lemma  reltriple_triple_equiv {A R: Type}: forall (P: @asrt Σₗ) Ps (s: program Σₕ R) c B Q Ps',
    ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ s ]ₕ ⟩ c ⟨EX (r: R) (a:A), !! (B a r) && ⌊ Q a r ⌋ && ⌈ Ps' a r⌉ && [ ret r ]ₕ ⟩ <->
    (forall X : R -> Σₕ -> Prop,
    ⊢∀ {{!! Exec Ps s X && P}} c {{EX r a, !! Exec (Ps' a r) (ret r) X && !! (B a r) && (Q a r)}}).
  Proof.
    intros;split.
    - intros.
      apply encoding_correctness in H.
    specialize (H X).  simpl_ldefs. 
    eapply hoare_conseq;eauto.
    eapply (logic_equiv_derivable1_2 (encode_decomposed X P Ps s)).
    apply logic_equiv_derivable1_1.
    eapply logic_equiv_trans.
    apply logic_equiv_symm; apply (encode_exp_equiv _ _ ).
    apply ex_logic_euiqv_elim_both;intros r.
    apply encode_normal_form.
    - intros. apply encoding_correctness.
      unfold valid_reltriple, valid_relT; intros.
      specialize (H X). 
      eapply hoare_conseq;eauto.
      apply (logic_equiv_derivable1_1 (encode_decomposed X P Ps s)).
      apply logic_equiv_derivable1_2.
      eapply logic_equiv_trans.
      apply logic_equiv_symm; apply (encode_exp_equiv _ _ ).
      apply ex_logic_euiqv_elim_both;intros r.
      apply encode_normal_form.
  Qed.

  
  Lemma high_focus_as_conseqpre {A B: Type} (cₗ: @denosem Σₗ) (cₕ1: program Σₕ A) (cₕ2: A -> program Σₕ B) F P R Q:
    forall X a,
    StateRelHoare.valid_angelic_triple P cₕ1 (fun r σ => r = a /\ R σ) ->
    ⊢∀ {{!! Exec R (cₕ2 a) X && F}} cₗ {{[|Q|](X)}} ->
    ⊢∀ {{!! Exec P (bind cₕ1 cₕ2) X && F}} cₗ {{[|Q|](X)}}.
  Proof.
    intros.
    eapply hoare_conseq_pre;[ | eauto].
    apply derivable1_andp_mono;[ | reflexivity].
    apply coq_prop_imply.
    eapply highstepbind_derive.
    eapply hs_eval_equiv_angelic_triple;auto.
  Qed.

  Lemma low_focus_as_seq {A: Type}  (cₗ1 cₗ2: @denosem Σₗ) (cₕ:  program Σₕ A) F P R Q:
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

Lemma comp_fc_as_conseq {Σₗ Σₕ A: Type}:forall 
  (P: @binasrt Σₗ Σₕ) (cₗ: denosem) (cₕ: program Σₕ A) (Q: A -> @binasrt Σₗ Σₕ) (Pₕ: @asrt Σₕ) Qₕ,
  ((forall X, ⊢∀ {{ [|↑ P && [cₕ ]ₕ|](X) }} cₗ {{ [|EX a, ↑ Q a && [ret a ]ₕ|](X) }})) -> 
  StateRelHoare.Hoare Pₕ cₕ Qₕ ->
  ⊢∀ {{ P ⋈_π Pₕ }} cₗ {{ EX a, (Q a) ⋈_π (Qₕ a) }}.
Proof.
  intros * HRT HHT.
  eapply hoare_conseq_pre.  
  { apply (logic_equiv_derivable1_2 (comp_proj_equiv _ _ )). }
  eapply hoare_exists_intro; intros σₕ.
  eapply hoare_coqprop_preintro. intros HPH.
  specialize (HRT (fun r (x: Σₕ) => cₕ σₕ r x)).
  eapply hoare_conseq;eauto.
  - intros st1 ?.
    unfold encode_asrt, lift, basicasrt.andp, Aspec. simpl.
    do 2 eexists. split;[ | eauto].
    unfold StateRelHoare.weakestpre.
    intros. auto.
  - intros st1 HQ.
    unfold encode_asrt, lift, basicasrt.andp, Aspec in HQ.
    destruct HQ as [σₕ' [cₕ' [? [? [? ?]]]]]. subst. simpl_hdefs.
    unfold StateRelHoare.weakestpre in H. sets_unfold in H.
    specialize (H x σₕ' (ltac:(unfold_monad;auto))). 
    specialize (HHT _ _ _ HPH H).
    exists x.
    do 2 eexists. cbv. split;eauto.
Qed.


End  composition_rules.
End NormalDenoAbsMonadEncRules.


  











