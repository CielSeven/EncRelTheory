From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadErr.StateRelMonadErr.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt encdefs.
From EncRelSeq.UBError Require Import errsem hoarelogic encrel.
From EncRelSeq.MonadsAsHigh.AbsMonadE Require Import relhoarelogic.

Require Import Coq.Logic.Classical_Prop.

#[export] Instance staterelmonaderr_highlevel_defs {Σ A: Type} : highlevel_defs Σ (program Σ A) (A -> Σ -> Prop) := {|
  highlevel_wlp := @weakestpre Σ A
|}.


Module EncPracticalDenoAbsMonad.
Import practicaldeno.
Import HoarePracticalDeno.
Import RelHoarePracticalDenoAsbMonad.

Definition valid_reltriple {Σₗ Σₕ A: Type}:= valid_relT Σₗ Σₕ (@denosem Σₗ) (program Σₕ A) (A -> Σₕ -> Prop).

Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).

Local Open Scope asrt_scope.

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
      destruct HP as (σₕ & cₕ & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not. intros.
        apply Hherr. apply Herr. auto.
      + 
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as [ | (σₕ' & cₕ' &  Hheval  & HQ)];[ contradiction | ].
      do 2 eexists. split;[ | eauto].
      destruct Hheval as [Hheval1 Hheval2].
      unfold MonadErrHoare.weakestpre in *.
      sets_unfold.
      split.
      * intros ?. eapply Hherr. eapply Hheval2. eauto.
      * intros.
      eapply Hhnrm;eauto. sets_unfold. auto.
    - unfold valid_RelTriples, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun r x => cₕ.(nrm) σₕ r x) st1).
      split.
      + intros. 
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ.(nrm) σₕ r x)) st1).
        { unfold encode_asrt. simpl_hdefs.
          do 2 eexists. split;[ | eauto].
          unfold MonadErrHoare.weakestpre; sets_unfold. auto. 
        }
        specialize (HT H1) as [? _].
        contradiction.
      + intros lst2 Hleval.
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ.(nrm) σₕ r x)) st1).
        { unfold encode_asrt. simpl_hdefs.
          do 2 eexists. split;[ | eauto].
          unfold MonadErrHoare.weakestpre; sets_unfold. auto. 
        }
        specialize (HT H0) as [_ HT].
        specialize (HT _ Hleval).
        destruct HT as [σₕ' [cₕ' [? ?]]];subst.
        right.
        do 2 eexists.
        split;eauto.
        destruct H1.
        unfold config_refinement.
        split.
        * intros.
          eapply H3;eauto.
        * intros.
          contradiction. 
  Qed. 

  Theorem validity_conrrectness : forall {A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ ↑ P && [ₕ cₕ ]ₕ ⟩ cₗ ⟨ EX r : A, ↑ (Q r) && [ₕ ret r ]ₕ ⟩.
  Proof.
    intros.
    split;intros.
    eapply encoding_correctness.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply encoding_correctness;auto.
  Qed.

End normal_validity_soundness.
End EncPracticalDenoAbsMonad.


Module PracticalDenoAbsMonadEncRules.

Import practicaldeno.
Import EncPracticalDenoAbsMonad.

Local Open Scope asrt_scope. 

(**********************************************************************************)
(*   encoded hoare rules                                                          *)
(**********************************************************************************)

Import HoarePracticalDeno PracticalDenoConstructs.
Import HoarePracticalDenoRules.
Import RelHoarePracticalDenoAsbMonad.


  Section  encrules.
  Context {Σₗ Σₕ: Type}.
  Ltac destructs H := rel_destruct Σₗ Σₕ (@denosem Σₕ) (@denosem Σₗ) H.



(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)

  Lemma  reltriple_triple_equiv1 {A:Type}: forall (P: @asrt Σₗ) Ps (s: program Σₕ A) c Q,
    ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ₕ s ]ₕ ⟩ c ⟨ Q ⟩ <->
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
    ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ₕ s ]ₕ ⟩ c ⟨EX (r: R) (a:A), !! (B a r) && ⌊ Q a r ⌋ && ⌈ Ps' a r⌉ && [ₕ ret r ]ₕ ⟩ <->
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
    MonadErrHoare.valid_angelic_triple P cₕ1 (fun r σ => r = a /\ R σ) ->
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
  ((forall X, ⊢∀ {{ [|↑ P && [ₕ cₕ ]ₕ|](X) }} cₗ {{ [|EX a, ↑ Q a && [ₕ ret a ]ₕ|](X) }})) -> 
  MonadErrHoare.Hoare Pₕ cₕ Qₕ ->
  ⊢∀ {{ P ⋈_π Pₕ }} cₗ {{ EX a, (Q a) ⋈_π (Qₕ a) }}.
Proof.
  intros * HRT HHT.
  eapply hoare_conseq_pre.  
  { apply (logic_equiv_derivable1_2 (comp_proj_equiv _ _ )). }
  eapply hoare_exists_intro; intros σₕ.
  eapply hoare_coqprop_preintro. intros HPH.
  specialize (HRT (fun r (x: Σₕ) => cₕ.(nrm) σₕ r x)).
  eapply hoare_conseq;eauto.
  - intros st1 ?.
    unfold encode_asrt, lift, basicasrt.andp, Aspec. simpl.
    do 2 eexists. split;[ | eauto].
    unfold MonadErrHoare.weakestpre.
    destruct HHT.
    specialize (H1 _ HPH).
    split;auto.
  - intros st1 HQ.
    unfold encode_asrt, lift, basicasrt.andp, Aspec in HQ.
    destruct HQ as [σₕ' [cₕ' [? [? [? ?]]]]]. subst. simpl_hdefs.
    unfold MonadErrHoare.weakestpre in H. sets_unfold in H.
    destruct H.
    specialize (H1 x σₕ' (ltac:(unfold_monad;auto))).
    destruct HHT. 
    specialize (H2 _ _ _ HPH H1).
    exists x.
    do 2 eexists. cbv. split;eauto.
Qed.


End  composition_rules.
End PracticalDenoAbsMonadEncRules.

