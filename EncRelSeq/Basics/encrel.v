(**
  * @file encrel.v
  * @brief Proves the correctness of the encoding  relational Hoare logic into standard Hoare logic.
  *
  * @details
  *   - valid_reltriple: Encoded relational Hoare triple using standard Hoare triples.
  *   - Theorem encoding_correctness: Equivalence between the encoded and native relational triple.
  *   - Theorem quadruple_conrrectness: Shows that relational quadruples correspond to encoded triples.
  *)

From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt relasrt hoarelogic relhoarelogic 
                                     encdefs safeexec_lib.


Local Open Scope asrt_scope.

#[export] Instance impnormaldeno_lowlevel_defs {Σ: Type} : lowlevel_defs Σ (@normaldeno.denosem Σ) := {|
  lowlevel_valid_triple := @HoareNormalDeno.valid_triple Σ
|}.

Module EncNormalDeno.
Import normaldeno.
Export NormalDenoExecLib.
Import HoareNormalDeno.
Import RelHoareNormalDeno.


Definition valid_reltriple {Σₗ Σₕ : Type}:= valid_relT Σₗ Σₕ (@denosem Σₗ) (@denosem Σₕ) (@asrt Σₕ).
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).
(**********************************************************************************************)
(**************************     proof for encoding theory    **********************************)
(**********************************************************************************************)

Section normal_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Theorem encoding_correctness  (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@denosem Σₗ))  (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)):
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    unfold valid_reltriple, valid_relT; simpl_ldefs;simpl_hdefs.
    split.
    - unfold valid_RelTriples, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *. simpl_hdefs.
      destruct HP as (σₕ & cₕ &  Hhnrm & HP).
      specialize (HT _ _ _ HP) as  Hnrm.
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as (σₕ' & cₕ' & Hheval  & HQ).
      subst.
      do 2 eexists. split;[ | eauto].
      unfold weakestpre.
      sets_unfold.
      intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun x => cₕ.(nrm) σₕ x) st1).
      intros st2 Heval.
      assert ( ([|P|](fun x : Σₕ => nrm cₕ σₕ x)) st1).
      { unfold encode_asrt.
        do 2 eexists. split;eauto.
        unfold safe.
        intro;auto. 
      }
      specialize (HT H) as ?.
      specialize (H0 _ Heval). 
      unfold encode_asrt in *. 
      simpl_hdefs. unfold weakestpre in *. sets_unfold in H0.  
      destruct H0 as [σₕ' [cₕ' [? ?]]];subst.
      do 2 eexists.
      split;eauto.
  Qed. 

  Import NormalDenoConstructs.
  Theorem quadruple_conrrectness (P: @binasrt Σₗ Σₕ) (cₗ: (@denosem Σₗ)) (cₕ: (@denosem Σₕ)) (Q : @binasrt Σₗ Σₕ):
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ ↑ P && [ₕ cₕ ]ₕ ⟩ cₗ ⟨ ↑ Q  && [ₕ skip ]ₕ ⟩.
  Proof.
    intros.
    split;intros.
    eapply encoding_correctness.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply encoding_correctness;auto.
  Qed.

Section  refinement_soundness.
  
  Variable R : (Σₗ * Σₕ) -> Prop.


  Record denote_refine (LD : @denosem Σₗ) (HD : @denosem Σₕ): Prop := {
  nrm_refine: forall lst1 lst2 hst1, (LD).(nrm) lst1 lst2 -> 
                                      R (lst1, hst1) -> 
                                      (exists hst2, (HD).(nrm) hst1 hst2 /\ R (lst2, hst2));
  }.
  
  Lemma lh_refinement (cₗ: @denosem Σₗ) (cₕ :@denosem Σₕ): 
    ⊢ₑ ⟨ ↑ R && [ₕ cₕ ]ₕ ⟩ cₗ  ⟨ ↑ R && [ₕ skip ]ₕ ⟩ ->
    denote_refine cₗ cₕ.
  Proof.
    intros HRT. apply quadruple_conrrectness in HRT.
    unfold valid_quadruples  in HRT.
    constructor.
    intros σ σ' σₕ HevL HR.
    eapply HRT;eauto.
  Qed.

End  refinement_soundness.
End  normal_validity_soundness.
End  EncNormalDeno.

