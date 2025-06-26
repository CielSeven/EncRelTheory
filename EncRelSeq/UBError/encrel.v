From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basicasrt relasrt encdefs.
From EncRelSeq.UBError Require Import errsem hoarelogic relhoarelogic safeexec_lib.
Require Import Coq.Logic.Classical_Prop.

Local Open Scope asrt_scope.

#[export] Instance imppracdeno_lowlevel_defs {Σ: Type} : lowlevel_defs Σ (@practicaldeno.denosem Σ) := {|
  lowlevel_valid_triple := @HoarePracticalDeno.valid_triple Σ
|}.


Module EncPracticalDeno.
Import practicaldeno.
Export PracticalDenoExecLib.
Import HoarePracticalDeno.
Import RelHoarePracticalDeno.

Definition valid_reltriple {Σₗ Σₕ : Type}:= valid_relT Σₗ Σₕ (@denosem Σₗ) (@denosem Σₕ) (@asrt Σₕ).
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).
(**********************************************************************************************)
(**************************     proof for encoding theory    **********************************)
(**********************************************************************************************)
Section practical_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Theorem encoding_correctness  (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@denosem Σₗ))  (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)):
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    unfold valid_reltriple, valid_relT; simpl_ldefs;simpl_hdefs.
    split.
    - unfold valid_RelTriples, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros st2 Heval.
      simpl_hdefs. unfold weakestpre in *. sets_unfold.
      specialize (Hnrm _ Heval) as [ | (σₕ' & cₕ' & [Hheval Hhevalerr] & HQ) ];[contradiction | ].
      subst.
      do 2 eexists. split;[ | eauto].
      split;[auto | ].
      intros.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun x => cₕ.(nrm) σₕ x) st1).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        assert (([|P|](fun x : Σₕ => nrm cₕ σₕ x)) st1).
        { unfold encode_asrt. simpl_hdefs.
          do 2 eexists. split;eauto.
          unfold weakestpre.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        contradiction.
      + intros st2 Heval.
        (* excluded middle used *)
        pose proof classic (cₕ.(err) σₕ) as [ | ];[auto | ].
        right.
        assert ( ([|P|](fun x : Σₕ => nrm cₕ σₕ x)) st1).
        { unfold encode_asrt. simpl_hdefs.
          do 2 eexists. split;eauto.
          unfold weakestpre.
          split;auto. 
        }
        specialize (HT H0) as [? ?].
        specialize (H2 _ Heval). 
        unfold encode_asrt in *. simpl_hdefs.
        unfold weakestpre in *.  simpl in *.
        destruct H2 as [σₕ' [cₕ' [? ?]]];subst.
        do 2 eexists.
        split;[ | eauto].
        unfold config_refinement ;cbn;sets_unfold.
        split.
        { intros. 
        destruct H2 as [_ ?].
        auto. }
        intros.
        destruct H2 as [? _].
        contradiction.
  Qed. 

  Import PracticalDenoConstructs.
  Theorem quadruple_conrrectness (P: @binasrt Σₗ Σₕ) (cₗ: (@denosem Σₗ)) (cₕ: (@denosem Σₕ)) (Q : @binasrt Σₗ Σₕ):
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ ↑ P && [cₕ]ₕ ⟩ cₗ ⟨ ↑ Q  && [skip]ₕ ⟩.
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
                                      (exists hst2, (HD).(nrm) hst1 hst2 /\ R (lst2, hst2)) \/ 
                                      ((HD).(err) hst1);
  err_refine: forall lst hst, (LD).(err) lst -> R (lst, hst) -> ((HD).(err) hst)
  }.

  Lemma lh_refinement (cₗ: @denosem Σₗ) (cₕ :@denosem Σₕ): 
    ⊢ₑ ⟨ ↑ R && [cₕ]ₕ ⟩ cₗ  ⟨ ↑ R && [skip]ₕ ⟩ ->
    denote_refine cₗ cₕ.
  Proof.
    intros HRT. apply quadruple_conrrectness in HRT.
    unfold valid_quadruples  in HRT.
    constructor.
    - 
    intros σ σ' σₕ HevL HR.
    specialize (HRT _ _ HR) as [_ ?].
    specialize (H _  HevL) as [? | ?];[ auto | ].
    left.
    eapply H;eauto.
    - intros.
      specialize (HRT _ _ H0) as [Herr _].
      auto.
  Qed.

End  refinement_soundness.
End  practical_validity_soundness.
End  EncPracticalDeno.
