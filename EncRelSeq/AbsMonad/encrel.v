From SetsClass Require Import SetsClass.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From EncRelSeq Require Import semantics basicasrt.
From EncRelSeq.AbsMonad Require Import hoarelogic.


Module EncNormalDenoAbsMonad.
Import normaldeno.

Section  encoding.
  Context {Σₗ Σₕ: Type}.
  Context {deno : Type}.
  Context {valid_t: @HT_validity Σₗ deno}.



  Definition encode_asrt {A: Type}  (P: @relasrt Σₗ Σₕ (program Σₕ A)) (X: A -> Σₕ -> Prop): @basicasrt.asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (program Σₕ A)),  
           safe σₕ cₕ X /\  P (σₗ, σₕ, cₕ).

  Definition valid_relT  {A: Type}  (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: deno) (Q : @relasrt Σₗ Σₕ (program Σₕ A)) := 
  forall X, valid_t 
                    (encode_asrt P X)
                    cₗ 
                    (encode_asrt Q X).
End  encoding.


Notation " '[|' P '|]' '(' x ')' " := (encode_asrt P x)  (at level 20, no associativity). 

Import RelHoareNormalDenoAsbMonad.
Definition valid_reltriple {Σₗ Σₕ A: Type}:= @valid_relT Σₗ Σₕ (@denosem Σₗ) (@valid_triple Σₗ) A.
Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).

(*************************************************************************************************************)
(*******************************     soundness proof for valid_reltriple    **********************************)
(*************************************************************************************************************)

Import MonadNotation.
Local Open Scope monad.
Section normal_validity_soundness.
  Context {Σₗ Σₕ: Type}.

  Theorem validity_lemma : forall {A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: denosem)  (Q :  @relasrt Σₗ Σₕ (program Σₕ A)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_reltriple, valid_relT, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ &  Hhnrm & HP).
      specialize (HT _ _ _ HP) as Hnrm.
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as (σₕ' & cₕ' & Hheval  & HQ).
      do 2 eexists. split;[ | eauto].
      unfold safe.
      cbn;intros.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_reltriple,valid_relT, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun r x => cₕ σₕ r x) st1).
        intros st2 Heval.
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ σₕ r x)) st1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;[ | eauto].
          unfold safe;auto. 
        }
        specialize (HT H _ Heval). clear H.
        unfold encode_asrt in *.
        destruct HT as [σₕ' [cₕ' [? ?]]];subst.
        do 2 eexists.
        split;eauto.
  Qed. 

  Local Open Scope asrt_scope.
  Theorem validity_conrrectness : forall {A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ EX x, lift (Q x) (return x) ⟩.
  Proof.
    intros.
    split;intros.
    eapply validity_lemma.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply validity_lemma;auto.
  Qed.

  Section absnoret.
     Lemma quadruple2reltriple_noret : forall  (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ unit)  (Q :  @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{fun _ => Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ lift Q (return tt) ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & r & Hheval & HQ).
      destruct r.
      unfold lift.
      do 2 eexists.
      split;eauto.
      unfold sem_eval.
      intros.
      destruct r.
      unfold_monad in H. destruct H as [? ?].
      subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? &  Hheval &  HQ & ? ).
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      unfold_monad;auto.
  Qed.


  Theorem validity_conrrectness_noret : forall (P: @binasrt Σₗ Σₕ ) (cₗ: denosem)  (cₕ: program Σₕ unit)  (Q : @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{fun _ => Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ lift Q (return tt) ⟩.
  Proof.
    intros.
    split;intros.
    eapply validity_lemma.
    eapply quadruple2reltriple_noret;auto.

    eapply quadruple2reltriple_noret.
    eapply validity_lemma;auto.
  Qed.
    
  End absnoret.
  
End normal_validity_soundness.


Arguments  valid_reltriple {Σₗ} {Σₕ} {A}.

(* 
Section absnostate_validity_soundness.
  Context {Σₗ : Type}.
  Context {deno : Type}.
  Context {valid_t: @HT_validity Σₗ deno}.

  Local Notation " '⊢' '{{' P '}}' cₗ '≾' cₕ '{{' Q '}}'" := (valid_quadruples P cₗ cₕ Q) (at level 71, no associativity).
  Local Notation " '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_RelTriples P c Q) (at level 71, no associativity).
  Local Notation " '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_reltriple P c Q) (at level 71, no associativity).

  Lemma quadruple2reltriple_nostate : forall {A: Type} (P: @binasrt Σₗ unit ) (cₗ: toysem)  (cₕ: MONAD A)  (Q : A -> @binasrt Σₗ unit),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ fun x => lift (Q x) (return x) ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' [HP ?].
      TODO
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & r & Hheval & HQ).
      unfold lift.
      do 3 eexists.
      split;eauto.
      unfold sem_eval.
      intros.
      apply return_eq in H as [? ?].
      subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & r & Hheval & HQ & ?).
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      apply return_eq;auto.
  Qed.

  Theorem validity_lemma : forall {A: Type} (P: @relasrt Σₗ Σₕ (program Σₕ A)) (cₗ: toysem)  (Q : A -> @relasrt Σₗ Σₕ (program Σₕ A)),
    ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_reltriple, valid_relT, valid_triple.
      intros HT X st1 HP.
      unfold encode_asrt in *.
      destruct HP as (σₕ & cₕ &  Hhnrm & HP).
      specialize (HT _ _ _ HP) as Hnrm.
      intros st2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as (σₕ' & cₕ' &  a & Hheval  & HQ).
      subst.
      do 3 eexists. split;[ | eauto].
      unfold safe.
      cbn;intros.
      eapply Hhnrm;eauto.
    - unfold valid_RelTriples, valid_reltriple,valid_relT, valid_triple.
      intros HT st1 σₕ cₕ HP.
      specialize (HT (fun r x => cₕ σₕ r x) st1).
        intros st2 Heval.
        assert (([|P|](fun (r : A) (x : Σₕ) => cₕ σₕ r x)) st1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;[ | eauto].
          unfold safe;auto. 
        }
        specialize (HT H _ Heval). clear H.
        unfold encode_asrt in *.
        destruct HT as [a [σₕ' [cₕ' [? ?]]]];subst.
        do 3 eexists.
        split;eauto.
  Qed. 

  Theorem validity_conrrectness : forall {A: Type} (P: @binasrt Σₗ Σₕ ) (cₗ: toysem)  (cₕ: program Σₕ A)  (Q : A -> @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ fun x => lift (Q x) (return x) ⟩.
  Proof.
    intros.
    split;intros.
    eapply validity_lemma.
    eapply quadruple2reltriple;auto.

    eapply quadruple2reltriple.
    eapply validity_lemma;auto.
  Qed.

  Section absnoret.
     Lemma quadruple2reltriple_noret : forall  (P: @binasrt Σₗ Σₕ ) (cₗ: toysem)  (cₕ: program Σₕ unit)  (Q :  @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{fun _ => Q}} <-> ⊢ ⟨ lift P cₕ ⟩ cₗ ⟨ fun _ => lift Q (return tt) ⟩.
  Proof.
    intros;split.
    - unfold valid_RelTriples, valid_quadruples.
      intros HQ lst1 hst1 cₕ' [HP ?].
      subst.
      intros lst2 Hleval.
      specialize (HQ _ _ HP _ Hleval) as (hst2 & r & Hheval & HQ).
      destruct r.
      unfold lift.
      do 2 eexists. exists tt.
      split;eauto.
      unfold sem_eval.
      intros.
      destruct r.
      apply (return_eq hst2 σ₃) in H as [? ?].
      subst.
      auto.
    - unfold valid_RelTriples, valid_quadruples, lift.
      intros HT lst1 hst1 HP.
      intros lst2 Hleval.
      specialize (HT lst1 hst1 _ (ltac:(split;auto)) _ Hleval) as (hst2 & ? & r & Hheval & HQ & ?).
      destruct r.
      subst.
      do 2 eexists.
      split;eauto.
      eapply Hheval.
      apply return_eq;auto.
  Qed.

  Theorem validity_lemma_noret : forall  (P: @relasrt Σₗ Σₕ (program Σₕ unit)) (cₗ: toysem)  (Q :@relasrt Σₗ Σₕ (program Σₕ unit)),
    ⊢ ⟨ P ⟩ cₗ ⟨ fun _ => Q ⟩ <-> ⊢ₑ ⟨ P ⟩ cₗ ⟨ fun _ => Q ⟩.
  Proof.
    intros.
    apply validity_lemma.
  Qed. 

  Theorem validity_conrrectness_noret : forall (P: @binasrt Σₗ Σₕ ) (cₗ: toysem)  (cₕ: program Σₕ unit)  (Q : @binasrt Σₗ Σₕ),
    ⊢ {{P}} cₗ ≾ cₕ {{fun _ => Q}} <-> ⊢ₑ ⟨ lift P cₕ ⟩ cₗ ⟨ fun _ => lift Q (return tt) ⟩.
  Proof.
    intros.
    split;intros.
    eapply validity_lemma_noret.
    eapply quadruple2reltriple_noret;auto.

    eapply quadruple2reltriple_noret.
    eapply validity_lemma_noret;auto.
  Qed.
    
  End absnoret.
  
End normal_validity_soundness. *)
End  EncNormalDenoAbsMonad.