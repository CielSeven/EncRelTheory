(**
 * @file hoarelogic.v
 * @import core semantics and basic assertions.
 * @brief Provides definitions and rules related to Hoare logic for reasoning about imperative programs 
 *        equipped with a relational denotational semantics with error-handling.
 *)

From FP Require Import SetsFixedpoints.
From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import semantics basicasrt hoarelogic.
From EncRelSeq.UBError Require Import errsem.

Import SetsNotation.
Local Open Scope sets_scope.

(***********************************************************************************************************)
(******************************* hoare logic based on semantics with error-handling ************************)
(***********************************************************************************************************)

Module HoarePracticalDeno.
Export practicaldeno.

Definition valid_triple {Σ: Type}: @HT_validity Σ (@denosem Σ) :=
  fun P c Q =>
  forall st1, P st1 -> ~ c.(err) st1 /\ 
  forall st2, c.(nrm) st1 st2 -> Q st2.

Definition valid_angelic_triple {Σ: Type}: @HT_validity Σ (@denosem Σ) :=
  fun P c Q =>
  forall st1, P st1 -> 
  exists st2, c.(nrm) st1 st2 /\ Q st2.


Definition weakestpre {Σ: Type}: @Deno_weakestpre Σ (@denosem Σ) (@asrt Σ) :=
    fun c X => 
      fun σ => ~ c.(err) σ /\ forall σ', c.(nrm) σ σ' -> σ' ∈ X.


Local Open Scope asrt_scope.  
  Lemma hoare_conseq {Σ: Type}: forall c (P P' Q Q': @asrt Σ),
  P |-- P' ->
  Q' |-- Q ->
  valid_triple P' c Q' ->
  valid_triple P c Q.
  Proof.
    unfold valid_triple. simpl. intros * HP' HQ' HT.
    intros * HP.
    specialize (HT _ (HP' _ HP)) as [HTerr HT].
    split;[auto | intros * Heval].
    specialize (HT _ Heval).
    eapply HQ';eauto.
  Qed.

  (* rule Conseq-Pre *)
  Lemma hoare_conseq_pre {Σ: Type}: forall c P P' (Q: @asrt Σ),
  P |-- P' ->
  valid_triple P' c Q ->
  valid_triple P c Q.
  Proof.
    intros. apply (hoare_conseq _  P P' Q Q); auto.
    reflexivity.
  Qed.

  Lemma hoare_conseq_post {Σ: Type}: forall c P (Q: @asrt Σ) Q',
    Q' |-- Q ->
    valid_triple P c Q' ->
    valid_triple P c Q.
  Proof.
    intros. apply (hoare_conseq _ P P Q Q'); auto.
    reflexivity.
  Qed.

  (* rule ExIntro *)
  Lemma hoare_exists_intro {Σ: Type}: forall c (A : Type) (P : A -> @asrt Σ) P',
    (forall v, valid_triple (P v) c P') ->
    valid_triple (exp P) c P'.
  Proof.
    unfold valid_triple. simpl. intros * HT.
    intros * HP.
    destruct HP.
    specialize (HT x _  H) as [HTerr HT].
    split;auto.
  Qed.

  Lemma hoare_exists_r {Σ: Type}: forall c (A : Type) (v : A) P (P' : A -> @asrt Σ),
    valid_triple P c (P' v) ->
    valid_triple P c (exp P').
  Proof.
    unfold valid_triple. simpl. intros * HT.
    intros * HP.
    specialize (HT _ HP) as [HTerr HT].
    split;auto. intros * Hev.
    specialize (HT _ Hev). intuition. exists v. auto.
  Qed.

  Lemma hoare_coqprop_preintro {Σ: Type}: forall c P (Q: @asrt Σ) (P' : Prop),
    (P' -> valid_triple P c Q)->
    valid_triple (!! P'  && P) c Q.
  Proof.
    unfold valid_triple, andp, coq_prop; intros.
    destruct H0 as [? ?].
    specialize (H H0 st1).
    intuition eauto.
  Qed.

  Lemma hoare_coqprop_postintro {Σ: Type}: forall c P (Q: @asrt Σ) (P' : Prop),
    P' -> valid_triple P c Q ->
    valid_triple P c (!! P'  && Q) .
  Proof.
    intros.
    eapply hoare_conseq_post;eauto.
    pose proof (prop_add_left Q P').
    apply logic_equiv_derivable1 in H1 as [? ?]; eauto.
    apply coq_prop_right;auto.
  Qed.
  
  Lemma weakestpre_skip {Σ: Type}: forall (P:  @asrt Σ),
    weakestpre PracticalDenoConstructs.skip P == P.
  Proof.
    intros.
    unfold weakestpre. simpl. sets_unfold. 
    split;intros. apply H;auto.
    split;auto. intros. subst;auto.
  Qed.

Notation " '⊢∀' '{{' P '}}' c {{ Q '}}'" := (valid_triple P c  Q) (at level 71, no associativity).
Notation " '⊢∃' '{{' P '}}' c '{{' Q '}}'" := (valid_angelic_triple P c  Q) (at level 71, no associativity).
Notation " 'wlp' c Q" := (weakestpre c Q) (at level 71, no associativity).

End HoarePracticalDeno.


Module HoarePracticalDenoRules.


Import HoarePracticalDeno.
  
Local Open Scope asrt_scope.

  Import PracticalDenoConstructs.
  Lemma hoare_swhile {Σ:Type}: forall B Ds (P: @asrt Σ),
  valid_triple (B && P)  Ds P -> 
  valid_triple P ( while B Ds) ((notB B) && P).
  Proof.
    intros.
    unfold valid_triple;intros.
    split.
    - unfold while, seq, ife, skip; sets_unfold.
      unfold Lfix;
      sets_unfold; simpl;unfold not;
      intros.
      destruct H1 as [n ?].
      revert st1 H0 H1.
      induction n;intros.
      + contradiction.
      + simpl in *.
        one_destruct Σ (@denosem Σ) H1.
        { subst.
          eapply (IHn st0);eauto.
          unfold valid_triple in H.
          eapply H;eauto.
          cbv.
          auto.  }
        { subst.
          specialize (H st1).
          eapply H;eauto.
          cbv.
          auto. }
    - unfold while, seq, ife, skip; sets_unfold.
      unfold Lfix;
      sets_unfold; simpl;unfold not;
      intros.
      destruct H1 as [n ?].
      revert st1 H0 H1.
      induction n;intros.
      + contradiction.
      + simpl in *.
        one_destruct Σ (@denosem Σ) H1.
        { subst.
          eapply (IHn st0);eauto.
          unfold valid_triple in H.
          eapply H;eauto.
          cbv.
          auto.  }
        { subst.
          cbv.
          auto. }
  Qed. 

  (*rule Seq *)
  Lemma hoare_Seq {Σ:Type}: forall (s1 s2: @denosem Σ) (P1 P2 P3: @asrt Σ),
  valid_triple P1 s1 P2 ->
  valid_triple P2 s2 P3 ->
  valid_triple P1 (seq s1 s2) P3.
  Proof.
    unfold valid_triple. simpl. intros * HT1 HT2.
    intros * HP.
    specialize (HT1 st1 HP) as [? HT1].
    split.
    - sets_unfold.
      repeat match goal with 
      | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
      | |- _ /\ _ => split
      end.
      auto.
      unfold not;intros [? [? ?]].
      specialize (HT1 _ H0).
      specialize (HT2 _ HT1) as [? ?].
      tauto.
    - intros * Hev.
    destruct Hev as [st3 [? ?] ].
    specialize (HT1 _ H0).
    specialize (HT2 _ HT1) as [? HT2].
    specialize (HT2 _ H1).
    auto.
  Qed.

  Lemma hoare_If {Σ:Type}: forall B s1 s2 P (Q: @asrt Σ),
  valid_triple (B && P) s1 Q ->
  valid_triple ((notB B) && P) s2 Q ->
  valid_triple P (ife B s1 s2) Q.
  Proof.
    unfold valid_triple. simpl. intros * HT1 HT2.
    intros * HP.
    specialize (HT1 st1).
    specialize (HT2 st1).
    split.
    - sets_unfold.
      repeat match goal with 
      | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
      | |- _ => split
      end.
      { unfold not;intros [? [? ?]].
        destruct H. subst x.
        cbv in HT1.
        apply HT1;auto. 
      }
      { unfold not;intros [? [? ?]].
        destruct H. subst x.
        cbv in HT2.
        apply HT2;auto. }
    -
    sets_unfold; intros * Hev.
    destruct Hev.
    + destruct H as [? [ [? ?] ?]].
      subst x.
      cbv in HT1.
      apply HT1;auto.
    + destruct H as [? [ [? ?] ?]].
      subst x.
      cbv in HT2.
      apply HT2;auto.
  Qed.
  Lemma hoare_Skip {Σ:Type}: forall (P1:  @asrt Σ),
  valid_triple P1 skip P1 .
  Proof.
    unfold valid_triple, skip;simpl;intros.
    sets_unfold.
    split;auto.
    intros.
    subst;auto.
  Qed.
  
  Lemma Ahoare_skip {Σ:Type}: forall (P:  @asrt Σ), 
    valid_angelic_triple P skip P.
  Proof.
    intros. cbv. intros.
    eexists. split;eauto.
  Qed.


End HoarePracticalDenoRules.

