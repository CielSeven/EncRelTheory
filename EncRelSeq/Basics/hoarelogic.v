(**
  * @file hoarelogic.v
  * @brief Provides generic notions for valid triples `HT_validity` and weakestpre `Deno_weakestpre`.
  *        Provides Hoare logic rules over relational denotational semantics (normal).
  *
  * @details
  *   - Defines validity of standard and angelic Hoare triples using relational semantics.
  *   - Defines weakest precondition for programs with denotational semantics.
  *   - Proves basic structural rules: consequence, existential intro, and Coq-level assertions.
  *   - Includes compositional rules: sequencing, conditionals, and while loops.
  *)


From FP Require Import SetsFixedpoints.
From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basictacs semantics basicasrt.

Import SetsNotation.
Local Open Scope sets_scope.


(* This is a generic notion of Hoare triple validity over any program. *)
Definition HT_validity {Σ: Type} {Prog: Type}: Type := (@asrt Σ) -> (Prog) -> (@asrt Σ) -> Prop.
(* This is a generic notion of weakest precondition  over any program. *)
Definition Deno_weakestpre {Σ: Type} {Prog: Type} {Postasrt: Type} : Type := 
  forall (c: Prog) (X: Postasrt),  Σ -> Prop.



Module HoareNormalDeno.
Export normaldeno.

Definition valid_triple {Σ: Type}: @HT_validity Σ (@denosem Σ) :=
  fun P c Q =>
  forall st1, P st1 -> 
  forall st2, c.(nrm) st1 st2 -> Q st2.

Definition valid_angelic_triple {Σ: Type}: @HT_validity Σ (@denosem Σ) :=
  fun P c Q =>
  forall st1, P st1 -> 
  exists st2, c.(nrm) st1 st2 /\ Q st2.

Definition weakestpre {Σ: Type} : @Deno_weakestpre Σ (@denosem Σ) (@asrt Σ):=
    fun c X => fun σ =>  forall σ', c.(nrm) σ σ' -> σ' ∈ X.


Local Open Scope asrt_scope.

  Lemma hoare_conseq {Σ: Type}: forall c (P P' Q Q': @asrt Σ),
  P |-- P' ->
  Q' |-- Q ->
  valid_triple P' c Q' ->
  valid_triple P c Q.
  Proof.
    unfold valid_triple. simpl. intros * HP' HQ' HT.
    intros * HP.
    specialize (HT _ (HP' _ HP) ) as HT.
    intros * Heval.
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
    specialize (HT x _  H) as HT.
    auto.
  Qed.

  Lemma hoare_exists_r {Σ: Type}: forall c (A : Type) (v : A) P (P' : A -> @asrt Σ),
    valid_triple P c (P' v) ->
    valid_triple P c (exp P').
  Proof.
    unfold valid_triple. simpl. intros * HT.
    intros * HP.
    specialize (HT _ HP) as  HT.
    intros * Hev.
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
    weakestpre NormalDenoConstructs.skip P == P.
  Proof.
    intros.
    unfold weakestpre. simpl. sets_unfold. 
    split;intros. apply H;auto.
    subst;auto.
  Qed.

Notation " '⊢∀' '{{' P '}}' c '{{' Q '}}'" := (valid_triple P c  Q) (at level 71, no associativity).
Notation " '⊢∃' '{{' P '}}' c '{{' Q '}}'" := (valid_angelic_triple P c  Q) (at level 71, no associativity).
Notation " 'wlp' c Q" := (weakestpre c Q) (at level 71, no associativity).

End HoareNormalDeno.

Module HoareNormalDenoRules.

Import HoareNormalDeno.
  
Local Open Scope asrt_scope.

  Import NormalDenoConstructs.

  Lemma hoare_swhile {Σ:Type} : forall B Ds (P: @asrt Σ),
  valid_triple (B && P)  Ds P -> 
  valid_triple P ( while B Ds) ((notB B) && P).
  Proof.
    intros.
    unfold valid_triple;intros.
    revert H1.
    unfold while, seq, ife, skip; sets_unfold.
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

  (* rule Seq *)
  Lemma hoare_Seq {Σ:Type}: forall (s1 s2: @denosem Σ) (P1 P2 P3: @asrt Σ),
  valid_triple P1 s1 P2 ->
  valid_triple P2 s2 P3 ->
  valid_triple P1 (seq s1 s2) P3.
  Proof.
    unfold valid_triple. simpl. intros * HT1 HT2.
    intros * HP.
    specialize (HT1 st1 HP) as HT1.
    intros * Hev.
    destruct Hev as [st3 [? ?] ].
    specialize (HT1 _ H).
    specialize (HT2 _ HT1) as HT2.
    specialize (HT2 _ H0).
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
    sets_unfold in H0.
    subst;auto.
  Qed.

  Lemma Ahoare_skip {Σ:Type}: forall (P:  @asrt Σ), 
    valid_angelic_triple P skip P.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.


End HoareNormalDenoRules.
