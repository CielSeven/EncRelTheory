From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basictacs semantics basicasrt encdefs.
From EncRelSeq.UBError Require Import errsem hoarelogic.

Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.

#[export] Instance imppracticaldeno_highlevel_defs {Σ: Type} : highlevel_defs Σ (@practicaldeno.denosem Σ) (@asrt Σ) := {|
  highlevel_wlp := @HoarePracticalDeno.weakestpre Σ
|}.


Module PracticalDenoExecLib.
Import practicaldeno.
Import PracticalDenoConstructs.
Import HoarePracticalDeno.

Lemma  seq_safe: forall {Σ: Type} (st : Σ) (s ks:  @denosem Σ), 
    ~ ((seq  s ks).(err) st) ->  ~ s.(err) st.
Proof.
  intros *.
  unfold seq;sets_unfold;simpl;intros.
  tauto.
Qed.

Lemma  seq_middlest_safe: forall {Σ: Type} (st : Σ) (s: @denosem Σ) ks X st',  
    safe st ( seq s ks) X -> 
    s.(nrm) st st' -> 
    safe st' ks X.
Proof.
  intros *.
  unfold safe, seq;sets_unfold;simpl;intros * [? ?] ?.
  split.
  - unfold not;intros.
    apply H.
    right.
    eexists;split;eauto.
  - intros.
    apply H0.
    eexists.
    split;eauto.
Qed.



(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Section  safe_rules.
  Context {Σ : Type}.
  
  Ltac destructs H:= one_destruct Σ (@denosem Σ) H. 
  
  Lemma Exec_pure : forall B (P: @asrt Σ) s X,
    Exec ( !! B && P) s X <-> B /\ Exec P s X.
  Proof.
    unfold Exec,safe, basicasrt.andp, basicasrt.coq_prop;sets_unfold.
    intros. split;intros.
    - destructs H.
      split;auto.
      eexists.
      split;eauto.
    - destructs H.
      eexists.
      splits;eauto.
  Qed.
  
  Lemma Exec_Seq : forall (P P': @asrt Σ)  s ks,
    (forall X, Exec P s X -> Exec P' skip X) ->
    (forall X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof. 
    unfold Exec;sets_unfold;intros.
    destructs H0. destruct H1.
    specialize (H (fun x => s.(nrm) st x)).
    assert ((exists σₕ0 : Σ,
    P σₕ0 /\
    ~ s.(err) σₕ0 /\
    (forall σₕ' : Σ,
    s.(nrm) σₕ0 σₕ' ->
    σₕ'
    ∈ (fun x : Σ =>
        s.(nrm) st x)))).
    { eexists;splits;eauto. 
      eapply seq_safe;eauto. }
    specialize (H H3);clear H3.
    destructs H. destruct H3.
    specialize (H4 st0 (Logic.eq_refl _)).
    unfold safe. simpl. unfold weakestpre. sets_unfold.
    sets_unfold in H4.
    eexists.
    splits;eauto.
    { revert H1;unfold seq, safe, weakestpre;sets_unfold;simpl;intros.
      unfold not;intros.
      apply H1.
      right.
      eexists. splits;eauto. }
    intros.
    apply H2.
    unfold seq;sets_unfold;simpl.
    eexists.
    split;eauto.
  Qed.

  Lemma highstepend_derive : forall s (P P' : Σ -> Prop),
  ⊢∃ {{P}} s {{P'}} -> (forall X, Exec P s X -> Exec P' skip X).
  Proof.
    intros.
    unfold valid_angelic_triple, Exec, safe in *.
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    split;auto.
    unfold safe,weakestpre, skip;simpl; sets_unfold; simpl;intros.
    subst.
    eapply H1;eauto.
  Qed.

  Lemma highstepseq_derive : forall s (P P' : Σ -> Prop),
  ⊢∃ {{P}} s {{P'}} -> (forall ks X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof.
    intros * H ks.
    eapply Exec_Seq;eauto.
    eapply highstepend_derive;eauto.
  Qed.

End  safe_rules. 
End  PracticalDenoExecLib.