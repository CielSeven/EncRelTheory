From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basictacs semantics basicasrt hoarelogic encdefs. 

Import SetsNotation.
Local Open Scope sets_scope.
Local Open Scope asrt_scope.

#[export] Instance impnormaldeno_highlevel_defs {Σ: Type} : highlevel_defs Σ (@normaldeno.denosem Σ) (@asrt Σ) := {|
  highlevel_wlp := @HoareNormalDeno.weakestpre Σ
|}.

Module NormalDenoExecLib.
Import normaldeno.
Import NormalDenoConstructs.
Import HoareNormalDeno.

Lemma  seq_middlest_safe: forall {Σ: Type} (st : Σ) (s: @denosem Σ) ks X st',  
    safe st (seq s ks) X -> 
    s.(nrm) st st' -> 
    safe st' ks X.
Proof.
  intros *.
  unfold safe, seq;sets_unfold;simpl;intros * ? ? ? ?.
    apply H.
    eexists.
    split;eauto.
Qed.

(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Section  safe_rules.
  Context {Σ : Type}.

  Ltac destructs  H:= one_destruct Σ (@denosem Σ) H. 
  
  Lemma Exec_imply_cont : forall (P P': @asrt Σ)  s ks,
    (forall X, Exec P s X -> Exec P' skip X) ->
    (forall X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof. 
    unfold Exec; sets_unfold;intros.
    simpl_hdefs.
    destructs H0. 
    specialize (H (fun x => s.(nrm) st x)).
    assert ((exists σₕ0 : Σ, P σₕ0 /\ safe σₕ0 s (fun x : Σ => nrm s st x))).
    { eexists;splits;eauto. 
      unfold safe. simpl. unfold weakestpre. auto. }
    specialize (H H2);clear H2.
    destructs H. 
    specialize (H2 st0 (Logic.eq_refl _)).
    unfold safe; simpl. unfold weakestpre. sets_unfold.
    sets_unfold in H2.
    eexists.
    splits;eauto.
    intros.
    apply H1.
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
    unfold safe,weakestpre, skip;simpl; sets_unfold; simpl;intros.
    subst.
    eapply H1;eauto.
  Qed.

  Lemma highstepseq_derive : forall s (P P' : Σ -> Prop),
  ⊢∃ {{P}} s {{P'}} -> (forall ks X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof.
    intros * H ks.
    eapply Exec_imply_cont;eauto.
    eapply highstepend_derive;eauto.
  Qed.

End  safe_rules. 
End  NormalDenoExecLib.
