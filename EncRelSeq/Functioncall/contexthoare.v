
From AUXLib Require Import List_lemma.
From SetsClass Require Import SetsClass.
From EncRelSeq Require Import callsem Basics.basicasrt. 
From EncRelSeq.Basics Require Export hoarelogic.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import Idents.
From FP Require Import SetsFixedpoints.

Import SetsNotation.
Local Open Scope sets.


(*************************************************************************************************************)
(**********************************             contextual triples           *********************************)
(**********************************   Normal Setting                         *********************************)
(**********************************          1. no join                      *********************************)
(**********************************          2. χ: func -> deno Σ            *********************************)
(*************************************************************************************************************)
Module ContextualNormal.

Import normaldeno.
Import CallNormalDeno.
Section contextual_hoaretriples.
  Context {Σ: Type}.
  Context {callc : @calllangclass Σ}.

  Definition assertion := @asrt Σ.
  Record funcspec : Type := mk_funcspec {
    FS_With : Type;
    FS_Pre : FS_With -> assertion;
    FS_Post : FS_With -> assertion;
  }.


  Definition funcspecs : Type := list (func * funcspec).

  Definition funcspecs_sat (χ : func -> @denosem Σ)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 (w : fspec.(FS_With)),
    fspec.(FS_Pre) w st1 ->
    forall st2, 
    (χ f).(nrm) st1 st2 ->
    fspec.(FS_Post) w st2.

  Definition valid_triple  (χ : func -> @denosem Σ): @HT_validity Σ (Langstmts) :=
    fun P c Q =>
    forall st1, P st1 -> 
    forall st2, (evalnrm (fun f => (χ f).(nrm)) c) st1 st2 -> Q st2.


  Definition valid_contextualtriple (Delta : funcspecs) : @HT_validity Σ (Langstmts) :=
    fun  (P : assertion) (c : (Langstmts)) (Q : assertion) =>
    forall χ,
    funcspecs_sat χ Delta ->
    valid_triple χ P c Q.

  Lemma funcspecs_equivforall : forall Δ χ ,
    funcspecs_sat χ Δ <-> Forall (fun '(f, fspec) => (forall st1 (w : fspec.(FS_With)),
    fspec.(FS_Pre) w st1 ->
    forall st2, 
    (χ f).(nrm) st1 st2 ->
    fspec.(FS_Post) w st2)) Δ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold funcspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      eapply H;eauto.
  Qed. 
    

  Lemma funcspecs_sat_app : forall Δ1 Δ2 χ ,
    funcspecs_sat χ (Δ1 ++ Δ2) <->  (funcspecs_sat χ Δ1 /\  funcspecs_sat χ Δ2).
  Proof.
    intros.
    split;intros.
    - apply funcspecs_equivforall in H.
      apply Forall_app in H as [? ?].
      apply funcspecs_equivforall in H.
      apply funcspecs_equivforall in H0.
      split;auto.
    - apply funcspecs_equivforall.
      apply Forall_app.
      split.
      apply funcspecs_equivforall. tauto.
      apply funcspecs_equivforall. tauto.
  Qed.


End contextual_hoaretriples.

End ContextualNormal.

(*************************************************************************************************************)
(**********************************             contextual triples           *********************************)
(**********************************             including errors             *********************************)
(**********************************   Normal Setting                         *********************************)
(**********************************          1. no join                      *********************************)
(**********************************          2. χ: func -> deno Σ            *********************************)
(*************************************************************************************************************)
Module ContextualPractical.

Import practicaldeno.
Import CallPracticalDeno.
Section contextual_hoaretriples.
  Context {Σ: Type}.
  Context {callc : @calllangclass Σ}.

  Definition assertion := @asrt Σ.
  Record funcspec : Type := mk_funcspec {
    FS_With : Type;
    FS_Pre : FS_With -> assertion;
    FS_Post : FS_With -> assertion;
  }.


  Definition funcspecs : Type := list (func * funcspec).

  Definition funcspecs_sat (χ : func -> @denosem Σ)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 (w : fspec.(FS_With)),
    fspec.(FS_Pre) w st1 ->
    ~ (χ f).(err) st1 /\
    forall st2, 
    (χ f).(nrm) st1 st2 ->
    fspec.(FS_Post) w st2.

  Definition valid_triple  (χ : func -> @denosem Σ): @HT_validity Σ (Langstmts) :=
    fun P c Q =>
    forall st1, P st1 -> ~ (evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) st1 /\ 
    forall st2, (evalnrm (fun f => (χ f).(nrm)) c) st1 st2 -> Q st2.


  Definition valid_contextualtriple (Delta : funcspecs) : @HT_validity Σ (Langstmts) :=
    fun  (P : assertion) (c : (Langstmts)) (Q : assertion) =>
    forall χ,
    funcspecs_sat χ Delta ->
    valid_triple χ P c Q.

  Lemma funcspecs_equivforall : forall Δ χ ,
    funcspecs_sat χ Δ <-> Forall (fun '(f, fspec) => (forall st1 (w : fspec.(FS_With)),
    fspec.(FS_Pre) w st1 ->
    ~ (χ f).(err) st1 /\
    forall st2, 
    (χ f).(nrm) st1 st2 ->
    fspec.(FS_Post) w st2)) Δ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold funcspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      apply H;auto.
  Qed. 
    

  Lemma funcspecs_sat_app : forall Δ1 Δ2 χ ,
    funcspecs_sat χ (Δ1 ++ Δ2) <->  (funcspecs_sat χ Δ1 /\  funcspecs_sat χ Δ2).
  Proof.
    intros.
    split;intros.
    - apply funcspecs_equivforall in H.
      apply Forall_app in H as [? ?].
      apply funcspecs_equivforall in H.
      apply funcspecs_equivforall in H0.
      split;auto.
    - apply funcspecs_equivforall.
      apply Forall_app.
      split.
      apply funcspecs_equivforall. tauto.
      apply funcspecs_equivforall. tauto.
  Qed.


End contextual_hoaretriples.

End ContextualPractical.


(*************************************************************************************************************)
(**********************************             contextual triples           *********************************)
(**********************************             including errors             *********************************)
(**********************************   Setting:                               *********************************)
(**********************************         1.program state join             *********************************)
(**********************************           valid triple has state frame   *********************************)
(**********************************         2. χ: func -> deno Σ             *********************************)
(*************************************************************************************************************)

Module ContextualJoinState.

Import practicaldeno.
Import CallPracticalDeno.
Section contextual_hoaretriples.
  Context {Σ: Type}.
  Context {callc: @calllangclass Σ}.
  Context {joinm: @JoinM Σ}.

  Definition assertion := @asrt Σ.
  Record funcspec : Type := mk_funcspec {
    FS_With : Type;
    FS_Pre : FS_With -> assertion;
    FS_Post : FS_With -> assertion;
  }.


  Definition funcspecs : Type := list (func * funcspec).

  Definition funcspecs_sat (χ : func -> @denosem Σ)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 st1' stf (w : fspec.(FS_With)),
      join st1' stf st1 ->
      fspec.(FS_Pre) w st1' ->
      ~ (χ f).(err) st1 /\
      forall st2, 
        (χ f).(nrm) st1 st2 ->
        exists st2', 
          join st2' stf st2 /\
          fspec.(FS_Post) w st2'.

  Definition valid_triple  (χ : func -> @denosem Σ): @HT_validity Σ (Langstmts) :=
    fun P c Q =>
    forall st1 st1' stf, join st1' stf st1 -> 
      P st1' -> ~ (evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) st1 /\ 
    forall st2, (evalnrm (fun f => (χ f).(nrm)) c) st1 st2 -> 
      exists st2', join st2' stf st2 /\ Q st2'.


  Definition valid_contextualtriple (Delta : funcspecs) : @HT_validity Σ (Langstmts) :=
    fun  (P : assertion) (c : (Langstmts)) (Q : assertion) =>
    forall χ,
    funcspecs_sat χ Delta ->
    valid_triple χ P c Q.
  Lemma funcspecs_equivforall : forall Δ χ ,
    funcspecs_sat χ Δ <-> Forall (fun '(f, fspec) => (forall st1 st1' stf (w : fspec.(FS_With)),
    join st1' stf st1 ->
    fspec.(FS_Pre) w st1' ->
    ~ (χ f).(err) st1 /\
    forall st2, 
      (χ f).(nrm) st1 st2 ->
      exists st2', 
        join st2' stf st2 /\
        fspec.(FS_Post) w st2')) Δ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold funcspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      eapply H;eauto.
  Qed. 
    

  Lemma funcspecs_sat_app : forall Δ1 Δ2 χ ,
    funcspecs_sat χ (Δ1 ++ Δ2) <->  (funcspecs_sat χ Δ1 /\  funcspecs_sat χ Δ2).
  Proof.
    intros.
    split;intros.
    - apply funcspecs_equivforall in H.
      apply Forall_app in H as [? ?].
      apply funcspecs_equivforall in H.
      apply funcspecs_equivforall in H0.
      split;auto.
    - apply funcspecs_equivforall.
      apply Forall_app.
      split.
      apply funcspecs_equivforall. tauto.
      apply funcspecs_equivforall. tauto.
  Qed.

End contextual_hoaretriples.


Section contextual_soundness.
  
  Context {Σ: Type}.
  Context {callc: @calllangclass Σ}.
  Context {joinm: @JoinM Σ}.

  Definition triple_body p Delta f fspec :=
    match find (fun fs => func_eqb (fst fs) f) p with
    | None => False
    | Some (_, c) =>
      forall w,
        valid_contextualtriple Delta (fspec.(FS_Pre) w) c (fspec.(FS_Post) w)
    end.

  Definition valid_triple_nrm  (χnrm : func -> Σ -> Σ -> Prop): @HT_validity Σ (Langstmts) :=
    fun P c Q =>
    forall st1 st1' stf, join st1' stf st1 ->  P st1' ->
    forall st2, (evalnrm (χnrm) c) st1 st2 -> 
      exists st2', join st2' stf st2 /\ Q st2'.

  Definition funcspecs_sat_nrm (χnrm : func -> Σ -> Σ -> Prop)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 st1' stf (w : fspec.(FS_With)),
      join st1' stf st1 ->
      fspec.(FS_Pre) w st1' ->
      forall st2, 
        (χnrm f) st1 st2 ->
        exists st2', 
          join st2' stf st2 /\
          fspec.(FS_Post) w st2'.

  Definition valid_contextualtriple_nrm (Delta : funcspecs) : @HT_validity Σ (Langstmts) :=
  fun  (P : assertion) (c : (Langstmts)) (Q : assertion) =>
  forall χnrm,
  funcspecs_sat_nrm χnrm Delta ->
  valid_triple_nrm χnrm P c Q.

  Definition triple_body_nrm p Delta f fspec :=
    match find (fun fs => func_eqb (fst fs) f) p with
    | None => False
    | Some (_, c) =>
      forall w,
        valid_contextualtriple_nrm Delta (fspec.(FS_Pre) w) c (fspec.(FS_Post) w)
    end.


  Definition funcspecs_sat_err (χ : func -> @denosem Σ)
      (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 st1' stf (w : fspec.(FS_With)),
    join st1' stf st1 ->
    fspec.(FS_Pre) w st1' ->
    ~ (χ f).(err) st1.


  Lemma funcspecs_sat_decompose:  forall (χnrm : func -> Σ -> Σ -> Prop) 
    (χerr : func -> Σ -> Prop) (Delta : funcspecs),
    funcspecs_sat_err (fun f => {| nrm:= χnrm f; err := χerr f |} ) Delta ->
    funcspecs_sat_nrm (χnrm) Delta ->
    funcspecs_sat (fun f => {| nrm:= χnrm f; err := χerr f |} ) Delta.
  Proof.
    unfold funcspecs_sat, funcspecs_sat_err, funcspecs_sat_nrm; cbn.
    intros.
    split.
    eapply H;eauto.
    eapply H0;eauto.
  Qed. 

  Lemma funcspecs_sat_nerr_false: forall (χnrm : func -> Σ -> Σ -> Prop) (Delta : funcspecs),
    funcspecs_sat_err (fun f => {| nrm:= χnrm f; err := (fun _ => ∅) f |} ) Delta.
  Proof.
    unfold funcspecs_sat_err. intros.
    unfold not. sets_unfold. auto.
  Qed. 


  Lemma triple_body_imply_nrm: forall p Delta f fspec,
    triple_body p Delta f fspec ->
    triple_body_nrm p Delta f fspec.
  Proof.
    unfold triple_body, triple_body_nrm.
    intros. 
    destruct (find (fun fs : func * Langstmts => func_eqb (fst fs) f) p)
     as [[f' c] | ] eqn:Hfind;auto.
    apply find_some in Hfind.
    simpl in Hfind.
    destruct Hfind as [HIn' Hf']. 
    rewrite func_eqb_eq in Hf'. 
    subst f'.
    intros w.
    unfold valid_contextualtriple_nrm.
    unfold valid_contextualtriple in H.
    intros.
    pose proof funcspecs_sat_decompose χnrm (fun f => ∅) Delta 
    (funcspecs_sat_nerr_false χnrm Delta) H0.
    specialize (H w _ H1).
    unfold valid_triple in H. 
    unfold valid_triple_nrm.
    intros.
    eapply H;eauto.
  Qed.
    
  Import ProgramSem.
  Lemma funcspecs_sat_triple_body_nrm : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun fs => triple_body_nrm p Delta (fst fs) (snd fs)) Delta) ->
    funcspecs_sat_nrm (prosem_nrm p) Delta.
  Proof.
    unfold triple_body_nrm, funcspecs_sat_nrm, valid_triple_nrm, prosem_nrm, Lfix.
    intros * HNoDup HT * HDelta * Hm1 HP * Hev.
    rewrite Forall_forall in HT.
    destruct Hev as [n Hev].
    revert HDelta Hm1 HP Hev. revert st1 st1' stf w st2. revert f fspec.
    induction n; simpl in *; [contradiction | ].
    remember (
      Nat.iter n
        (fun (X : func -> Σ -> Σ -> Prop) (f0 : func) (st3 st4 : Σ) =>
         exists c : Langstmts, In (f0, c) p /\ evalnrm X c st3 st4) ∅)
    as callees eqn:Hcallees in *.
    assert (funcspecs_sat_nrm callees Delta) as IHsat.
    { unfold funcspecs_sat_nrm. intros * HDelta * Hm1 HP * Hev.
      eapply IHn;eauto. }
    clear IHn.
    intros * HDelta * Hm1 HP Hev.
    destruct Hev as [c [HIn Hev] ].
    specialize (HT _ HDelta). simpl in HT.
    destruct (find (fun fs => func_eqb (fst fs) f) p) eqn:Hfind.
    2:{ pose proof (find_none _ _ Hfind _ HIn). simpl in H.
        rewrite func_eqb_refl in H. discriminate. }
    apply find_some in Hfind. 
    destruct p0 as [f' c'].
    simpl in Hfind.
    destruct Hfind as [HIn' Hf']. 
    rewrite func_eqb_eq in Hf'. 
    subst f'.
    rewrite <- (NoDup_map_fst _ _ _ _ _ _ HNoDup HIn HIn') in *.
    specialize (HT w callees IHsat st1 st1' stf Hm1 HP _ Hev) as [st2' [Hm2 HQ] ].
    exists st2'. auto.
  Qed.

  Lemma funcspecs_sat_triple_body_err : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun fs => triple_body p Delta (fst fs) (snd fs)) Delta) ->
    funcspecs_sat_err (prosem p) Delta.
  Proof.
    unfold funcspecs_sat_err,  prosem, Lfix;cbn.
    intros * HNoDup HT * HDelta * Hm1 HP Herr.
    assert (Forall (fun fs : func * funcspec => triple_body_nrm p Delta (fst fs) (snd fs))
    Delta ).
    { eapply Forall_impl.
      2: exact HT.
      intros [? ?]. cbn. intros.
      eapply triple_body_imply_nrm;eauto.
    }
    pose proof (funcspecs_sat_triple_body_nrm p Delta HNoDup H) as Hnrmsat.
    clear H.
    rewrite Forall_forall in HT.
    destruct Herr as [n Herr].
    revert HDelta Hm1 HP Herr. revert st1 st1' stf w. revert f fspec.
    induction n; simpl in *; [contradiction | ].
    remember (
      Nat.iter n
        (fun (X : func -> Σ -> Prop) (f0 : func) (st2 : Σ) =>
         exists c : Langstmts, In (f0, c) p /\ evalerr (prosem_nrm p) X c st2) ∅)
    as errcall eqn:Herrcall in *.
    intros * HDelta * Hm1 HP Herr.
    destruct Herr as [c [HIn Herr]].
    specialize (HT _ HDelta) as HT1. 
    simpl in HT1. unfold triple_body in HT1.
    destruct (find (fun fs => func_eqb (fst fs) f) p) eqn:Hfind.
    2:{ pose proof (find_none _ _ Hfind _ HIn). simpl in H.
    rewrite func_eqb_refl in H. discriminate. }
    apply find_some in Hfind. 
    destruct p0 as [f' c'].
    simpl in Hfind.
    destruct Hfind as [HIn' Hf']. 
    rewrite func_eqb_eq in Hf'. 
    subst f'.
    erewrite (NoDup_map_fst _ _ _ _ _ _ HNoDup HIn HIn') in *. 
    clear HIn'.
    assert (funcspecs_sat (fun f => {| nrm:= (prosem_nrm p) f; err := errcall f |} ) Delta).
    { unfold prosem.
      eapply funcspecs_sat_decompose;eauto.
      unfold funcspecs_sat_err.
      cbn. intros.
      unfold not. intros.
      eapply IHn;eauto.
    }
    specialize (HT1 w _ H st1 st1' stf Hm1 HP) as [? _]. clear H.
    cbn in H0.
    contradiction.
  Qed.

  Lemma funcspecs_sat_triple_body : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun fs => triple_body p Delta (fst fs) (snd fs)) Delta) ->
    funcspecs_sat (prosem p) Delta.
  Proof.
    intros * HNoDup HT.
    eapply funcspecs_sat_decompose;eauto.
    - (* err *)
      eapply funcspecs_sat_triple_body_err;eauto.
    - eapply funcspecs_sat_triple_body_nrm;eauto.
      eapply Forall_impl;eauto.
      intros [? ?] ?.
      simpl in *.
      eapply triple_body_imply_nrm;eauto.
  Qed. 

  Lemma contexthoare_imply_prosemhoare : forall ρ Delta P c Q,
    NoDup (map fst ρ) ->
    (Forall (fun fs => triple_body ρ Delta (fst fs) (snd fs)) Delta) ->
    valid_contextualtriple Delta P c Q ->
    valid_triple (prosem ρ) P c Q.
  Proof.
    intros.
    pose proof funcspecs_sat_triple_body _ _ H H0.
    unfold valid_contextualtriple in H1.
    specialize (H1 _ H2).
    auto.
  Qed. 

End contextual_soundness.
End ContextualJoinState.

