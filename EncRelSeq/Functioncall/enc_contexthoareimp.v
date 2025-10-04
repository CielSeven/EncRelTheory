From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basictacs basicasrt relasrt encdefs relhoarelogic safeexec_lib.
From EncRelSeq.UBError Require Import errsem hoarelogic relhoarelogic safeexec_lib.
From EncRelSeq Require Import callsem contexthoare contexthoare_imp. 
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import Idents .

Import SetsNotation.
Local Open Scope sets.

(*************************************************************************************************************)
(**********************************   Encode contextual relational triples   *********************************)
(**********************************             including errors             *********************************)
(**********************************   High-level setting                     *********************************)
(**********************************          1. high denosem  no  call       *********************************)
(*************************************************************************************************************)
Module RelJoinStateGlobalEnvHighNoCall.

Import practicaldeno.
Import RelHoarePracticalDeno.
Import PracticalDenoConstructs.
Import HoarePracticalDeno.
Import ContextualJoinStateGlobalEnv.

Section contextual_relationaltriples.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Context {Σₕ: Type}.

  Definition relassertion := @relasrt local_cstate Σₕ (@denosem Σₕ).
  Record relfuncspec : Type := mk_relfuncspec {
    rFS_With : Type;
    rFS_Pre : rFS_With -> relassertion;
    rFS_Post : rFS_With -> relassertion;
  }.

  (* funcspecs_sat *)

  Definition relfuncspecs : Type := list (func * relfuncspec).

  Definition relfuncspecs_sat (χ : func -> @denosem global_cstate)
                        (Gamma : relfuncspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Gamma -> 
    forall (w : fspec.(rFS_With)) lst1 lm1 lmf hst1 hstmt,
      join lm1 lmf lst1.(st_mem) ->
      fspec.(rFS_Pre) w ((mk_lstate lst1.(lenv) lst1.(genv) lm1), hst1, hstmt) ->
      ((χ f).(err) (mk_gstate lst1.(genv) lst1.(st_mem))  -> (hstmt).(err) hst1) /\
      forall lgst2, 
        (χ f).(nrm) (mk_gstate lst1.(genv) lst1.(st_mem)) lgst2 -> ((hstmt).(err) hst1) \/
        exists hst2 hstmt2, 
        ( hst1, hstmt ) ↪ ( hst2, hstmt2 ) /\
        exists lm2, join lm2 lmf lgst2.(gst_mem) /\
        fspec.(rFS_Post) w ((mk_lstate lst1.(lenv) lgst2.(ggenv) lm2), hst2, hstmt2).

  Definition valid_reltriple  (χ : func -> @denosem global_cstate) :=
    fun (P : relassertion) (c : Langstmts) (Q : relassertion) =>
    forall lst1 lm1 lmf hst1 hstmt1, join lm1 lmf lst1.(st_mem) -> P ((mk_lstate lst1.(lenv) lst1.(genv) lm1), hst1, hstmt1) ->  
            ((evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) lst1  ->  
            (hstmt1).(err) hst1) /\ 
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    ((hstmt1).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (hstmt1) ) ↪ ( hst2, (hstmt2) ) /\
    exists lm2, join lm2 lmf lst2.(st_mem) /\
    Q ((mk_lstate lst2.(lenv) lst2.(genv) lm2), hst2, hstmt2).


  Definition valid_contextualreltriple (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : Langstmts) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    valid_reltriple χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => forall (w : fspec.(rFS_With)) lst1 lm1 lmf hst1 hstmt,
    join lm1 lmf lst1.(st_mem) ->
    fspec.(rFS_Pre) w ((mk_lstate lst1.(lenv) lst1.(genv) lm1), hst1, hstmt) ->
    ((χ f).(err) (mk_gstate lst1.(genv) lst1.(st_mem))  -> (hstmt).(err) hst1) /\
    forall lgst2, 
      (χ f).(nrm) (mk_gstate lst1.(genv) lst1.(st_mem)) lgst2 -> ((hstmt).(err) hst1) \/
      exists hst2 hstmt2, 
      ( hst1, hstmt ) ↪ ( hst2, hstmt2 ) /\
      exists lm2, join lm2 lmf lgst2.(gst_mem) /\
      fspec.(rFS_Post) w ((mk_lstate lst1.(lenv) lgst2.(ggenv) lm2), hst2, hstmt2)) Γ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold relfuncspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      eapply H;eauto.
  Qed. 

End contextual_relationaltriples.
(*************************************************************************************************************)
(*******************************   encoding for contextual relational triples   ******************************)
(*************************************************************************************************************)
Section encode_contextual_triples.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Context {Σₕ: Type}.


  Definition encode_relfuncspec (rfspec: relfuncspec) : funcspec :=
    mk_funcspec ((Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => encode_asrt (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => encode_asrt (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt local_cstate Σₕ (@denosem Σₕ)) (cₗ: Langstmts) (Q : @relasrt local_cstate Σₕ (@denosem Σₕ)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt P X)
                        cₗ 
                        (encode_asrt Q X).


End encode_contextual_triples.

Notation " '(|' Γ '|)'  " := (encode_relfuncspecs Γ)  (at level 20, no associativity). 

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Import Coq.Logic.Classical_Prop.

Section contextual_validity_soundness.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Context {Σₕ: Type}.

  Local Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple Δ Γ P c Q) (at level 71, no associativity).
  Local Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT Δ Γ P c Q) (at level 71, no associativity).


  Lemma funcspecs_equiv_relfuncspecs:  forall (Γ : relfuncspecs) (χ: func -> denosem),
    funcspecs_sat χ (@encode_relfuncspecs lgst Σₕ Γ) <-> 
    relfuncspecs_sat χ Γ.
  Proof.
    induction Γ;intros.
    - split;intros. 
      apply relfuncspecs_equivforall. constructor.
      cbn. apply funcspecs_equivforall. constructor.
    - split;intros.
      { apply relfuncspecs_equivforall.
      destruct a as [f fspec].
      cbn in H.
      apply funcspecs_equivforall in H.
      inversion H. subst.
      clear H.
      constructor;auto.
      + clear H3.
        intros.
        destruct fspec as [rfwith RP RQ].
        cbn in *.
        remember (fun hst => (hstmt).(nrm) hst1 hst) as X.
        specialize (H2 lst1 lm1 lmf (X, w) H).
        cbn in H2.
        split.
        * intros.
          pose proof classic ((hstmt).(err) hst1) as [ | ];[auto | ].
          assert (encode_asrt (RP w) X {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
          { unfold encode_asrt.
            do 2 eexists.
            split;eauto.
            unfold safe.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H4) as [? _].
          contradiction.
        * intros * HLeval.
          pose proof classic ((hstmt).(err) hst1) as [HHerr | HHnerr];[auto | ].
          right.
          assert (encode_asrt (RP w) X {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
          { unfold encode_asrt.
            do 2 eexists.
            split;eauto.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H1) as [_ ?].
          specialize (H2 _ HLeval).
          unfold encode_asrt in H2.
          destruct H2 as (lm2 & Hjoin & hst2 & hstmt2 & [? ?] & HQ).
          do 2 eexists.
          split;eauto.
          unfold config_refinement.
          split;intros.
          { subst X. eapply H3;eauto. }  
          contradiction.
      + apply relfuncspecs_equivforall.
        apply IHΓ.
        apply funcspecs_equivforall;auto. }
      apply funcspecs_equivforall.
      destruct a as [f fspec].
      cbn.
      apply relfuncspecs_equivforall in H.
      inversion H. subst.
      clear H.
      constructor;auto.
      + clear H3.
        intros.
        destruct fspec as [fwith P Q].
        cbn in *.
        destruct w as [X w].
        destruct H0 as (hst1 & hstmt & [HHerr HHnrm] & HP).
        specialize (H2 w _ _ _  hst1 hstmt H HP) as [Herr Hnrm].
        split.
        * intros.
          unfold not.
          intros.
          apply HHerr. intuition auto.
        * intros * HLeval.
          specialize (Hnrm _ HLeval).
          destruct Hnrm.
          contradiction.
          destruct H0 as (hst2 & hstmt2 & [Hheval1 Hheval2] & (lm2 & ? & ?)).
          eexists.
          split;eauto.
          exists hst2, hstmt2.
          split;auto.
          split;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem encoding_correctness : forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt local_cstate Σₕ (@denosem Σₕ)) (cₗ: Langstmts) 
    (Q : @relasrt local_cstate Σₕ (@denosem Σₕ)),
    Δ ⩅ Γ  ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT X χ HDelta lst1 lm1 lmf Hframe HP. 
      apply funcspecs_sat_app in HDelta as [HDelta HGamma].
      apply funcspecs_equiv_relfuncspecs in HGamma.
      specialize (HT _ HDelta HGamma).
      unfold valid_reltriple in HT.
      unfold encode_asrt in HP.
      destruct HP as (hst1 & hstmt1 & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ _ _ Hframe HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros lst2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as [ | (hst2 & hstmt2 & [Hheval Hhevalerr] & lm2 & Hframe2 & HQ) ];[contradiction | ].
      eexists.
      split;eauto.
      do 2 eexists. split;eauto.
      unfold safe.
      split;[cbn;auto | ].
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT χ HDelta HGamma lst1 lm1 lmf hst1 hstmt1 Hframe HP.
      specialize (HT (fun hst => (hstmt1).(nrm) hst1 hst) χ).
      assert (funcspecs_sat χ (Δ ++ encode_relfuncspecs Γ)).
      { apply funcspecs_sat_app.
        split;auto.
        apply funcspecs_equiv_relfuncspecs.
        auto. 
      }
      specialize (HT H lst1 _ _ Hframe).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (err (hstmt1) hst1) as [ | ];[auto | ].
        assert (encode_asrt P (fun hst : Σₕ => nrm hstmt1 hst1 hst)
        {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
        { unfold encode_asrt.
          do 2 eexists. split;eauto.
          split;auto. 
        }
        specialize (HT H2) as [? ?].
        contradiction.
      + intros lst2 Heval.
        (* excluded middle used *)
        pose proof classic (err (hstmt1) hst1) as [ | ];[auto | ].
        right.
        assert (encode_asrt P (fun hst : Σₕ => nrm hstmt1 hst1 hst)
        {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
        { unfold encode_asrt, lift.
          do 2 eexists. split;eauto.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        specialize (H3 _ Heval) as (lm2 & Hframe2 & H3). 
        unfold encode_asrt in H3.
        destruct H3 as [hst2 [hstmt2 [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold config_refinement;cbn.
        split.
        { intros. 
        unfold safe in H3.
        destruct H3 as [_ ?].
        sets_unfold in H3.
        auto. }
        intros.
        unfold safe in H3.
        destruct H3 as [? _].
        contradiction.
  Qed. 
  
End contextual_validity_soundness.
Local Open Scope asrt_scope. 
Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple Δ Γ P c Q) (at level 71, no associativity).
Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT Δ Γ P c Q) (at level 71, no associativity).

(**********************************************************************************)
(*    encode asrt rules                                                           *)
(**********************************************************************************)
Section  SepRAssertion.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  
  Context {Σₕ: Type}.

  Definition relexpr : Type := local_cstate * Σₕ * (@denosem Σₕ).
  Definition rjoin : (relexpr) -> (relexpr) -> (relexpr) -> Prop :=
    fun '(σₗ1, σₕ1, cₕ1) '(σₗ2, σₕ2, cₕ2) '(σₗ3, σₕ3, cₕ3) =>
        join σₗ1.(st_mem) σₗ2.(st_mem) σₗ3.(st_mem) /\ 
        σₗ1.(lenv) = σₗ2.(lenv) /\ σₗ2.(lenv) = σₗ3.(lenv) /\
        σₗ1.(genv) = σₗ2.(genv) /\ σₗ2.(genv) = σₗ3.(genv) /\ 
        σₕ1 = σₕ2 /\ σₕ2 = σₕ3 /\ 
        cₕ1 = cₕ2 /\ cₕ2 = cₕ3.

  Definition ris_unit : (relexpr) -> Prop := fun '(σₗ1, σₕ1, cₕ1) => is_unit σₗ1.(st_mem).


  #[export] Instance reljoinm: @JoinM relexpr := {
    join := rjoin;
    is_unit := ris_unit;
  }. 
  Definition SepAhst (P : Σₕ -> Prop ): @relasrt local_cstate Σₕ (@denosem Σₕ):= fun '(σₗ, σₕ, cₕ) =>  P σₕ /\ is_unit σₗ.(st_mem).

  Definition SepAspec (cₕ : @denosem Σₕ) : @relasrt local_cstate Σₕ (@denosem Σₕ):= fun '(σₗ, σₕ, c) =>  c = cₕ /\ is_unit σₗ.(st_mem).
End SepRAssertion.

Section  EncodeRules.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context {lmaxioms: @JoinMAxioms memory memm}.
  Context {Σₕ: Type}.


Local Open Scope sets_scope.
Ltac destructs H:= rel_destruct local_cstate Σₕ Langstmts (@denosem Σₕ) H.
Lemma encode_decomposed_sepcon: forall X (P: @asrt local_cstate) (P' : @asrt Σₕ) s,
 [| ⌊ P ⌋ ** SepAhst P' ** SepAspec s|](X) --||--  !! (Exec P' s X) && P. 
Proof.
  intros.
  intros σₗ;split.
  { unfold derivable1, sepcon, andp, coq_prop, encode_asrt, andp, Alst, SepAhst, SepAspec, Exec. simpl_hdefs. sets_unfold.
  intros.
  destructs H.
  simpl in *. 
  destruct x as ((? & ?) & ?). destruct x0 as ((? & ?) & ?).
  destruct x1 as ((? & ?) & ?). destruct x2 as ((? & ?) & ?).
  simpl in *.
  destructs H4.
  destructs H2.
  subst.
  destruct_st σₗ. destruct_st l. destruct_st l0. destruct_st l1. destruct_st l2.
  cbn in *. subst. destructs H1. subst. 
  destructs H0. subst.
  apply unit_spec in H1;auto.
  apply unit_spec in H0;auto.
  subst.
  split;auto.
  eexists;
  split;eauto. }

  unfold derivable1, sepcon, andp, coq_prop, encode_asrt, andp, Alst, SepAhst, SepAspec, Exec. simpl_hdefs. sets_unfold.
  intros.
  destructs H.
  do 2 eexists.
  split;eauto.
  destruct_st σₗ.
  pose proof unit_join m as [m0 [? ?]].
  exists ({| lenv := l; genv := g; st_mem := m |}, σₕ, s).
  exists ({| lenv := l; genv := g; st_mem := m0 |}, σₕ, s).
  cbn.
  splits;auto.
  exists ({| lenv := l; genv := g; st_mem := m |}, σₕ, s), ({| lenv := l; genv := g; st_mem := m0 |}, σₕ, s).
  cbn.
  splits;auto.
Qed.

End  EncodeRules.

(**********************************************************************************)
(*    hoare rules                                                                 *)
(**********************************************************************************)
Section  encrules.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context {lmaxioms: @JoinMAxioms memory memm}.

  Context {Σₕ: Type}.
  Context (Δ : funcspecs).
  Context (Γ : @relfuncspecs lgst Σₕ).

  Local Open Scope sets_scope.

  Ltac destructs H:= rel_destruct local_cstate Σₕ Langstmts (@denosem Σₕ) H.

  
(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)

  Lemma  reltriple_triple_equiv1 : forall P Ps (s: @denosem Σₕ) c Q,
    Δ ⩅ Γ ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ₕ s ]ₕ ⟩ c ⟨ Q ⟩ <->
    (forall X, (Δ ++ (| Γ |)) ⊢ {{!! Exec Ps s X && P}} c {{[| Q |](X)}}).
  Proof.
    intros;split.
    - intros. apply encoding_correctness in H. 
    specialize (H X). simpl_ldefs.
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_2 (encode_decomposed X P Ps s)).
    cbv. auto.
    - intros. apply encoding_correctness.
      unfold valid_contextualrelT. intros.
      specialize (H X).
      eapply hoare_conseq;eauto.
      apply (logic_equiv_derivable1_1 (encode_decomposed X P Ps s)).
      cbv. auto.
  Qed.

  Lemma  reltriple_triple_equiv {A: Type}: forall P Ps (s: @denosem Σₕ) c B Q Ps',
    Δ ⩅ Γ ⊢ ⟨ ⌊ P ⌋ && ⌈ Ps ⌉ && [ₕ s ]ₕ ⟩ c ⟨EX (a:A), !! (B a) && ⌊ Q a ⌋ && ⌈ Ps' a⌉ && [ₕ skip ]ₕ ⟩ <->
    (forall X : Σₕ -> Prop,
    (Δ ++ (| Γ |)) ⊢ {{!! Exec Ps s X && P}} c {{EX a, !! Exec (Ps' a) skip X && !! (B a) && (Q a)}}).
  Proof.
    intros;split.
    - intros.
      apply encoding_correctness in H.
    specialize (H X).  simpl_ldefs. 
    eapply hoare_conseq;eauto.
    eapply (logic_equiv_derivable1_2 (encode_decomposed X P Ps s)).
    apply logic_equiv_derivable1_1.
    apply encode_normal_form.
    - intros. apply encoding_correctness.
      unfold valid_contextualrelT. intros.
      specialize (H X). 
      eapply hoare_conseq;eauto.
      apply (logic_equiv_derivable1_1 (encode_decomposed X P Ps s)).
      apply logic_equiv_derivable1_2.
      apply encode_normal_form.
  Qed.

  Lemma high_focus_as_conseqpre cₗ (cₕ1 cₕ2: @denosem Σₕ) F P R Q:
    forall X,
    ⊢∃ {{P}} cₕ1 {{R}}  ->
    (Δ ++ (| Γ |)) ⊢ {{!! Exec R cₕ2 X && F}} cₗ {{[|Q|](X)}} ->
    (Δ ++ (| Γ |)) ⊢ {{!! Exec P (seq cₕ1 cₕ2) X && F}} cₗ {{[|Q|](X)}}.
  Proof.
    intros.
    eapply hoare_conseq_pre;[ | eauto].
    apply derivable1_andp_mono;[ | reflexivity].
    apply coq_prop_imply.
    eapply PracticalDenoExecLib.highstepseq_derive;eauto.
  Qed.

  Lemma comp_fc_as_conseq :forall 
  P (cₗ: Langstmts) (cₕ: denosem) Q (Pₕ Qₕ: @asrt Σₕ),
  ((forall X,  (Δ ++ (| Γ |)) ⊢ {{ [|↑ P && [ₕ cₕ ]ₕ|](X) }} cₗ {{ [|↑ Q && [ₕ skip ]ₕ|](X) }})) -> 
  ⊢∀ {{ Pₕ }} cₕ {{ Qₕ }} ->
   (Δ ++ (| Γ |)) ⊢ {{ P ⋈_π Pₕ }} cₗ {{ Q ⋈_π Qₕ }}.
Proof.
  intros * HRT HHT.
  eapply hoare_conseq_pre.  
  { apply (logic_equiv_derivable1_2 (comp_proj_equiv _ _ )). }
  eapply hoare_exists_intro; intros σₕ.
  eapply hoare_coqprop_preintro. intros HPH.
  specialize (HRT (fun (x: Σₕ) => (nrm cₕ) σₕ x)).
  eapply hoare_conseq;eauto.
  - intros st1 ?.
    unfold encode_asrt, lift, basicasrt.andp, Aspec. simpl.
    do 2 eexists. split;[ | eauto].
    specialize (HHT _ HPH)  as [? ?].
    unfold weakestpre.
    split;auto. 
  - intros st1 HQ.
    unfold encode_asrt, lift, basicasrt.andp, Aspec in HQ.
    destruct HQ as [σₕ' [cₕ' [? [? ?]]]]. subst. simpl_hdefs.
    rewrite weakestpre_skip in H. simpl in H.
    specialize (HHT _ HPH ) as [? ?].
    specialize (H2 _ H).
    do 2 eexists. cbv. split;eauto.
Qed.

End encrules.

End RelJoinStateGlobalEnvHighNoCall.

