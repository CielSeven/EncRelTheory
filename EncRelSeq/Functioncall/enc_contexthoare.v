From SetsClass Require Import SetsClass.
From EncRelSeq.Basics Require Import basicasrt relasrt encdefs relhoarelogic safeexec_lib.
From EncRelSeq.UBError Require Import errsem hoarelogic relhoarelogic safeexec_lib.
From EncRelSeq Require Import callsem contexthoare. 
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import Idents .

Import SetsNotation.
Local Open Scope sets.

(***************************************************************************************************)
(************************   Encode contextual relational triples   *********************************)
(************************   High-level Setting                     *********************************)
(************************          1. high denosem no call          *********************************)
(***************************************************************************************************)
Module RelNormalFuncallHighNoCall.

Import normaldeno.
Import CallNormalDeno.
Import ProgramSem.
Import ContextualNormal.
Import HoareNormalDeno.
Import RelHoareNormalDeno.

Section contextual_relationaltriples.
  Context {Σₗ Σₕ: Type}.
  Context {callcₗ : @calllangclass Σₗ}.

  Definition relassertion : Type := @relasrt Σₗ Σₕ (@denosem Σₕ).
  Record relfuncspec : Type := mk_relfuncspec {
    rFS_With : Type;
    rFS_Pre : rFS_With -> relassertion;
    rFS_Post : rFS_With -> relassertion;
  }.

  Definition relfuncspecs : Type := list (func * relfuncspec).

  Definition relfuncspecs_sat (χ : func -> @denosem Σₗ)
                        (Gamma : relfuncspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Gamma -> 
    forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    forall lst2, 
    (χ f).(nrm) lst1 lst2 ->
    exists hst2 hstmt2, 
    ( hst1, hstmt ) ↪ ( hst2, hstmt2 ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2).

  Definition valid_reltriple  (χ : func -> @denosem Σₗ) :=
    fun (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall lst1 hst1 hstmt1, P (lst1, hst1, hstmt1) ->  
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    exists hst2 hstmt2, 
    ( hst1, hstmt1 ) ↪ ( hst2, hstmt2 ) /\
    Q (lst2, hst2, hstmt2).


  Definition valid_contextualreltriple (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    valid_reltriple χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => (forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    forall lst2, 
    (χ f).(nrm) lst1 lst2 -> 
    exists hst2 hstmt2, 
    ( hst1, (hstmt) ) ↪ ( hst2, (hstmt2) ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2))) Γ.
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

(******************************************************************************************************)
(************************   encoding for contextual relational triples   ******************************)
(******************************************************************************************************)

Section encode_contextual_triples.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  
  Definition encode_relfuncspec (rfspec: relfuncspec) : funcspec :=
    mk_funcspec ((Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => @encode_asrt Σₗ Σₕ _ _ _ (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => @encode_asrt Σₗ Σₕ _ _ _ (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt P X)
                        cₗ 
                        (encode_asrt Q X).


End encode_contextual_triples.

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Section contextual_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.

  Local Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple Δ Γ P c Q) (at level 71, no associativity).
  Local Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT Δ Γ P c Q) (at level 71, no associativity).


  Lemma funcspecs_equiv_relfuncspecs:  forall (Γ : relfuncspecs) (χ: func -> denosem),
    funcspecs_sat χ (@encode_relfuncspecs Σₗ Σₕ  Γ) <-> 
    relfuncspecs_sat  χ Γ.
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
        specialize (H2 lst1 (X, w)).
        cbn in H2.
          rename H0 into HLeval.
          assert (encode_asrt (RP w) X lst1).
          { unfold encode_asrt.
            do 2 eexists.
            split;eauto.
            simpl_hdefs.
            unfold weakestpre. sets_unfold.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H0) as ?.
          specialize (H1 _ HLeval).
          unfold encode_asrt in H1.
          destruct H1 as (hst2 & hstmt2 & ? & HQ).
          do 2 eexists.
          split;eauto.
          unfold config_refinement.
          intros. subst X. eapply H1;eauto. 
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
        destruct H as (hst1 & hstmt & HHnrm & HP).
        specialize (H2 w st1 hst1 hstmt HP) as  Hnrm.
          rename H0 into HLeval.
          specialize (Hnrm _ HLeval).
          destruct Hnrm as (hst2 & hstmt2 &  Hheval & HQ).
          exists hst2, hstmt2.
          split;auto. simpl_hdefs.
          unfold HoareNormalDeno.weakestpre in *. sets_unfold.
          intros;auto. apply HHnrm;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem validity_lemma : forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) 
    (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)),
    Δ ⩅ Γ  ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT X χ HDelta lst1 HP.
      apply funcspecs_sat_app in HDelta as [HDelta HGamma].
      apply funcspecs_equiv_relfuncspecs in HGamma.
      specialize (HT _ HDelta HGamma).
      unfold valid_reltriple in HT.
      unfold encode_asrt in HP.
      destruct HP as (hst1 & hstmt1 & Hhnrm & HP).
      specialize (HT _ _ _ HP) as  Hnrm.
      intros lst2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as (hst2 & hstmt2 & Hheval & HQ).
      do 2 eexists. split;[ | eauto].
      eapply configrefine_decompose with (X:= X)  in Hheval;eauto.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT χ HDelta HGamma lst1 hst1 hstmt1 HP.
      specialize (HT (fun hst => (hstmt1).(nrm) hst1 hst) χ).
      assert (funcspecs_sat χ (Δ ++ encode_relfuncspecs Γ)).
      { apply funcspecs_sat_app.
        split;auto.
        apply funcspecs_equiv_relfuncspecs.
        auto. 
      }
      specialize (HT H lst1).
      intros lst2 Heval.
        assert (encode_asrt P
        (fun hst : Σₕ =>
         nrm ( hstmt1) hst1 hst) lst1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;eauto. simpl_hdefs.
          unfold weakestpre. sets_unfold.
          intros;auto. 
        }
        specialize (HT H0) as ?.
        specialize (H1 _ Heval). 
        unfold encode_asrt in H1.
        destruct H1 as [hst2 [hstmt2 [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold config_refinement.
        intros.  eapply H1;eauto. 
  Qed. 
  
End contextual_validity_soundness.

End RelNormalFuncallHighNoCall.



(*************************************************************************************************************)
(**********************************   Encode contextual relational triples   *********************************)
(**********************************             including errors             *********************************)
(**********************************   High-level setting                     *********************************)
(**********************************          1. high denosemno call          *********************************)
(*************************************************************************************************************)
Module RelPracticalFuncallHighNoCall.

Import practicaldeno.
Import CallPracticalDeno.
Import ProgramSem.
Import ContextualPractical.
Import HoarePracticalDeno.
Import RelHoarePracticalDeno.
Import PracticalDenoExecLib.
Section contextual_relationaltriples.
  Context {Σₗ Σₕ: Type}.
  Context {callcₗ : @calllangclass Σₗ}.

  Definition relassertion := @relasrt Σₗ Σₕ (@denosem Σₕ).
  Record relfuncspec : Type := mk_relfuncspec {
    rFS_With : Type;
    rFS_Pre : rFS_With -> relassertion;
    rFS_Post : rFS_With -> relassertion;
  }.

  Definition relfuncspecs : Type := list (func * relfuncspec).

  Definition relfuncspecs_sat (χ : func -> @denosem Σₗ)
                        (Gamma : relfuncspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Gamma -> 
    forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    ((χ f).(err) lst1  -> (hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 -> (hstmt.(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, hstmt ) ↪ ( hst2, hstmt2 ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2).

  Definition valid_reltriple  (χ : func -> @denosem Σₗ) :=
    fun (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall lst1 hst1 hstmt1, P (lst1, hst1, hstmt1) ->  
            ((evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) lst1  ->  
            ( hstmt1).(err) hst1) /\ 
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    (hstmt1.(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, hstmt1 ) ↪ ( hst2, hstmt2 ) /\
    Q (lst2, hst2, hstmt2).


  Definition valid_contextualreltriple (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    valid_reltriple χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => (forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    ((χ f).(err) lst1  -> (hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 ->  ((hstmt).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (hstmt) ) ↪ ( hst2, (hstmt2) ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2))) Γ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold relfuncspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      apply H;auto.
  Qed. 

End contextual_relationaltriples.

(*************************************************************************************************************)
(*******************************   encoding for contextual relational triples   ******************************)
(*************************************************************************************************************)
Section encode_contextual_triples.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.


  Definition encode_relfuncspec (rfspec: relfuncspec) : funcspec :=
    mk_funcspec ((Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => @encode_asrt Σₗ Σₕ (@denosem Σₕ) _ _ (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => encode_asrt (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt P X)
                        cₗ 
                        (encode_asrt Q X).


End encode_contextual_triples.

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Import Coq.Logic.Classical_Prop.
Section contextual_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.

  Local Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple Δ Γ P c Q) (at level 71, no associativity).
  Local Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT Δ Γ P c Q) (at level 71, no associativity).


  Lemma funcspecs_equiv_relfuncspecs:  forall (Γ : relfuncspecs) (χ: func -> denosem),
    funcspecs_sat χ (@encode_relfuncspecs Σₗ Σₕ  Γ) <-> 
    relfuncspecs_sat  χ Γ.
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
        specialize (H2 lst1 (X, w)).
        cbn in H2.
        split.
        * intros.
          pose proof classic ((hstmt).(err) hst1) as [ | ];[auto | ].
          assert (encode_asrt (RP w) X lst1).
          { unfold encode_asrt.
            do 2 eexists.
            split;eauto.
            simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H3) as [? _].
          contradiction.
        * intros * HLeval.
          pose proof classic ((hstmt).(err) hst1) as [HHerr | HHnerr];[auto | ].
          right.
          assert (encode_asrt (RP w) X lst1).
          { unfold encode_asrt.
            do 2 eexists.
            split;eauto.
            simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H0) as [_ ?].
          specialize (H1 _ HLeval).
          unfold encode_asrt in H1.
          destruct H1 as (hst2 & hstmt2 & [? ?] & HQ).
          do 2 eexists.
          split;eauto.
          unfold config_refinement.
          split;intros.
          { subst X. eapply H2;eauto. }  
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
        destruct H as (hst1 & hstmt & [HHerr HHnrm] & HP).
        specialize (H2 w st1 hst1 hstmt HP) as [Herr Hnrm].
        split.
        * intros.
          unfold not.
          intros.
          apply HHerr. intuition auto.
        * intros * HLeval.
          specialize (Hnrm _ HLeval).
          destruct Hnrm.
          contradiction.
          destruct H as (hst2 & hstmt2 & [Hheval1 Hheval2] & HQ).
          exists hst2, hstmt2.
          split;auto.
          simpl_hdefs. unfold weakestpre.
          split;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem validity_lemma : forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt Σₗ Σₕ (@denosem Σₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) 
    (Q : @relasrt Σₗ Σₕ (@denosem Σₕ)),
    Δ ⩅ Γ  ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT X χ HDelta lst1 HP.
      apply funcspecs_sat_app in HDelta as [HDelta HGamma].
      apply funcspecs_equiv_relfuncspecs in HGamma.
      specialize (HT _ HDelta HGamma).
      unfold valid_reltriple in HT.
      unfold encode_asrt in HP.
      destruct HP as (hst1 & hstmt1 & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros lst2 Heval.
      unfold encode_asrt.
      specialize (Hnrm _ Heval) as [ | (hst2 & hstmt2 & [Hheval Hhevalerr] & HQ) ];[contradiction | ].
      subst.
      do 2 eexists. split;eauto.
      simpl_hdefs. unfold weakestpre.
      split;[cbn;auto | ].
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT χ HDelta HGamma lst1 hst1 hstmt1 HP.
      specialize (HT (fun hst => (hstmt1).(nrm) hst1 hst) χ).
      assert (funcspecs_sat χ (Δ ++ encode_relfuncspecs Γ)).
      { apply funcspecs_sat_app.
        split;auto.
        apply funcspecs_equiv_relfuncspecs.
        auto. 
      }
      specialize (HT H lst1).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (err (hstmt1) hst1) as [ | ];[auto | ].
        assert (encode_asrt P
        (fun hst : Σₕ =>
         nrm (hstmt1) hst1 hst) lst1).
        { unfold encode_asrt.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H2) as [? ?].
        contradiction.
      + intros lst2 Heval.
        (* excluded middle used *)
        pose proof classic (err (hstmt1) hst1) as [ | ];[auto | ].
        right.
        assert (encode_asrt P
        (fun hst : Σₕ =>
         nrm ( hstmt1) hst1 hst) lst1).
        { unfold encode_asrt, lift.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        specialize (H3 _ Heval). 
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

End RelPracticalFuncallHighNoCall.



(*************************************************************************************************************)
(**********************************   Encode contextual relational triples   *********************************)
(**********************************             including errors             *********************************)
(**********************************   High-level setting                     *********************************)
(**********************************          1. high denosemwith call        *********************************)
(*************************************************************************************************************)
Module RelPracticalFuncall.

Import practicaldeno.
Import CallPracticalDeno.
Import ProgramSem.
Import ContextualPractical.
Import HoarePracticalDeno.
Import RelHoarePracticalDeno.
Import PracticalDenoExecLib.
Section contextual_relationaltriples.
  Context {Σₗ Σₕ: Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).

  Definition relassertion := @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ).
  Record relfuncspec : Type := mk_relfuncspec {
    rFS_With : Type;
    rFS_Pre : rFS_With -> relassertion;
    rFS_Post : rFS_With -> relassertion;
  }.

  Definition evalh := eval ρₕ.

  Definition relfuncspecs : Type := list (func * relfuncspec).

  Definition relfuncspecs_sat (χ : func -> @denosem Σₗ)
                        (Gamma : relfuncspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Gamma -> 
    forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    ((χ f).(err) lst1  -> (evalh hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 -> ((evalh hstmt).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt) ) ↪ ( hst2, (evalh hstmt2) ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2).

  Definition valid_reltriple  (χ : func -> @denosem Σₗ) :=
    fun (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall lst1 hst1 hstmt1, P (lst1, hst1, hstmt1) ->  
            ((evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) lst1  ->  
            (evalh hstmt1).(err) hst1) /\ 
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    ((evalh hstmt1).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt1) ) ↪ ( hst2, (evalh hstmt2) ) /\
    Q (lst2, hst2, hstmt2).


  Definition valid_contextualreltriple (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    valid_reltriple χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => (forall (w : fspec.(rFS_With)) lst1 hst1 hstmt,
    fspec.(rFS_Pre) w (lst1, hst1, hstmt) ->
    ((χ f).(err) lst1  -> (evalh hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 ->  ((evalh hstmt).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt) ) ↪ ( hst2, (evalh hstmt2) ) /\
    fspec.(rFS_Post) w (lst2, hst2, hstmt2))) Γ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold relfuncspecs_sat. intros.
      eapply Forall_forall in H;eauto.
      apply H;auto.
  Qed. 

End contextual_relationaltriples.

(*************************************************************************************************************)
(*******************************   encoding for contextual relational triples   ******************************)
(*************************************************************************************************************)
Section encode_contextual_triples.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).


  Definition encode_asrt_expr  (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (X: Σₕ -> Prop): @asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (@Langstmts Σₕ callcₕ)),  
           safe σₕ (evalh ρₕ cₕ)  X /\  P (σₗ, σₕ, cₕ).

  Definition encode_relfuncspec (rfspec: relfuncspec) : funcspec :=
    mk_funcspec ((Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => encode_asrt_expr (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => encode_asrt_expr (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) (Q : @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt_expr P X)
                        cₗ 
                        (encode_asrt_expr Q X).


End encode_contextual_triples.

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Import Coq.Logic.Classical_Prop.
Section contextual_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).

  Local Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple ρₕ Δ Γ P c Q) (at level 71, no associativity).
  Local Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT ρₕ Δ Γ P c Q) (at level 71, no associativity).


  Lemma funcspecs_equiv_relfuncspecs:  forall (Γ : relfuncspecs) (χ: func -> denosem),
    funcspecs_sat χ (@encode_relfuncspecs Σₗ Σₕ callcₕ ρₕ Γ) <-> 
    relfuncspecs_sat ρₕ χ Γ.
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
        remember (fun hst => (evalh ρₕ hstmt).(nrm) hst1 hst) as X.
        specialize (H2 lst1 (X, w)).
        cbn in H2.
        split.
        * intros.
          pose proof classic ((evalh ρₕ hstmt).(err) hst1) as [ | ];[auto | ].
          assert (encode_asrt_expr ρₕ (RP w) X lst1).
          { unfold encode_asrt_expr.
            do 2 eexists.
            split;eauto.
            unfold safe. simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H3) as [? _].
          contradiction.
        * intros * HLeval.
          pose proof classic ((evalh ρₕ hstmt).(err) hst1) as [HHerr | HHnerr];[auto | ].
          right.
          assert (encode_asrt_expr ρₕ (RP w) X lst1).
          { unfold encode_asrt_expr.
            do 2 eexists.
            split;eauto.
            simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H0) as [_ ?].
          specialize (H1 _ HLeval).
          unfold encode_asrt_expr in H1.
          destruct H1 as (hst2 & hstmt2 & [? ?] & HQ).
          do 2 eexists.
          split;eauto.
          unfold config_refinement.
          split;intros.
          { subst X. eapply H2;eauto. }  
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
        destruct H as (hst1 & hstmt & [HHerr HHnrm] & HP).
        specialize (H2 w st1 hst1 hstmt HP) as [Herr Hnrm].
        split.
        * intros.
          unfold not.
          intros.
          apply HHerr. intuition auto.
        * intros * HLeval.
          specialize (Hnrm _ HLeval).
          destruct Hnrm.
          contradiction.
          destruct H as (hst2 & hstmt2 & [Hheval1 Hheval2] & HQ).
          exists hst2, hstmt2.
          split;auto.
          simpl_hdefs. unfold weakestpre.
          split;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem validity_lemma : forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) 
    (Q : @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)),
    Δ ⩅ Γ  ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT X χ HDelta lst1 HP.
      apply funcspecs_sat_app in HDelta as [HDelta HGamma].
      apply funcspecs_equiv_relfuncspecs in HGamma.
      specialize (HT _ HDelta HGamma).
      unfold valid_reltriple in HT.
      unfold encode_asrt_expr in HP.
      destruct HP as (hst1 & hstmt1 & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros lst2 Heval.
      unfold encode_asrt_expr.
      specialize (Hnrm _ Heval) as [ | (hst2 & hstmt2 & [Hheval Hhevalerr] & HQ) ];[contradiction | ].
      subst.
      do 2 eexists. split;eauto.
      simpl_hdefs. unfold weakestpre.
      split;[cbn;auto | ].
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT χ HDelta HGamma lst1 hst1 hstmt1 HP.
      specialize (HT (fun hst => (evalh ρₕ hstmt1).(nrm) hst1 hst) χ).
      assert (funcspecs_sat χ (Δ ++ encode_relfuncspecs ρₕ Γ)).
      { apply funcspecs_sat_app.
        split;auto.
        apply funcspecs_equiv_relfuncspecs.
        auto. 
      }
      specialize (HT H lst1).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (err (evalh ρₕ hstmt1) hst1) as [ | ];[auto | ].
        assert (encode_asrt_expr ρₕ P
        (fun hst : Σₕ =>
         nrm (evalh ρₕ hstmt1) hst1 hst) lst1).
        { unfold encode_asrt_expr.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H2) as [? ?].
        contradiction.
      + intros lst2 Heval.
        (* excluded middle used *)
        pose proof classic (err (evalh ρₕ hstmt1) hst1) as [ | ];[auto | ].
        right.
        assert (encode_asrt_expr ρₕ P
        (fun hst : Σₕ =>
         nrm (evalh ρₕ hstmt1) hst1 hst) lst1).
        { unfold encode_asrt_expr, lift.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        specialize (H3 _ Heval). 
        unfold encode_asrt_expr in H3.
        destruct H3 as [hst2 [hstmt2 [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold config_refinement;cbn.
        split.
        { intros. 
        unfold safe in H3.
        destruct H3 as [_ ?].
        sets_unfold in H3. cbn in H3.
        auto. }
        intros.
        unfold safe in H3.
        destruct H3 as [? _].
        contradiction.
  Qed. 
  
End contextual_validity_soundness.

End RelPracticalFuncall.



(*************************************************************************************************************)
(**********************************   Encode contextual relational triples   *********************************)
(**********************************             including errors             *********************************)
(**********************************   High-level setting                     *********************************)
(**********************************          1. high denosemwith call        *********************************)
(**********************************   Concrete Pro Setting                   *********************************)
(**********************************         1.program state join             *********************************)
(**********************************           valid triple has state frame   *********************************)
(**********************************         2. χ: func -> deno Σ             *********************************)
(*************************************************************************************************************)

Module RelConcreteJoinFuncall.

Import practicaldeno.
Import CallPracticalDeno.
Import ProgramSem.
Import ContextualJoinState.
Import HoarePracticalDeno.
Import RelHoarePracticalDeno.
Import PracticalDenoExecLib.
Section contextual_relationaltriples.
  Context {Σₗ Σₕ: Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {joinm: @JoinM Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).

  Definition relassertion := @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ).
  Record relfuncspec : Type := mk_relfuncspec {
    rFS_With : Type;
    rFS_Pre : rFS_With -> relassertion;
    rFS_Post : rFS_With -> relassertion;
  }.

  Definition evalh := eval ρₕ.

  Definition relfuncspecs : Type := list (func * relfuncspec).

  Definition relfuncspecs_sat (χ : func -> @denosem Σₗ)
                        (Gamma : relfuncspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Gamma -> 
    forall (w : fspec.(rFS_With)) lst1 lst1' lstf hst1 hstmt,
    join lst1' lstf lst1 ->
    fspec.(rFS_Pre) w (lst1', hst1, hstmt) ->
    ((χ f).(err) lst1  -> (evalh hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 -> ((evalh hstmt).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt) ) ↪ ( hst2, (evalh hstmt2) ) /\
    exists lst2', join lst2' lstf lst2 /\
    fspec.(rFS_Post) w (lst2', hst2, hstmt2).

  Definition valid_reltriple  (χ : func -> @denosem Σₗ) :=
    fun (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall lst1 lst1' lstf hst1 hstmt1, join lst1' lstf lst1 -> P (lst1', hst1, hstmt1) ->  
            ((evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) lst1  ->  
            (evalh hstmt1).(err) hst1) /\ 
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    ((evalh hstmt1).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt1) ) ↪ ( hst2, (evalh hstmt2) ) /\
    exists lst2', join lst2' lstf lst2 /\
    Q (lst2', hst2, hstmt2).


  Definition valid_contextualreltriple (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : (@Langstmts Σₗ callcₗ)) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    valid_reltriple χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => forall (w : fspec.(rFS_With)) lst1 lst1' lstf hst1 hstmt,
    join lst1' lstf lst1 ->
    fspec.(rFS_Pre) w (lst1', hst1, hstmt) ->
    ((χ f).(err) lst1  -> (evalh hstmt).(err) hst1) /\
    forall lst2, 
    (χ f).(nrm) lst1 lst2 -> ((evalh hstmt).(err) hst1) \/
    exists hst2 hstmt2, 
    ( hst1, (evalh hstmt) ) ↪ ( hst2, (evalh hstmt2) ) /\
    exists lst2', join lst2' lstf lst2 /\
    fspec.(rFS_Post) w (lst2', hst2, hstmt2)) Γ.
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
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {joinm: @JoinM Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).

  Definition encode_asrt_expr  (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (X: Σₕ -> Prop): @asrt Σₗ :=
  fun σₗ => exists (σₕ: Σₕ) (cₕ: (@Langstmts Σₕ callcₕ)),  
           safe σₕ (evalh ρₕ cₕ) X /\ P (σₗ, σₕ, cₕ).

  Definition encode_relfuncspec (rfspec: relfuncspec) : funcspec :=
    mk_funcspec ((Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => encode_asrt_expr (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => encode_asrt_expr (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) (Q : @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt_expr P X)
                        cₗ 
                        (encode_asrt_expr Q X).


End encode_contextual_triples.

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Import Coq.Logic.Classical_Prop.

Section contextual_validity_soundness.
  Context {Σₗ Σₕ : Type}.
  Context {callcₗ : @calllangclass Σₗ}.
  Context {joinm: @JoinM Σₗ}.
  Context {callcₕ : @calllangclass Σₕ}.
  Context (ρₕ: @program Σₕ callcₕ).

  Local Notation " Δ ⩅ Γ '⊢' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualreltriple ρₕ Δ Γ P c Q) (at level 71, no associativity).
  Local Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT ρₕ Δ Γ P c Q) (at level 71, no associativity).


  Lemma funcspecs_equiv_relfuncspecs:  forall (Γ : relfuncspecs) (χ: func -> denosem),
    funcspecs_sat χ (@encode_relfuncspecs Σₗ Σₕ callcₕ ρₕ Γ) <-> 
    relfuncspecs_sat ρₕ χ Γ.
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
        remember (fun hst => (evalh ρₕ hstmt).(nrm) hst1 hst) as X.
        specialize (H2 lst1 lst1' lstf (X, w) H).
        cbn in H2.
        split.
        * intros.
          pose proof classic ((evalh ρₕ hstmt).(err) hst1) as [ | ];[auto | ].
          assert (encode_asrt_expr ρₕ (RP w) X lst1').
          { unfold encode_asrt_expr.
            do 2 eexists.
            split;eauto.
            unfold safe. simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H4) as [? _].
          contradiction.
        * intros * HLeval.
          pose proof classic ((evalh ρₕ hstmt).(err) hst1) as [HHerr | HHnerr];[auto | ].
          right.
          assert (encode_asrt_expr ρₕ (RP w) X lst1').
          { unfold encode_asrt_expr.
            do 2 eexists.
            split;eauto.
            simpl_hdefs. unfold weakestpre.
            split;auto.
            intros.
            subst X.
            auto.
          }
          specialize (H2 H1) as [_ ?].
          specialize (H2 _ HLeval).
          unfold encode_asrt_expr in H2.
          destruct H2 as (lst2' & Hjoin & hst2 & hstmt2 & [? ?] & HQ).
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
          destruct H0 as (hst2 & hstmt2 & [Hheval1 Hheval2] & (lst2' & ? & ?)).
          eexists.
          split;eauto.
          exists hst2, hstmt2.
          split;auto.
          simpl_hdefs. unfold weakestpre.
          split;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem validity_lemma : forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)) (cₗ: (@Langstmts Σₗ callcₗ)) 
    (Q : @relasrt Σₗ Σₕ (@Langstmts Σₕ callcₕ)),
    Δ ⩅ Γ  ⊢ ⟨ P ⟩ cₗ ⟨ Q ⟩ <-> Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ cₗ ⟨ Q ⟩.
  Proof.
    intros;split.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT X χ HDelta lst1 lst1' lstf Hframe HP. 
      apply funcspecs_sat_app in HDelta as [HDelta HGamma].
      apply funcspecs_equiv_relfuncspecs in HGamma.
      specialize (HT _ HDelta HGamma).
      unfold valid_reltriple in HT.
      unfold encode_asrt_expr in HP.
      destruct HP as (hst1 & hstmt1 & [Hherr Hhnrm] & HP).
      specialize (HT _ _ _ _ _ Hframe HP) as [Herr Hnrm].
      split.
      + unfold not in *. intros. apply Hherr. intuition auto.
      +  
      intros lst2 Heval.
      unfold encode_asrt_expr.
      specialize (Hnrm _ Heval) as [ | (hst2 & hstmt2 & [Hheval Hhevalerr] & lst2' & Hframe2 & HQ) ];[contradiction | ].
      eexists.
      split;eauto.
      do 2 eexists. split;eauto.
      simpl_hdefs. unfold weakestpre.
      split;[cbn;auto | ].
      cbn;intros.
      sets_unfold in H. subst.
      eapply Hhnrm;eauto.
    - unfold valid_contextualreltriple, valid_contextualrelT, valid_contextualtriple.
      intros HT χ HDelta HGamma lst1 lst1' lstf hst1 hstmt1 Hframe HP.
      specialize (HT (fun hst => (evalh ρₕ hstmt1).(nrm) hst1 hst) χ).
      assert (funcspecs_sat χ (Δ ++ encode_relfuncspecs ρₕ Γ)).
      { apply funcspecs_sat_app.
        split;auto.
        apply funcspecs_equiv_relfuncspecs.
        auto. 
      }
      specialize (HT H lst1 _ _ Hframe).
      split.
      + intros.
        (* excluded middle used *)
        pose proof classic (err (evalh ρₕ hstmt1) hst1) as [ | ];[auto | ].
        assert (encode_asrt_expr ρₕ P
        (fun hst : Σₕ =>
         nrm (evalh ρₕ hstmt1) hst1 hst) lst1').
        { unfold encode_asrt_expr.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H2) as [? ?].
        contradiction.
      + intros lst2 Heval.
        (* excluded middle used *)
        pose proof classic (err (evalh ρₕ hstmt1) hst1) as [ | ];[auto | ].
        right.
        assert (encode_asrt_expr ρₕ P
        (fun hst : Σₕ =>
         nrm (evalh ρₕ hstmt1) hst1 hst) lst1').
        { unfold encode_asrt_expr, lift.
          do 2 eexists. split;eauto.
          simpl_hdefs. unfold weakestpre.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        specialize (H3 _ Heval) as (lst2' & Hframe2 & H3). 
        unfold encode_asrt_expr in H3.
        destruct H3 as [hst2 [hstmt2 [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold config_refinement;cbn.
        split.
        { intros. 
        unfold safe in H3.
        destruct H3 as [_ ?].
        sets_unfold in H3. cbn in H3.
        auto. }
        intros.
        unfold safe in H3.
        destruct H3 as [? _].
        contradiction.
  Qed. 
  
End contextual_validity_soundness.
  
End RelConcreteJoinFuncall.


