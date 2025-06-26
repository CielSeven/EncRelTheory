
From AUXLib Require Import List_lemma.
From SetsClass Require Import SetsClass.
From EncRelSeq Require Import callsem basicasrt. 
From EncRelSeq Require Export contexthoare  contexthoare_imp AbsMonadE.hoarelogic  AbsMonadE.encrel .
Require Import MonadLib.MonadLib.
Import StateRelMonadErr.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import Idents .

Import SetsNotation.
Local Open Scope sets.

(*************************************************************************************************************)
(**********************************   Encode contextual relational triples   *********************************)
(**********************************             including errors             *********************************)
(**********************************   High-level setting                     *********************************)
(**********************************          1. monade                       *********************************)
(*************************************************************************************************************)
Module RelJoinStateGlobalEnvAbsMonad.

Import practicaldeno.
Import RelHoarePracticalDenoAsbMonad.
Import ContextualJoinStateGlobalEnv.
Import EncPracticalDenoAbsMonad.
Section contextual_relationaltriples.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Context {Σₕ: Type}.

  Definition relassertion {A: Type}:= @relasrt local_cstate Σₕ (program Σₕ A).
  Record relfuncspec  : Type := mk_relfuncspec {
    rA: Type;
    rFS_With : Type;
    rFS_Pre : rFS_With -> @relassertion rA;
    rFS_Post : rFS_With -> @relassertion rA;
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
        (- hst1, hstmt -) ↪ (- hst2, hstmt2 -) /\
        exists lm2, join lm2 lmf lgst2.(gst_mem) /\
        fspec.(rFS_Post) w ((mk_lstate lst1.(lenv) lgst2.(ggenv) lm2), hst2, hstmt2).

  Definition valid_reltriple {A: Type} (χ : func -> @denosem global_cstate) :=
    fun (P : relassertion) (c : Langstmts) (Q : relassertion) =>
    forall lst1 lm1 lmf hst1 (hstmt1: program Σₕ A), join lm1 lmf lst1.(st_mem) -> P ((mk_lstate lst1.(lenv) lst1.(genv) lm1), hst1, hstmt1) ->  
            ((evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) lst1  ->  
            (hstmt1).(err) hst1) /\ 
    forall lst2, (evalnrm (fun f => (χ f).(nrm)) c) lst1 lst2 ->
    ((hstmt1).(err) hst1) \/
    exists hst2 hstmt2, 
    (- hst1, (hstmt1) -) ↪ (- hst2, (hstmt2) -) /\
    exists lm2, join lm2 lmf lst2.(st_mem) /\
    Q ((mk_lstate lst2.(lenv) lst2.(genv) lm2), hst2, hstmt2).


  Definition valid_contextualreltriple {A: Type} (Delta : funcspecs) (Gamma : relfuncspecs)  :=
    fun  (P : relassertion) (c : Langstmts) (Q : relassertion) =>
    forall χ,
    funcspecs_sat χ Delta ->  relfuncspecs_sat χ Gamma ->
    @valid_reltriple A χ P c Q.

  Lemma relfuncspecs_equivforall : forall Γ χ ,
    relfuncspecs_sat χ Γ <-> Forall (fun '(f, fspec) => forall (w : fspec.(rFS_With)) lst1 lm1 lmf hst1 hstmt,
    join lm1 lmf lst1.(st_mem) ->
    fspec.(rFS_Pre) w ((mk_lstate lst1.(lenv) lst1.(genv) lm1), hst1, hstmt) ->
    ((χ f).(err) (mk_gstate lst1.(genv) lst1.(st_mem))  -> (hstmt).(err) hst1) /\
    forall lgst2, 
      (χ f).(nrm) (mk_gstate lst1.(genv) lst1.(st_mem)) lgst2 -> ((hstmt).(err) hst1) \/
      exists hst2 hstmt2, 
      (- hst1, hstmt -) ↪ (- hst2, hstmt2 -) /\
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
    mk_funcspec ((rfspec.(rA) -> Σₕ -> Prop) * rfspec.(rFS_With)) 
                (fun '(X, w) => encode_asrt (rfspec.(rFS_Pre) w) X) 
                (fun '(X, w) => encode_asrt (rfspec.(rFS_Post) w) X). 

  Fixpoint encode_relfuncspecs (Gamma : relfuncspecs)  : funcspecs :=
    match Gamma with 
    | nil => nil 
    | (fid, rfspec) :: Gamma' =>  (fid, encode_relfuncspec rfspec) :: (encode_relfuncspecs Gamma')
    end.

  Definition valid_contextualrelT {A: Type} (Delta : funcspecs) (Gamma : relfuncspecs) 
    (P: @relasrt local_cstate Σₕ (program Σₕ A)) (cₗ: Langstmts) (Q : @relasrt local_cstate Σₕ (program Σₕ A)) := 
      forall X, valid_contextualtriple (Delta ++ (encode_relfuncspecs Gamma))
                        (encode_asrt P X)
                        cₗ 
                        (encode_asrt Q X).


End encode_contextual_triples.

Notation " '(|' Γ '|)'  " := (encode_relfuncspecs Γ)  (at level 20, no associativity). 

(*************************************************************************************************************)
(*******************************     soundness proof for valid_contextualrelT    *****************************)
(*************************************************************************************************************)
Require Import Coq.Logic.Classical_Prop.

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
        destruct fspec as [A rfwith RP RQ].
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
            unfold safe.
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
          unfold sem_eval.
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
          unfold safe.
          split;auto.
      + apply funcspecs_equivforall.
        apply IHΓ.
        apply relfuncspecs_equivforall;auto.
  Qed.

  Theorem validity_lemma {A: Type}: forall (Δ : funcspecs) (Γ : relfuncspecs) (P: @relasrt local_cstate Σₕ (program Σₕ A)) (cₗ: Langstmts) 
    (Q : @relasrt local_cstate Σₕ (program Σₕ A)),
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
      specialize (HT (fun r hst => (hstmt1).(nrm) hst1 r  hst) χ).
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
        pose proof classic ((hstmt1).(err) hst1) as [ | ];[auto | ].
        assert (encode_asrt P (fun (r : A) (hst : Σₕ) => hstmt1.(nrm) hst1 r hst)
        {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
        { unfold encode_asrt.
          do 2 eexists. split;eauto.
          unfold safe.
          split;auto. 
        }
        specialize (HT H2) as [? ?].
        contradiction.
      + intros lst2 Heval.
        (* excluded middle used *)
        pose proof classic ((hstmt1).(err) hst1) as [ | ];[auto | ].
        right.
        assert (encode_asrt P (fun (r : A) (hst : Σₕ) => hstmt1.(nrm) hst1 r hst)
        {| lenv := lenv lst1; genv := genv lst1; st_mem := lm1 |}).
        { unfold encode_asrt, lift.
          do 2 eexists. split;eauto.
          unfold safe.
          split;auto. 
        }
        specialize (HT H1) as [? ?].
        specialize (H3 _ Heval) as (lm2 & Hframe2 & H3). 
        unfold encode_asrt in H3.
        destruct H3 as [hst2 [hstmt2 [? ?]]];subst.
        do 2 eexists.
        split;eauto.
        unfold sem_eval;cbn.
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

Notation " Δ ⩅ Γ '⊢ₑ' '⟨' P '⟩' c '⟨' Q '⟩'" := (valid_contextualrelT Δ Γ P c Q) (at level 71, no associativity).

End RelJoinStateGlobalEnvAbsMonad.

Module RelJoinStateGlobalEnvAbsMonadRules.
Import practicaldeno.
Import RelHoarePracticalDenoAsbMonad.
Import ContextualJoinStateGlobalEnv.
Import EncPracticalDenoAbsMonad.
Import RelJoinStateGlobalEnvAbsMonad.
(**********************************************************************************)
(*    encode asrt rules                                                           *)
(**********************************************************************************)
Section  RAssertion.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  
  Context {Σₕ A: Type}.

  Definition relexpr {A: Type} : Type := local_cstate * Σₕ * (program Σₕ A).
  Definition rjoin {A: Type} : (@relexpr A) -> (@relexpr A) -> (relexpr) -> Prop :=
    fun '(σₗ1, σₕ1, cₕ1) '(σₗ2, σₕ2, cₕ2) '(σₗ3, σₕ3, cₕ3) =>
        join σₗ1.(st_mem) σₗ2.(st_mem) σₗ3.(st_mem) /\ 
        σₗ1.(lenv) = σₗ2.(lenv) /\ σₗ2.(lenv) = σₗ3.(lenv) /\
        σₗ1.(genv) = σₗ2.(genv) /\ σₗ2.(genv) = σₗ3.(genv) /\ 
        σₕ1 = σₕ2 /\ σₕ2 = σₕ3 /\ 
        cₕ1 = cₕ2 /\ cₕ2 = cₕ3.

  Definition ris_unit {A: Type}: (@relexpr A) -> Prop := fun '(σₗ1, σₕ1, cₕ1) => is_unit σₗ1.(st_mem).


  #[export] Instance reljoinm {A: Type}: @JoinM (@relexpr A) := {
    join := rjoin;
    is_unit := ris_unit;
  }. 

  Definition Alst (P : local_cstate -> Prop ): @relasrt local_cstate Σₕ (program Σₕ A):= fun '(σₗ, σₕ, cₕ) => P σₗ .

  Definition Ahst (P : Σₕ -> Prop ): @relasrt local_cstate Σₕ (program Σₕ A):= fun '(σₗ, σₕ, cₕ) =>  P σₕ /\ is_unit σₗ.(st_mem).

  Definition Aspec (cₕ : program Σₕ A) : @relasrt local_cstate Σₕ (program Σₕ A):= fun '(σₗ, σₕ, c) =>  c = cₕ /\ is_unit σₗ.(st_mem).
End RAssertion.

Notation " ⌊ P ⌋ " := (Alst P) (at level 22, no associativity).
Notation " ⌈ P ⌉ " := (Ahst P) (at level 22, no associativity).
Local Open Scope asrt_scope. 

Section  EncodeRules.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context {lmaxioms: @JoinMAxioms memory memm}.
  Context {Σₕ A: Type}.

Lemma encode_derives: forall X (P: @relasrt local_cstate Σₕ (program Σₕ A)) (P' : @relasrt local_cstate Σₕ (program Σₕ A)),
P |-- P' -> [|P|](X) |-- [|P'|](X).
Proof.
  intros.
  unfold derivable1, encode_asrt.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H0.
  do 2 eexists.
  split;eauto. 
Qed.


Lemma encode_alst_andp: forall X (P: @asrt local_cstate) (P' : @asrt Σₕ) (s: program Σₕ A),
 [|Aspec s ** Alst P ** Ahst P'|](X) --||--  !! (safeExec P' s X) && P. (*// safeexec *)
Proof.
  intros.
  intros σₗ;split.
  { unfold derivable1, sepcon, andp, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, safeExec, safe.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  simpl in *. 
  destruct x as ((? & ?) & ?). destruct x0 as ((? & ?) & ?).
  destruct x1 as ((? & ?) & ?). destruct x2 as ((? & ?) & ?).
  simpl in *.
  my_destruct local_cstate Σₕ (program Σₕ A) H0.
  my_destruct local_cstate Σₕ (program Σₕ A) H2.
  subst.
  destruct_st σₗ. destruct_st l. destruct_st l0. destruct_st l1. destruct_st l2.
  cbn in *. subst. 
  destruct H3. destruct H4. subst.
  apply join_comm in H2.
  apply unit_spec in H2;auto.
  apply unit_spec in H0;auto.
  subst.
  split;auto.
  eexists;
  split;eauto. }

  unfold derivable1, sepcon, coq_prop, encode_asrt, andp, Alst, Ahst, Aspec, safeExec, safe.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  do 2 eexists.
  split;eauto.
  destruct_st σₗ.
  pose proof unit_join m as [m0 [? ?]].
  exists ({| lenv := l; genv := g; st_mem := m |}, σₕ, s).
  exists ({| lenv := l; genv := g; st_mem := m0 |}, σₕ, s).
  cbn.
  splits;auto.
  exists ({| lenv := l; genv := g; st_mem := m0 |}, σₕ, s), ({| lenv := l; genv := g; st_mem := m |}, σₕ, s).
  cbn.
  splits;auto.
  apply join_comm;auto.
Qed.

Lemma encode_andp_split : forall X (x y: @relasrt local_cstate Σₕ (program Σₕ A)), [| x && y |](X) |-- [| x |](X) && [| y |](X).
Proof.
  intros.
  unfold derivable1, encode_asrt, andp.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  split.
  all :do 2 eexists;
      split;eauto. 
Qed.

Lemma encode_andp_merge : forall X (x y: @relasrt local_cstate Σₕ (program Σₕ A)), [| x |](X) && [| y |](X) |-- [| x && y |](X).
Proof.
  intros. 
  unfold derivable1, encode_asrt, andp.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  do 2 eexists;
      split;eauto. 
Abort.
(* ATTENTION : THE REVERSE IS WRONG *)


Lemma encode_exp_intro : forall {A: Type} X (P : A ->   @relasrt local_cstate Σₕ (program Σₕ A)), EX v, [|P v|](X) |-- [|EX v, (P v)|](X) .
Proof.
  intros.
  unfold derivable1, encode_asrt, exp.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  do 2 eexists.
  split;eauto.
Qed.

Lemma encode_expunit_equiv : forall X (P :  @relasrt local_cstate Σₕ (program Σₕ A)), EX (v : unit), [|P|](X) --||-- [|P|](X) .
Proof.
  intros;split;intros.
  - my_destruct local_cstate Σₕ (program Σₕ A) H.
    auto.
  - 
  unfold derivable1, encode_asrt, exp, exp in *.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  do 3 eexists.
  split;eauto.
Qed.


Lemma encode_exp_equiv : forall {A: Type} X (P : A ->  @relasrt local_cstate Σₕ (program Σₕ A)), EX v, [|P v|](X) --||-- [|EX v, (P v)|](X) .
Proof.
  intros;split;intros.
  - apply encode_exp_intro.
    auto.
  - 
  unfold derivable1, encode_asrt, exp, exp in *.
  my_destruct local_cstate Σₕ (program Σₕ A) H.
  do 3 eexists.
  split;eauto.
Qed.

Lemma encode_prop_andp : forall (B: Prop) X (P:  @relasrt local_cstate Σₕ (program Σₕ A)), [| !! B && P |](X) --||--  !! B && [| P |](X).
Proof.
  intros.
  unfold logic_equiv, encode_asrt, andp, andp, coq_prop, coq_prop.
  split;intros.
  - my_destruct local_cstate Σₕ (program Σₕ A) H.
    split;auto.
    do 2 eexists.
    split;eauto.
  - my_destruct local_cstate Σₕ (program Σₕ A) H.
    do 2 eexists.
    split;eauto.
Qed.

(**********************************************************************************)
(*    relation asrt rules                                                         *)
(**********************************************************************************)
Lemma derives_imply_lderi : forall (P P' : @relasrt local_cstate Σₕ (program Σₕ A)) ,
 P |-- P' ->
 (forall X,  [| P |] (X)  |-- [| P' |] (X) ).
Proof.
  unfold derivable1, encode_asrt.
  intros.
  my_destruct local_cstate Σₕ (program Σₕ A) H0.
  do 2 eexists;split;eauto. 
Qed.


Lemma lderi_imply_derives : forall P (P': @asrt local_cstate),
 P |-- P' ->
 @Alst lgst Σₕ  A P  |-- Alst P' .
Proof.
  unfold derivable1,  Alst.
  intros.
  destruct st as ((? & ?) & ?).
  auto.
Qed.

Lemma hderi_imply_derives : forall P P',
 P |-- P' ->
 @Ahst lgst Σₕ  A P  |-- Ahst P' .
Proof.
  unfold derivable1,  Ahst.
  intros. destruct st as ((? & ?) & ?). destruct H0. split; auto.
Qed.


End  EncodeRules.

(**********************************************************************************)
(*    hoare rules                                                                 *)
(**********************************************************************************)
Section  HoareRules.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context {lmaxioms: @JoinMAxioms memory memm}.

  Context {Σₕ A: Type}.


Lemma rh_hoare_conseq : forall Δ Γ c (P P' Q Q': @relasrt local_cstate Σₕ (program Σₕ A)),
  P |-- P' ->
  Q' |--  Q ->
  Δ ⩅ Γ ⊢ₑ ⟨ P' ⟩ c ⟨ Q' ⟩ ->
  Δ ⩅ Γ ⊢ₑ ⟨ P ⟩ c ⟨ Q ⟩.
Proof.
  unfold valid_contextualrelT; simpl. intros * HP' HQ' HT.
  intros.
  specialize (HT X).
  eapply hoare_conseq;[ | | exact HT].
  eapply encode_derives;eauto.
  eapply encode_derives;eauto.
Qed.
(**********************************************************************************)
(*    trans reltriple into hoare triple                                           *)
(**********************************************************************************)
Lemma  reltriple_triple_equiv : forall Δ Γ (P: @asrt local_cstate) Ps (s: program Σₕ A) c Q Ps' s',
  Δ ⩅ Γ ⊢ₑ ⟨ Aspec s ** Alst P ** Ahst Ps ⟩ c ⟨ Aspec s' **  Alst Q ** Ahst Ps' ⟩ <->
  (forall X, 
   Δ ++ (|Γ|) ⊢ {{!! safeExec Ps s X && P}} c {{!! safeExec Ps' s' X && Q}}).
Proof.
  intros;split.
  - intros.
  specialize (H X).
  eapply hoare_conseq;eauto.
  eapply (logic_equiv_derivable1_2 (encode_alst_andp X P Ps s)).
  apply (logic_equiv_derivable1_1 (encode_alst_andp X Q Ps' s')).
  - unfold valid_contextualrelT; intros.
    specialize (H X).
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_1 (encode_alst_andp X P Ps s)).
    apply (logic_equiv_derivable1_2 (encode_alst_andp X Q Ps' s')).
Qed.

Lemma  reltriple_triple_equiv1 : forall  Δ Γ (P: @asrt local_cstate) Ps (s: program Σₕ A) c Q,
  Δ ⩅ Γ ⊢ₑ ⟨ Aspec s **  Alst P ** Ahst Ps ⟩ c ⟨ Q ⟩ <->
  (forall X,  
    Δ ++ (|Γ|)  ⊢ {{!! safeExec Ps s X && P}} c {{[|Q|](X)}}).
Proof.
  intros;split.
  - intros.
  specialize (H X).
  eapply hoare_conseq;eauto.
  apply (logic_equiv_derivable1_2 (encode_alst_andp X P Ps s)).
  cbv. auto.
  - unfold valid_contextualrelT; intros.
    specialize (H X).
    eapply hoare_conseq;eauto.
    apply (logic_equiv_derivable1_1 (encode_alst_andp X P Ps s)).
    cbv. auto.
Qed.

End HoareRules.

Section  composition_rules.

Import MonadNotation.
  Local Open Scope monad.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context {lmaxioms: @JoinMAxioms memory memm}.

  Context {Σₕ A: Type}.
  Definition link {Σₗ Σₕ: Type} (P: @binasrt Σₗ Σₕ) (P': @asrt Σₕ) : @asrt Σₗ:=
    fun σₗ =>  exists σₕ, P (σₗ, σₕ) /\  P' σₕ.
(*************************************************************************************)
(*    vertical composition rule                                                      *)
(*                                                                                   *)
(*  ⟨ P * cₕ ⟩  c  ⟨ Q * skip ⟩                        { Pₕ } cₕ { Qₕ }                 *)
(* ________________________________________________________________________________  *)
(* {λ σₗ. ∃ σₕ. P(σₗ, σₕ) /\ Pₕ' (σₕ) } c {λ σₗ. ∃ σₕ. Q(σₗ, σₕ) /\ Qₕ (σₕ) }              *)
(*************************************************************************************)
Lemma rh_hoare_vc :forall Δ Γ c (sₕ : program Σₕ A) P Q Pₕ Qₕ,
Δ ⩅ Γ ⊢ₑ ⟨ lift P sₕ ⟩ c ⟨ EX r : A, lift Q (return r) ⟩ ->
Hoare Pₕ sₕ Qₕ ->
Δ ++ (|Γ|)  ⊢ {{link P Pₕ}} c {{EX r, link (Q) (Qₕ r)}}.
Proof.
  unfold valid_reltriple; intros * HRT HHT.
  unfold valid_triple in HHT.
  unfold valid_triple.
  intros χ Hcallees lst1 * Hjoin HP.
  destruct HP as [σₕ [? HPH]].
  destruct HHT as [HHnrm HHerr].
  specialize (HHerr _ HPH).
  (*将high level 终止状态指定为满足条件的初始状态经过从cₕ能到达的集合*)
  specialize (HRT  (fun r (x: Σₕ) => (sₕ.(nrm)) σₕ r x) _ Hcallees lst1 _ _ Hjoin).
  assert (([|lift P sₕ|](fun (r : A) (x : Σₕ) => sₕ.(nrm) σₕ r x))
  {| lenv := lenv lst1; genv := genv lst1; st_mem := m1 |}).
  { unfold encode_asrt, lift.
    exists σₕ, sₕ.
    split;auto.
    unfold safe.
    split;auto.  }
  specialize (HRT H0) as [HRerr HRT].
  clear H0.
  split;auto.
  intros * Hceval.
  specialize (HRT _ Hceval) as  [? [Hjoin2 HRQ]].
  unfold encode_asrt, lift, exp in *.
  destruct HRQ as [σₕ' [cₕ' [? [? [? ?]]]]]. subst cₕ'.
  unfold safe, ret in H0. cbn in H0.
  destruct H0.
  specialize (H2 x0 σₕ' (ltac:(simpl;auto))).
  specialize (HHnrm x0 _ σₕ' HPH H2) as HHQ.
  eexists;split;eauto.
  exists x0.
  unfold link.
  eexists.
  eauto.
Qed.


Lemma rh_hoare_vc_safeexec {U V: Type}:forall Δ c (sₕ :  U -> program Σₕ A) P Ps Q Qs B1 B2 Pₕ Qₕ u,
  (Hoare (Pₕ) (sₕ u) (Qₕ)) ->
  (forall X,  Δ ⊢ {{EX (u: U), !! safeExec (Ps u) (sₕ u) X && !! (B1 u) && (P u)}} c 
      {{EX (r: A) (v: V), !! safeExec (Qs v r) (return r) X && !! (B2 v r) && (Q v r) }}) ->
  (Δ  ⊢ {{ !! (exists s, Ps u s /\ Pₕ s) && !! (B1 u) && (P u) }} c 
        {{EX r v, !! (exists s, Qs v r s /\ Qₕ r s) && !! (B2 v r) && (Q v r) }}).
Proof.
  unfold valid_triple; intros * HHT HRT.
  intros χ Hcallees lst1 * Hjoin HP.
  destruct HP as [[[σₕ [? HPH]] HBH] HP].
  destruct HHT as [HHnrm HHerr].
  specialize (HHerr _ HPH).
  (* specialize (HHT σₕ HPH) as HHnrm. *)
  (*将high level 终止状态指定为满足条件的初始状态经过从cₕ能到达的集合*)
  specialize (HRT  (fun r (x: Σₕ) =>  (sₕ u).(nrm) σₕ r x) _ Hcallees lst1 _ _ Hjoin).
  assert ((EX u0 : U, !! safeExec (Ps u0) (sₕ u0) (fun (r : A) (x : Σₕ) => (sₕ u).(nrm) σₕ r x) && !! B1 u0 && P u0)
  {| lenv := lenv lst1; genv := genv lst1; st_mem := m1 |}).
  { exists u.
    unfold andp, coq_prop in *. 
    splits;try tauto.
    unfold safeExec.
    exists σₕ.
    split;try tauto.
    unfold safe.
    split;auto. }
  specialize (HRT H0) as [HRerr HRT].
  clear H0.
  split;auto.
  intros * Hceval.
  specialize (HRT _ Hceval) as  [? [Hjoin2 HRQ]].
  destruct HRQ as [r [v HRQ]].
  unfold andp, coq_prop in HRQ. simpl in HRQ.
  destruct HRQ as [[? ?] ?].
  destruct H0 as [σₕ' [? ?]].
  unfold safe, ret in H3. cbn in H3.
  destruct H3 as [_ H3].
  specialize (H3 r σₕ' (ltac:(unfold_monad;auto))).
  specialize (HHnrm r _ σₕ' HPH H3) as HHQ.
  eexists;split;eauto.
  exists r, v.
  unfold link, andp, coq_prop.
  simpl.
  splits;auto.
  eexists.
  eauto.
Qed.
End composition_rules.
End RelJoinStateGlobalEnvAbsMonadRules.







