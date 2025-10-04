From AUXLib Require Import List_lemma.
From SetsClass Require Import SetsClass.
From EncRelSeq Require Import callsem basicasrt.
From EncRelSeq Require Export contexthoare.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import Idents.
From FP Require Import SetsFixedpoints.

Import SetsNotation.
Local Open Scope sets.

(*************************************************************************************************************)
(**********************************           Contextual Tiples              *********************************)
(**********************************   Setting:                               *********************************)
(**********************************         1.memory join                    *********************************)
(**********************************           env  nojoin: l g               *********************************)
(**********************************           valid triple has memory frame  *********************************)
(**********************************         2.Σ': genv mem                   *********************************)
(**********************************           χ: func -> deno Σ'             *********************************)
(*************************************************************************************************************)


Class  calllang_envstate {Σ Σ': Type} := {
  Langstmts: Type;
  evalnrm: (func -> Σ' -> Σ' -> Prop) -> (Langstmts) -> Σ -> Σ -> Prop;
  evalerr: (func -> Σ' -> Σ' -> Prop) -> (func -> Σ' -> Prop) -> (Langstmts) -> Σ -> Prop;
}.

Record lstate {l g m : Type} : Type := mk_lstate{
  lenv : l;
  genv : g;
  st_mem: m;
}.

Arguments mk_lstate {l} {g} {m}.

Record gstate {g m : Type} : Type := mk_gstate{
  ggenv : g;
  gst_mem: m;
}.

Arguments mk_gstate {g} {m}.


Class lgstate := {
  local_env: Type;
  global_env : Type;
  memory: Type;
  memm :: @JoinM memory 
}.

Definition local_cstate `{st: lgstate} := @lstate local_env global_env memory.
Definition global_cstate `{st: lgstate} := @gstate global_env memory. 

Ltac destruct_st σ :=
  let l := fresh "l" in let g := fresh "g" in let m := fresh "m" in destruct σ as [l g m].

Definition assertion `{lgst : lgstate}:= @asrt local_cstate.

(*************************************************************************************************************)
(**********************************             program semantics            *********************************)
(**********************************   Setting                                *********************************)
(**********************************          1. mem joi                      *********************************)
(**********************************          2. χ: func -> deno global_state *********************************)
(*************************************************************************************************************)
Module EnvProgramSem.

Import practicaldeno.


Section procedurecall_sem.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.
  Context (χnrm : func -> global_cstate  -> global_cstate -> Prop).
  Context (χerr : func -> global_cstate  -> Prop).

  Definition call_nrm f: local_cstate -> local_cstate -> Prop :=
    fun st1 st2 => (χnrm f) (mk_gstate st1.(genv) st1.(st_mem)) (mk_gstate st2.(genv) st2.(st_mem)) /\ 
                   st1.(lenv) = st2.(lenv).
  
  Definition call_err f: local_cstate -> Prop :=
    fun st1 => (χerr f) (mk_gstate st1.(genv) st1.(st_mem)). 

  Definition call_denote f  : @denosem local_cstate :=
  {|
    nrm := call_nrm f;
    err := call_err f;
  |}.

End procedurecall_sem.

Section  program_sem.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Variable default: local_env.

  Definition program : Type := list (func * Langstmts).

  Definition prosem_nrm (p : program) : func -> global_cstate  -> global_cstate -> Prop :=
  Lfix (fun X f st1 st2 =>
    exists c, In (f, c) p /\
    (evalnrm X c) (mk_lstate default st1.(ggenv) st1.(gst_mem)) 
                  (mk_lstate default st2.(ggenv) st2.(gst_mem))).

  Definition prosem_err (p : program) : func -> global_cstate  -> Prop :=
  Lfix (fun X f st1 =>
    exists c, In (f, c) p /\
    (evalerr (prosem_nrm p) X c) (mk_lstate default st1.(ggenv) st1.(gst_mem)) ).

  Definition prosem (p : program) (f: func) : @denosem global_cstate := {|
    nrm := prosem_nrm p f;
    err := prosem_err p f;
  |}.

  Definition eval (p : program) (stmt: Langstmts): @denosem local_cstate := {|
    nrm := evalnrm (prosem_nrm p) stmt;
    err := evalerr (prosem_nrm p) (prosem_err p) stmt
  |}.

End program_sem.
End EnvProgramSem.


Module NormalContextualImp.

Import practicaldeno.
Import EnvProgramSem.
Section contextual_hoaretriples.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Variable default: local_env.
  Record funcspec : Type := mk_funcspec {
    FS_With : Type;
    FS_Pre : FS_With -> assertion;
    FS_Post : FS_With -> assertion;
  }.


  Definition funcspecs : Type := list (func * funcspec).

  
  Definition valid_triple_nrm  (χnrm : func -> global_cstate -> global_cstate -> Prop): @HT_validity local_cstate (Langstmts) :=
    fun P c Q =>
    forall st1 m1 mf, join m1 mf st1.(st_mem)  -> 
      P (mk_lstate st1.(lenv) st1.(genv) m1) -> 
    forall st2, (evalnrm χnrm c) st1 st2 -> 
      exists m2, join m2 mf st2.(st_mem) /\ Q (mk_lstate st2.(lenv) st2.(genv) m2).

  Definition funcspecs_sat_nrm (χnrm : func -> global_cstate -> global_cstate  -> Prop)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 m1 mf (w : fspec.(FS_With)),
      join m1 mf st1.(st_mem) ->
      fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
      forall gst2, 
        (χnrm f) (mk_gstate st1.(genv) st1.(st_mem)) 
                    gst2 ->
        exists m2, 
          join m2 mf gst2.(gst_mem)  /\
          fspec.(FS_Post) w (mk_lstate st1.(lenv) gst2.(ggenv) m2).

  Definition valid_contextualtriple_nrm (Delta : funcspecs) : @HT_validity local_cstate (Langstmts) :=
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

  
  Lemma funcspecs_nrm_equivforall : forall Δ  χnrm ,
  funcspecs_sat_nrm χnrm Δ <-> Forall (fun '(f, fspec) => (forall st1 m1 mf (w : fspec.(FS_With)),
  join m1 mf st1.(st_mem) ->
  fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
  forall gst2, 
    (χnrm f) (mk_gstate st1.(genv) st1.(st_mem))  gst2 ->
    exists m2, 
      join m2 mf gst2.(gst_mem)  /\
      fspec.(FS_Post) w (mk_lstate st1.(lenv) gst2.(ggenv) m2))) Δ.
  Proof.
    intros.
    split;intros.
    - apply Forall_forall. 
      intros [f fspec].
      apply H.
    - unfold funcspecs_sat_nrm. intros.
      eapply Forall_forall in H;eauto.
      eapply H;eauto.
  Qed. 
  
  Lemma funcspecs_sat_nrm_app : forall Δ1 Δ2 χ ,
    funcspecs_sat_nrm χ (Δ1 ++ Δ2) <->  (funcspecs_sat_nrm χ Δ1 /\  funcspecs_sat_nrm χ Δ2).
  Proof.
    intros.
    split;intros.
    - apply funcspecs_nrm_equivforall in H.
      apply Forall_app in H as [? ?].
      apply funcspecs_nrm_equivforall in H.
      apply funcspecs_nrm_equivforall in H0.
      split;auto.
    - apply funcspecs_nrm_equivforall.
      apply Forall_app.
      split.
      apply funcspecs_nrm_equivforall. tauto.
      apply funcspecs_nrm_equivforall. tauto.
  Qed.

End contextual_hoaretriples.

Notation " Δ '⊢' '{{' P '}}' c '{{' Q '}}'" := (valid_contextualtriple_nrm Δ  P c Q) (at level 72, no associativity).
Local Open Scope asrt_scope. 
Lemma hoare_conseq {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P P' Q Q',
  P |-- P' ->
  Q' |-- Q ->
  Δ ⊢ {{P'}} c {{Q'}} -> 
  Δ ⊢ {{P}} c {{Q}}.
  Proof.
    unfold valid_contextualtriple_nrm. simpl. intros * HP' HQ' HT.
    intros * HDelta lst1 * Hjoin HP.
    specialize (HT  _ HDelta _ _ _ Hjoin  (HP' _ HP)) as HT.
    intros * Heval.
    specialize (HT _ Heval) as [? [? ?]].
    eexists.
    split;eauto.
  Qed.

(* rule Conseq-Pre *)
Lemma hoare_conseq_pre {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall Δ c P P' Q,
  P |-- P' ->
  Δ ⊢ {{P'}} c {{Q}} -> 
  Δ ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P' Q Q); auto.
  reflexivity.
Qed.

Lemma hoare_conseq_post {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall Δ c P Q Q',
  Q' |-- Q ->
  Δ ⊢ {{P}} c {{Q'}} -> 
  Δ ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P Q Q'); auto.
  reflexivity.
Qed.
(* rule ExIntro *)
Lemma hoare_exists_intro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall  Δ  c (A : Type) P Q,
  (forall (v: A), Δ ⊢ {{P v}} c {{Q}}) ->
   Δ ⊢ {{EX v, P v}} c {{Q}}.
Proof.
  unfold valid_contextualtriple_nrm. simpl. intros * HT * Hcallees.
  unfold valid_triple_nrm.
  intros * Hmem HP.
  destruct HP.
  specialize (HT x _ Hcallees _ _ _ Hmem H).
  auto.
Qed.

Lemma hoare_exists_r {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall  Δ  c (A : Type) P Q (v: A),
  Δ ⊢ {{P}} c {{Q v}} ->
  Δ ⊢ {{P}} c {{EX v, Q v}}.
Proof.
  unfold valid_contextualtriple_nrm. simpl. intros * HT * Hcallees.
  unfold valid_triple_nrm.
  intros * Hmem HP.
  specialize (HT _ Hcallees _ _ _ Hmem HP) as HT.
  intros.
  specialize (HT _ H) as [? [? ?]].
  eexists. split;eauto.
  exists v. auto.
Qed.

Lemma hoare_coqprop_preintro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P Q (P': Prop),
  (P' -> Δ ⊢ {{P}} c {{Q}})->
  Δ ⊢ {{!! P' && P}} c {{Q}}.
Proof.
  unfold valid_contextualtriple_nrm. simpl. intros * HT * Hcallees.
  unfold valid_triple_nrm.
  intros * Hmem HP.
  destruct HP. unfold coq_prop in H.
  specialize (HT H _ Hcallees _ _ _ Hmem H0) as HT.
  auto.
Qed.

Lemma hoare_coqprop_postintro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P Q (P': Prop),
  P' -> Δ ⊢ {{P}} c {{Q}}->
  Δ ⊢ {{P}} c {{!! P' &&  Q}}.
Proof.
  intros.
  eapply hoare_conseq_post;eauto.
  pose proof (prop_add_left Q P').
  apply logic_equiv_derivable1 in H1 as [? ?]; eauto.
  apply coq_prop_right;auto.
Qed.

Section contextual_soundness.

  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Variable default: local_env.
  
  Definition func_closed_wrt_lvars (P : assertion) : Prop :=
  forall l1 l2 g m,
  P (mk_lstate l1 g m) = P (mk_lstate l2 g m).

  Definition fspec_closed_wrt_lvars (fspec : funcspec) : Prop :=
    (forall w, func_closed_wrt_lvars (fspec.(FS_Pre) w)) /\
    (forall w, func_closed_wrt_lvars (fspec.(FS_Post) w)).


  Lemma funcspecs_sat_triple_body_nrm : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body_nrm p Delta f fspec) Delta) ->
    funcspecs_sat_nrm (prosem_nrm default p) Delta.
  Proof.
    unfold triple_body_nrm, funcspecs_sat_nrm, valid_triple_nrm, prosem_nrm, Lfix.
    intros * HNoDup HCP HT * HDelta * Hm1 HP * Hev.
    rewrite Forall_forall in HT.
    rewrite Forall_forall in HCP.
    destruct Hev as [n Hev].
    revert HDelta Hm1 HP Hev. revert st1 m1 mf w gst2. revert f fspec.
    induction n; simpl in *; [contradiction | ].
    remember (Nat.iter n
    (fun (X : func -> global_cstate -> global_cstate -> Prop) (f0 : func) (st2 st3 : gstate) =>
     exists c : Langstmts,
       In (f0, c) p /\
       evalnrm X c {| lenv := default; genv := ggenv st2; st_mem := gst_mem st2 |}
         {| lenv := default; genv := ggenv st3; st_mem := gst_mem st3 |}) ∅)
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
    specialize (HCP _ HDelta).
    destruct HCP as [HCP HCP'].
    erewrite <- (HCP _ default) in HP. 
    specialize (HT w callees IHsat (mk_lstate default st1.(genv) st1.(st_mem)) m1 mf Hm1 HP _ Hev) as [m2 [Hm2 HQ] ].
    exists m2. split; auto.
    cbn in HQ.
    erewrite <- (HCP' _  st1.(lenv)) in HQ.
    auto.
  Qed.

  
  Lemma contexthoare_imply_prosemhoare : forall (ρ: program) Delta P c Q,
    NoDup (map fst ρ) ->
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body_nrm ρ Delta f fspec) Delta) ->
    valid_contextualtriple_nrm Delta P c Q ->
    valid_triple_nrm (prosem_nrm default ρ) P c Q.
  Proof.
    intros.
    pose proof funcspecs_sat_triple_body_nrm _ _ H H0 H1.
    unfold valid_contextualtriple_nrm in H1.
    specialize (H2 _  H3).
    auto.
  Qed. 

End contextual_soundness.


End NormalContextualImp.





Module ContextualJoinStateGlobalEnv.

Import practicaldeno.
Import EnvProgramSem.
Section contextual_hoaretriples.
  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Variable default: local_env.

  Record funcspec : Type := mk_funcspec {
    FS_With : Type;
    FS_Pre : FS_With -> assertion;
    FS_Post : FS_With -> assertion;
  }.


  Definition funcspecs : Type := list (func * funcspec).


  Definition funcspecs_sat (χ : func -> @denosem global_cstate)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 m1 mf (w : fspec.(FS_With)),
      join m1 mf st1.(st_mem) ->
      fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
      ~ (χ f).(err) (mk_gstate st1.(genv) st1.(st_mem)) /\
      forall gst2, 
        (χ f).(nrm) (mk_gstate st1.(genv) st1.(st_mem)) 
                    gst2 ->
        exists m2, 
          join m2 mf gst2.(gst_mem)  /\
          fspec.(FS_Post) w (mk_lstate st1.(lenv) gst2.(ggenv) m2).

  Definition valid_triple (χ : func -> @denosem global_cstate): @HT_validity local_cstate (Langstmts) :=
    fun P c Q =>
    forall st1 m1 mf, join m1 mf st1.(st_mem)  -> 
      P (mk_lstate st1.(lenv) st1.(genv) m1) -> 
      ~ (evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c) st1 /\ 
    forall st2, (evalnrm (fun f => (χ f).(nrm)) c) st1 st2 -> 
      exists m2, join m2 mf st2.(st_mem) /\ Q (mk_lstate st2.(lenv) st2.(genv) m2).


  Definition valid_contextualtriple (Delta : funcspecs) : @HT_validity local_cstate (Langstmts) :=
    fun  (P : assertion) (c : (Langstmts)) (Q : assertion) =>
    forall χ,
    funcspecs_sat χ Delta ->
    valid_triple χ P c Q.

  Lemma funcspecs_equivforall : forall Δ χ ,
    funcspecs_sat χ Δ <-> Forall (fun '(f, fspec) => (forall st1 m1 mf (w : fspec.(FS_With)),
    join m1 mf st1.(st_mem) ->
    fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
    ~ (χ f).(err) (mk_gstate st1.(genv) st1.(st_mem)) /\
    forall gst2, 
      (χ f).(nrm) (mk_gstate st1.(genv) st1.(st_mem)) 
                  gst2 ->
      exists m2, 
        join m2 mf gst2.(gst_mem)  /\
        fspec.(FS_Post) w (mk_lstate st1.(lenv) gst2.(ggenv) m2))) Δ.
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

Notation " Δ '⊢' '{{' P '}}' c '{{' Q '}}'" := (valid_contextualtriple Δ  P c Q) (at level 72, no associativity).
Local Open Scope asrt_scope. 
Lemma hoare_conseq {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P P' Q Q',
  P |-- P' ->
  Q' |-- Q ->
  Δ ⊢ {{P'}} c {{Q'}} -> 
  Δ ⊢ {{P}} c {{Q}}.
  Proof.
    unfold valid_contextualtriple. simpl. intros * HP' HQ' HT.
    intros * HDelta lst1 * Hjoin HP.
    specialize (HT  _ HDelta _ _ _ Hjoin  (HP' _ HP)) as [HTerr HT].
    split;[auto | intros * Heval].
    specialize (HT _ Heval) as [? [? ?]].
    eexists.
    split;eauto.
  Qed.

(* rule Conseq-Pre *)
Lemma hoare_conseq_pre {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall Δ c P P' Q,
  P |-- P' ->
  Δ ⊢ {{P'}} c {{Q}} -> 
  Δ ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P' Q Q); auto.
  reflexivity.
Qed.

Lemma hoare_conseq_post {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall Δ c P Q Q',
  Q' |-- Q ->
  Δ ⊢ {{P}} c {{Q'}} -> 
  Δ ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P Q Q'); auto.
  reflexivity.
Qed.
(* rule ExIntro *)
Lemma hoare_exists_intro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall  Δ  c (A : Type) P Q,
  (forall (v: A), Δ ⊢ {{P v}} c {{Q}}) ->
   Δ ⊢ {{EX v, P v}} c {{Q}}.
Proof.
  unfold valid_contextualtriple. simpl. intros * HT * Hcallees.
  unfold valid_triple.
  intros * Hmem HP.
  destruct HP.
  specialize (HT x _ Hcallees _ _ _ Hmem H) as [HTerr HT].
  split;auto.
Qed.

Lemma hoare_exists_r {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate}: forall  Δ  c (A : Type) P Q (v: A),
  Δ ⊢ {{P}} c {{Q v}} ->
  Δ ⊢ {{P}} c {{EX v, Q v}}.
Proof.
  unfold valid_contextualtriple. simpl. intros * HT * Hcallees.
  unfold valid_triple.
  intros * Hmem HP.
  specialize (HT _ Hcallees _ _ _ Hmem HP) as [HTerr HT].
  split;auto.
  intros.
  specialize (HT _ H) as [? [? ?]].
  eexists. split;eauto.
  exists v. auto.
Qed.

Lemma hoare_coqprop_preintro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P Q (P': Prop),
  (P' -> Δ ⊢ {{P}} c {{Q}})->
  Δ ⊢ {{!! P' && P}} c {{Q}}.
Proof.
  unfold valid_contextualtriple. simpl. intros * HT * Hcallees.
  unfold valid_triple.
  intros * Hmem HP.
  destruct HP. unfold coq_prop in H.
  specialize (HT H _ Hcallees _ _ _ Hmem H0) as [HTerr HT].
  split;auto.
Qed.

Lemma hoare_coqprop_postintro {lgst : lgstate} {callc: @calllang_envstate local_cstate global_cstate} : forall  Δ c P Q (P': Prop),
  P' -> Δ ⊢ {{P}} c {{Q}}->
  Δ ⊢ {{P}} c {{!! P' &&  Q}}.
Proof.
  intros.
  eapply hoare_conseq_post;eauto.
  pose proof (prop_add_left Q P').
  apply logic_equiv_derivable1 in H1 as [? ?]; eauto.
  apply coq_prop_right;auto.
Qed.

Section contextual_soundness.

  Context {lgst : lgstate}.
  Context {callc: @calllang_envstate local_cstate global_cstate}.

  Variable default: local_env.
  
  Definition func_closed_wrt_lvars (P : assertion) : Prop :=
  forall l1 l2 g m,
  P (mk_lstate l1 g m) = P (mk_lstate l2 g m).

  Definition fspec_closed_wrt_lvars (fspec : funcspec) : Prop :=
    (forall w, func_closed_wrt_lvars (fspec.(FS_Pre) w)) /\
    (forall w, func_closed_wrt_lvars (fspec.(FS_Post) w)).

  Definition triple_body p Delta f fspec :=
    match find (fun fs => func_eqb (fst fs) f) p with
    | None => False
    | Some (_, c) =>
      forall w,
        valid_contextualtriple Delta (fspec.(FS_Pre) w) c (fspec.(FS_Post) w)
    end.


  Definition valid_triple_nrm  (χnrm : func -> global_cstate -> global_cstate -> Prop): @HT_validity local_cstate (Langstmts) :=
    fun P c Q =>
    forall st1 m1 mf, join m1 mf st1.(st_mem)  -> 
      P (mk_lstate st1.(lenv) st1.(genv) m1) -> 
    forall st2, (evalnrm χnrm c) st1 st2 -> 
      exists m2, join m2 mf st2.(st_mem) /\ Q (mk_lstate st2.(lenv) st2.(genv) m2).

  Definition funcspecs_sat_nrm (χnrm : func -> global_cstate -> global_cstate  -> Prop)
                        (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 m1 mf (w : fspec.(FS_With)),
      join m1 mf st1.(st_mem) ->
      fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
      forall gst2, 
        (χnrm f) (mk_gstate st1.(genv) st1.(st_mem)) 
                    gst2 ->
        exists m2, 
          join m2 mf gst2.(gst_mem)  /\
          fspec.(FS_Post) w (mk_lstate st1.(lenv) gst2.(ggenv) m2).

  Definition valid_contextualtriple_nrm (Delta : funcspecs) : @HT_validity local_cstate (Langstmts) :=
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


  Definition funcspecs_sat_err (χ : func -> @denosem global_cstate)
      (Delta : funcspecs) : Prop :=
    forall f fspec,
    In (f, fspec) Delta -> 
    forall st1 m1 mf (w : fspec.(FS_With)),
      join m1 mf st1.(st_mem) ->
      fspec.(FS_Pre) w (mk_lstate st1.(lenv) st1.(genv) m1) ->
      ~ (χ f).(err) (mk_gstate st1.(genv) st1.(st_mem)).


  Lemma funcspecs_sat_decompose:  forall (χnrm : func -> global_cstate -> global_cstate -> Prop) 
    (χerr : func -> global_cstate -> Prop) (Delta : funcspecs),
    funcspecs_sat_err (fun f => {| nrm:= χnrm f; err := χerr f |} ) Delta ->
    funcspecs_sat_nrm (χnrm) Delta ->
    funcspecs_sat (fun f => {| nrm:= χnrm f; err := χerr f |} ) Delta.
  Proof.
    unfold funcspecs_sat, funcspecs_sat_err, funcspecs_sat_nrm, prosem; cbn.
    intros.
    split.
    eapply H;eauto.
    eapply H0;eauto.
  Qed. 

  Lemma funcspecs_sat_nerr_false: forall (χnrm : func -> global_cstate -> global_cstate -> Prop) (Delta : funcspecs),
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
    

  Lemma funcspecs_sat_triple_body_nrm : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body_nrm p Delta f fspec) Delta) ->
    funcspecs_sat_nrm (prosem_nrm default p) Delta.
  Proof.
    unfold triple_body_nrm, funcspecs_sat_nrm, valid_triple_nrm, prosem_nrm, Lfix.
    intros * HNoDup HCP HT * HDelta * Hm1 HP * Hev.
    rewrite Forall_forall in HT.
    rewrite Forall_forall in HCP.
    destruct Hev as [n Hev].
    revert HDelta Hm1 HP Hev. revert st1 m1 mf w gst2. revert f fspec.
    induction n; simpl in *; [contradiction | ].
    remember (Nat.iter n
    (fun (X : func -> global_cstate -> global_cstate -> Prop) (f0 : func) (st2 st3 : gstate) =>
     exists c : Langstmts,
       In (f0, c) p /\
       evalnrm X c {| lenv := default; genv := ggenv st2; st_mem := gst_mem st2 |}
         {| lenv := default; genv := ggenv st3; st_mem := gst_mem st3 |}) ∅)
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
    specialize (HCP _ HDelta).
    destruct HCP as [HCP HCP'].
    erewrite <- (HCP _ default) in HP. 
    specialize (HT w callees IHsat (mk_lstate default st1.(genv) st1.(st_mem)) m1 mf Hm1 HP _ Hev) as [m2 [Hm2 HQ] ].
    exists m2. split; auto.
    cbn in HQ.
    erewrite <- (HCP' _  st1.(lenv)) in HQ.
    auto.
  Qed.

  Lemma funcspecs_sat_triple_body_err : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body p Delta f fspec) Delta) ->
    funcspecs_sat_err (prosem default p) Delta.
  Proof.
    unfold funcspecs_sat_err,  prosem, Lfix;cbn.
    intros * HNoDup HCP HT * HDelta * Hm1 HP Herr.
    assert (Forall (fun '(f,fspec) => triple_body_nrm p Delta f fspec) Delta) .
    { eapply Forall_impl.
      2: exact HT.
      intros [? ?]. cbn. intros.
      eapply triple_body_imply_nrm;eauto.
    }
    pose proof (funcspecs_sat_triple_body_nrm p Delta HNoDup HCP H) as Hnrmsat.
    clear H.
    rewrite Forall_forall in HT.
    rewrite Forall_forall in HCP.
    destruct Herr as [n Herr].
    revert HDelta Hm1 HP Herr. revert st1 m1 mf w. revert f fspec.
    induction n; simpl in *; [contradiction | ].
    remember (Nat.iter n
    (fun (X : func -> global_cstate -> Prop) (f0 : func) (st2 : gstate) =>
     exists c : Langstmts, In (f0, c) p /\ evalerr (prosem_nrm default p) X c {| lenv := default; genv := ggenv st2; st_mem := gst_mem st2 |}) ∅)
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
    assert (funcspecs_sat (fun f => {| nrm:= (prosem_nrm default p) f; err := errcall f |} ) Delta).
    { unfold prosem.
      eapply funcspecs_sat_decompose;eauto.
      unfold funcspecs_sat_err.
      cbn. intros.
      unfold not. intros.
      eapply IHn;eauto.
    }
    specialize (HCP _ HDelta).
    destruct HCP as [HCP _].
    erewrite <- (HCP _ default) in HP. 
    specialize (HT1 w _ H (mk_lstate default st1.(genv) st1.(st_mem)) m1 mf Hm1 HP) as [? _]. clear H.
    cbn in H0.
    contradiction.
  Qed.

  Lemma funcspecs_sat_triple_body : forall (p : program) (Delta : funcspecs),
    NoDup (map fst p) ->
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body p Delta f fspec) Delta) ->
    funcspecs_sat (prosem default p) Delta.
  Proof.
    intros * HNoDup HCP HT.
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
    (Forall (fun '(f,fspec)=> fspec_closed_wrt_lvars fspec) Delta) ->
    (Forall (fun '(f,fspec) => triple_body ρ Delta f fspec) Delta) ->
    valid_contextualtriple Delta P c Q ->
    valid_triple (prosem default ρ) P c Q.
  Proof.
    intros.
    pose proof funcspecs_sat_triple_body _ _ H H0 H1.
    unfold valid_contextualtriple in H1.
    specialize (H2 _  H3).
    auto.
  Qed. 

End contextual_soundness.


End ContextualJoinStateGlobalEnv.


