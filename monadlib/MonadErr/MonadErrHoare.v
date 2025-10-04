Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrLoop.

Import SetsNotation.
Local Open Scope sets.

Export MonadNotation.
Local Open Scope monad.
Local Open Scope order_scope.
Local Open Scope Z_scope.

Section HoareBasic.
Import MonadErr.

Definition Hoare {Σ A: Type}
(P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop): Prop :=
  ((forall (a: A)(σ1 σ2: Σ), 
    P σ1 -> c.(nrm) σ1 a σ2 -> Q a σ2)
  /\ (forall (σ1: Σ), P σ1 -> c.(err) σ1 -> False)).


Lemma Hoare_proequiv:
  forall {A Σ: Type} (c1 c2: program Σ A) (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    c1 == c2 ->
    Hoare P c1 Q -> Hoare P c2 Q.
Proof.
  intros.
  unfold Hoare in *.
  destruct H0 as [H0 H1].
  unfold Sets.equiv in H; destruct H as [Hn He].
  split; intros.
  + specialize (H0 a σ1 σ2 H).
    apply H0; clear H0.    
    sets_unfold in Hn.
    apply Hn; auto.
  + specialize (H1 σ1 H).
    apply H1; clear H1.
    sets_unfold in He.
    apply He; auto.
Qed.

#[export] Instance Hoare_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==> iff) (@Hoare Σ A P).
Proof.
  unfold Proper, respectful; intros.
  subst x0; split; intros.
  - apply Hoare_proequiv with x; easy.
  - apply Hoare_proequiv with y; easy.
Qed.

Lemma Hoare_bind {A B Σ: Type}: 
  forall (P: Σ -> Prop) (Q : A -> Σ -> Prop) (R: B -> Σ -> Prop)
  (c1: program Σ A) (c2: A -> program Σ B) ,
    Hoare P c1 Q -> (forall a, Hoare (Q a) (c2 a) R) -> Hoare P (bind c1 c2) R.
Proof.
  unfold Hoare.
  intros.
  split; simpl.
  + unfold nrm_nrm; intros.
    destruct H2 as [? [? [? ?]]].
    destruct H.
    specialize (H0 x).
    destruct H0.
    eapply H0; eauto.
  + sets_unfold.
    unfold nrm_err; intros.
    destruct H2.
    - destruct H.
      apply (H3 σ1 H1 H2).
    - destruct H2 as [? [? [? ?]]].
      specialize (H0 x).
      destruct H; destruct H0.
      eapply H5; eauto.
Qed.

Lemma Hoare_assert {Σ: Type}:
  forall (P: Σ -> Prop) (Q: Prop),
    Q ->
    Hoare P (assert Q) (fun _ => P).
Proof.
  intros.
  unfold Hoare, assert; simpl; split; intros.
  + destruct H1; subst; tauto.
  + tauto.
Qed. 

Lemma Hoare_implies {A Σ: Type}:
  forall (P P': Σ -> Prop) (P0: Prop)
         (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P0 /\ P' σ) ->
    (P0 -> Hoare P' c Q) ->
    Hoare P c Q.
Proof.
  unfold Hoare; intros.
  split; intros.
  + specialize (H _ H1).
    destruct (H0 ltac:(tauto)); clear H0.
    eapply H3; eauto.
    tauto.
  + specialize (H _ H1).
    destruct (H0 ltac:(tauto)); clear H0.
    eapply H4; eauto.
    tauto.
Qed.

Lemma Hoare_unit_pre {A: Type} :
  forall (P: Prop) (c: program unit A) (Q: A -> unit -> Prop),
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof.
  intros.
  eapply Hoare_implies; eauto.
  intros; tauto.
Qed.

Lemma Hoare_cons_pre {B Σ: Type} : 
  forall (P P': Σ -> Prop) (c: program Σ B) (Q: B -> Σ -> Prop),
    (forall σ, P' σ -> P σ) ->
    Hoare P c Q ->
    Hoare P' c Q.
Proof.
  unfold Hoare; intros.
  destruct H0; split.
  + intros.
    eapply H0; eauto.
  + intros.
    eapply H1; eauto.
Qed.

Lemma Hoare_cons_post {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q Q': A -> Σ -> Prop),
    (forall a σ, Q a σ -> Q' a σ) ->
    Hoare P c Q ->
    Hoare P c Q'.
Proof.
  unfold Hoare; intros.
  split; try tauto.
  intros. destruct H0 as [H0 _].
  specialize (H0 a σ1 σ2).
  specialize (H a σ2). tauto.
Qed.

Lemma Hoare_choice {A Σ: Type}:
  forall (P: Σ -> Prop) (c1 c2: program Σ A) (Q: A -> Σ -> Prop),
    Hoare P c1 Q -> Hoare P c2 Q -> Hoare P (choice c1 c2) Q.
Proof.
  unfold Hoare; intros.
  destruct H as [H1 H2]; destruct H0 as [H3 H4].
  split; intros; unfold choice in H0; simpl in H0.
  - specialize (H1 a σ1); specialize (H3 a σ1).
    destruct H0; [apply H1 | apply H3]; auto.
  - specialize (H2 σ1); specialize (H4 σ1).
    destruct H0; [apply H2 | apply H4]; auto.
Qed.

Lemma Hoare_assume_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (P2 -> Hoare P1 c Q) -> Hoare P1 (assume!! P2;; c) Q.
Proof.
  split; intros; unfold test in H1; simpl in H1.
  - unfold nrm_nrm in H1. destruct H1 as [_ [? [[Hs HP] H1]]].
    subst σ1. specialize (H HP). destruct H as [H _].
    specialize (H a x σ2). tauto.
  - destruct H1; [tauto |].
    unfold nrm_err in H1. destruct H1 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H H2). destruct H as [_ H].
    specialize (H s). tauto.
Qed.

Lemma Hoare_assumeS {Σ: Type}:
  forall (P1 P2: Σ -> Prop),
    Hoare P1 (assume P2) (fun _ s => P1 s /\ P2 s).
Proof.
  intros.
  unfold Hoare; simpl; split; intros.
  - destruct H0; subst; easy.
  - tauto.
Qed.

Lemma Hoare_assumeS_bind {A Σ: Type}:
  forall (P1: Σ -> Prop) (P2: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (Hoare (fun s => P1 s /\ P2 s) c Q) -> Hoare P1 (assume P2;; c) Q.
Proof.
  intros.
  eapply Hoare_bind; [apply Hoare_assumeS|].
  simpl; auto.
Qed.

Lemma Hoare_assert_bind {A Σ: Type}:
  forall (P: Σ -> Prop) (P': Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> P') ->
    (P' -> Hoare P c Q) -> 
    Hoare P (assert P';; c) Q.
Proof.
  unfold Hoare; intros.
  split; intros; unfold assert in H2; simpl in H2.
  - unfold nrm_nrm in H2. destruct H2 as [_ [s [[Hs HP] Hn]]].
    subst σ1. specialize (H0 HP). destruct H0 as [H0 _].
    specialize (H0 a s σ2). tauto.
  - pose proof (H σ1) H1. 
    destruct H2; [tauto |].
    unfold nrm_err in H2. destruct H2 as [_ [s [[? ?] ?]]].
    subst σ1. specialize (H0 H3). destruct H0 as [_ H0].
    specialize (H0 s). tauto.
Qed.

Lemma Hoare_ret {A Σ: Type}:
  forall (P: Σ -> Prop) (a: A) (Q: A -> Σ -> Prop),
    (forall σ, P σ -> Q a σ) ->
    Hoare P (ret a) Q.
Proof.
  intros; unfold Hoare; simpl; split; intros; try tauto.
  destruct H1; subst. 
  specialize (H σ1); tauto.
Qed.

Definition continue_case {A B Σ: Type} (ab: CntOrBrk A B): (program Σ A) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | by_continue a => s1 = s2 /\ r = a
                          | by_break _ => ∅
                          end;
    err := ∅;
  |}.

Definition break_case {A B Σ: Type} (ab: CntOrBrk A B): (program Σ B) := 
  {|
    nrm := fun s1 r s2 => match ab with
                          | by_continue _ => ∅
                          | by_break b => s1 = s2 /\ r = b
                          end;
    err := ∅;
  |}.

Lemma Hoare_cnt_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a: A),
    (forall s, P s -> Q a s) ->
    Hoare P (@continue_case A B Σ (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; simpl.
  split; intros.
  - destruct H1; subst.
    apply H; auto.
  - tauto.
Qed.

Lemma Hoare_brk_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (b: B),
    (forall s, P s -> Q b s) ->
    Hoare P (@break_case A B Σ (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, break_case; simpl.
  split; intros.
  - destruct H1; subst.
    apply H; auto.
  - tauto.
Qed.

Lemma Hoare_brk_cnt {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: B -> Σ -> Prop) (a: A),
    Hoare P (@break_case A B Σ (by_continue a)) Q.
Proof.
  intros.
  unfold Hoare, break_case; simpl.
  split; intros; tauto.
Qed.

Lemma Hoare_cnt_brk {A B Σ: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (b: B),
    Hoare P (@continue_case A B Σ (by_break b)) Q.
Proof.
  intros.
  unfold Hoare, continue_case; simpl.
  split; intros; tauto.
Qed.

Lemma Hoare_sum {A B Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ (CntOrBrk A B)) (Q: A -> Σ -> Prop) (R: B -> Σ -> Prop),
    Hoare P (x <- c;; continue_case x) Q ->
    Hoare P (x <- c;; break_case x) R ->
    Hoare P c (fun x σ => match x with
                          | by_continue a => Q a σ
                          | by_break b => R b σ
                          end).
Proof.
  intros.
  unfold Hoare in *.
  split; intros.
  2:{ 
    destruct H as [_ H], H0 as [_ H0].
    specialize (H σ1 H1).
    unfold bind in H.
    simpl in H.
    sets_unfold in H.
    tauto.
  }
  destruct H as [H _], H0 as [H0 _].
  destruct a.
  - specialize (H a σ1 σ2 H1).
    apply H; clear H.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (by_continue a); exists σ2.
    simpl; tauto.
  - specialize (H0 b σ1 σ2 H1).
    apply H0; clear H0.
    unfold bind; simpl.
    unfold nrm_nrm.
    exists (by_break b); exists σ2.
    simpl; tauto.
Qed.

Lemma Hoare_conj {A Σ: Type}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop) (R: A -> Σ -> Prop),
    Hoare P c Q ->
    Hoare P c R ->
    Hoare P c (fun a σ => Q a σ /\ R a σ).
Proof.
  intros.
  unfold Hoare in *.
  split; try tauto.
  intros.
  destruct H as [H _], H0 as [H0 _].
  specialize (H a σ1 σ2).
  specialize (H0 a σ1 σ2).
  tauto.
Qed.

Lemma Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  unfold Hoare; intros.
  split.
  - intros a s1 s2 (x & ?) ?.
    specialize (H x).
    destruct H.
    apply (H a s1 s2); auto.
  - intros s1 (x & ?) ?.
    specialize (H x).
    destruct H.
    apply (H2 s1); auto.
Qed.

Lemma Hoare_stateless:
  forall {A Σ} (P: Prop) (c: program Σ A) Q,
    (P -> Hoare (fun _ => True) c Q) ->
    Hoare (fun _ => P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  split.
  - intros.
    apply H in H0.
    destruct H0.
    apply (H0 a σ1 σ2); auto.
  - intros.
    apply H in H0.
    destruct H0.
    apply (H2 σ1); auto.
Qed.

Lemma Hoare_stateless':
  forall {A Σ} (P: Prop) (P': Σ -> Prop) (c: program Σ A) Q,
    (P -> Hoare P' c Q) ->
    Hoare (fun s => P' s /\ P) c Q.
Proof.
  unfold Hoare; intros.
  sets_unfold; intros.
  split.
  - intros.
    specialize (H ltac:(tauto)).
    destruct H.
    apply (H a σ1 σ2); tauto.
  - intros.
    specialize (H ltac:(tauto)).
    destruct H.
    apply (H2 σ1); tauto.
Qed.

Lemma Hoare_empty {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop),
    Hoare P {|nrm:=∅; err:=∅; |} Q.
Proof.
  unfold Hoare; sets_unfold.
  intros.
  split; simpl; intros; tauto.
Qed.

End HoareBasic.

(** Tactics *)
Tactic Notation "hoare_bind" uconstr(H) :=
  eapply Hoare_bind; [apply H |]; intros.

(* for unit type *)
Tactic Notation "hoare_bind'" uconstr(H) :=
  eapply Hoare_bind; [apply H |]; simpl; intros _.

Ltac hoare_conj :=
  match goal with
    | |- Hoare _  _ (fun _ _ => _ /\ _) => apply Hoare_conj; [try hoare_conj | try hoare_conj]
    | |- Hoare _ _ _ => eapply Hoare_cons_pre
  end.

Ltac hoare_intros :=
  apply Hoare_pre_ex; intros.

Ltac stateless_intros :=
  repeat (apply Hoare_stateless || apply Hoare_stateless'); intros.

Ltac hoare_step :=
  unfold continue, break;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_step
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_step
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_l
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind; intros
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assumeS_bind
    | |- Hoare _ (assert _;; _) _ => apply Hoare_assert_bind; [ |intros]
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice
    | |- Hoare _ (ret _) _ => apply Hoare_ret; intros
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (match ?a with _ => _ end) _ => destruct a; hoare_step
  end; auto.

Ltac hoare_auto :=
  unfold continue, break;
  match goal with
    | |- Hoare _ (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto
    | |- Hoare _ (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto
    | |- Hoare _ (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_auto
    | |- Hoare _ (assume!! _;; _) _ => apply Hoare_assume_bind; intros; try hoare_auto
    | |- Hoare _ (assume _ ;; _) _ => apply Hoare_assumeS_bind; try hoare_auto
    | |- Hoare _ (assert _;; _) _ => apply Hoare_assert_bind; [auto |intros; try hoare_auto]
    | |- Hoare _ (choice _ _) _ => apply Hoare_choice; try hoare_auto
    | |- Hoare _ (ret _) _ => apply Hoare_ret; intros
    | |- Hoare _ (continue_case (by_continue _)) _ => apply Hoare_cnt_cnt; intros
    | |- Hoare _ (continue_case (by_break _)) _ => apply Hoare_cnt_brk
    | |- Hoare _ (break_case (by_continue _)) _ => apply Hoare_brk_cnt
    | |- Hoare _ (break_case (by_break _)) _ => apply Hoare_brk_brk; intros
    | |- Hoare _ (match ?a with _ => _ end) _ => destruct a; try hoare_auto
  end; auto.

Ltac monad_law :=
  repeat (rewrite bind_assoc ||
          rewrite bind_ret_l ||
          rewrite bind_ret_r).

Ltac intro_bound :=
  unfold Sets.equiv; simpl; unfold Sets.lift_equiv; intros.

Ltac monad_equiv :=
  unfold continue_case, break_case;
  repeat (prog_nf; try easy;
          apply bind_equiv; try easy;
          intro_bound).

Tactic Notation "hoare_apply" uconstr(H) :=
  eapply Hoare_proequiv;
  [ | apply H; try tauto];
  monad_equiv.


(** Hoare Logic For Recursions and Loops *)
Lemma Hoare_BW_fix {Σ A B: Type}:
  forall (f: (A -> program Σ B) -> (A -> program Σ B))
         (P: A -> Σ -> Prop) (Q: A -> B -> Σ -> Prop) (a: A),
    (forall W: A -> program Σ B,
        (forall a, Hoare (P a) (W a) (fun b s => Q a b s)) ->
        forall a, Hoare (P a) (f W a) (fun b s => Q a b s)) ->
    Hoare (P a) (BW_fix f a) (fun b s => Q a b s).
Proof.
  intros.
  unfold Hoare.
  unfold BW_fix, omega_lub, oLub_lift, LiftConstructors.lift_binder,
    omega_lub, oLub_program, ProgramPO.indexed_union; simpl.
  sets_unfold.
  assert (forall i, Hoare (P a) (Init.Nat.iter i f bot a) (Q a)).
  2:{
    unfold Hoare in H0.
    split. 
    - intros b s1 s2 H1 H2.
      destruct H2 as [i H2].
      eapply H0; eauto.
    - intros s1 H1 H2.
      destruct H2 as [i H2].
      eapply H0; eauto.
  }
  intros i; revert a.
  induction i.
  split; simpl; easy.
  simpl.
  apply H; auto.
Qed.

Lemma Hoare_repeat_break {Σ A B: Type}:
forall (f: A -> program Σ (CntOrBrk A B)) (P: A -> Σ -> Prop) (Q: B -> Σ -> Prop),
  (forall a, Hoare (P a) (f a) (fun ab σ =>
  match ab with
  | by_continue a => P a σ
  | by_break b => Q b σ
  end)) -> (forall a, Hoare (P a) (repeat_break f a) Q).
Proof.
  intros.
  unfold repeat_break.
  apply Hoare_BW_fix with (Q:= fun _ => Q).
  intros.
  unfold repeat_break_f.
  hoare_bind H.
  hoare_auto.
Qed.

Lemma range_plus_1_aux: forall (P: Z -> Prop) lo hi,
  (forall i, lo <= i < hi -> P i) ->
  (forall i, lo + 1 <= i < hi -> P i).
Proof.
  intros.
  apply H.
  lia.
Qed.

Lemma Hoare_range_iter' {A Σ: Type} : 
forall (f: Z -> A -> program Σ A) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (fun b => P (i+1) b)) -> 
  (forall a, Hoare (P lo a) (range_iter lo hi f a) (fun b => P hi b)).
Proof.
  intros.
  unfold range_iter.
  apply Hoare_cons_pre with (P:= fun s => P lo a s /\ lo <= lo <= hi). 
  intros; split; [auto| lia].
  unfold range_iter.
  apply Hoare_BW_fix with
    (P:= fun '(i, a) s => P i a s /\ lo <= i <= hi)
    (a:= (lo, a))
    (Q:= fun '(_, a) a' s => P hi a' s).
  clear a.
  intros; destruct a as [i a].
  unfold range_iter_f.
  hoare_auto.
  2:{ 
    assert (i = hi) by lia.
    subst; tauto. 
  }
  stateless_intros.
  specialize (H0 i (ltac:(lia)) a).
  hoare_bind H0.
  specialize (H1 (i+1, a0)); simpl in H1.
  eapply Hoare_cons_pre.
  2:apply H1.
  intros; simpl.
  split; [auto | lia].
Qed.


Lemma Hoare_range_iter_break' {A B Σ: Type} : 
forall (f: Z -> A -> program Σ (CntOrBrk A B)) (P: Z -> A -> Σ -> Prop) (Q: B -> Σ -> Prop) (lo hi: Z),
  lo <= hi ->
  (forall i, lo <= i < hi -> forall a,
     Hoare (P i a) (f i a) (fun res => match res with
                                       | by_continue a => P (i+1) a
                                       | by_break b => Q b
                                       end)) -> 
  (forall a, Hoare (P lo a) (range_iter_break lo hi f a)
               (fun res σ => match res with
                             | by_continue a => P hi a σ
                             | by_break b => Q b σ
                             end)).
Proof.
  intros.
  unfold range_iter.
  apply Hoare_cons_pre with (P:= fun s => P lo a s /\ lo <= lo <= hi). 
  intros; split; [auto| lia].
  unfold range_iter_break.
  apply Hoare_BW_fix with
    (P:= fun '(i, a) s => P i a s /\ lo <= i <= hi)
    (a:= (lo, a))
    (Q:= fun '_ res s =>
      match res with
      | by_continue a0 => P hi a0 s
      | by_break b => Q b s
      end).
  clear a.
  intros; destruct a as [i a].
  unfold range_iter_break_f.
  hoare_auto.
  2:{
    assert (i = hi) by lia.
    subst; tauto.
  }
  stateless_intros.
  specialize (H0 i (ltac:(lia)) a).
  hoare_bind H0.
  simpl.
  hoare_auto.
  specialize (H1 (i+1, a0)); simpl in H1.
  eapply Hoare_cons_pre.
  2:apply H1.
  intros; simpl.
  split; [auto | lia].
Qed.

Lemma Hoare_range_iter {A Σ: Type}:
  forall (f: Z -> A -> program Σ A)
         (Q: Σ -> Prop) (P: Z -> A -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a, 
      (forall σ, Q σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a, Hoare (P i a) (f i a) (P (i+1))) -> 
      Hoare Q (range_iter lo hi f a) (P hi).
Proof.
  intros.
  eapply Hoare_cons_pre; [ | apply (Hoare_range_iter' f P lo hi H H1)].
  auto.
Qed.

Lemma Hoare_range_iter_break {A B Σ: Type}:
  forall (f: Z -> A -> program Σ (CntOrBrk A B))
         (P: Z -> A -> Σ -> Prop)
         (Q1: Σ -> Prop)
         (Q2: B -> Σ -> Prop) (lo hi: Z),
    lo <= hi ->
    forall a,
      (forall σ, Q1 σ -> P lo a σ) ->
      (forall i, lo <= i < hi -> forall a,
         Hoare (P i a) (f i a) (fun res => match res with
                                           | by_continue a => P (i+1) a
                                           | by_break b => Q2 b
                                           end)) -> 
      Hoare Q1
            (range_iter_break lo hi f a)
            (fun res σ => match res with
                          | by_continue a => P hi a σ
                          | by_break b => Q2 b σ
                          end).
Proof.
  intros.
  eapply Hoare_cons_pre; [ | apply (Hoare_range_iter_break' f P Q2 lo hi H H1)].
  auto.
Qed.

Lemma range_iter_no_iter {A Σ: Type} : 
  forall (f: Z -> A -> program Σ A) (P: A -> Σ -> Prop) (lo hi: Z),
  hi < lo ->
  (forall a, Hoare (P a) (range_iter lo hi f a) P).
Proof.
  intros.
  rewrite range_iter_unfold.
  hoare_auto.
  lia.
Qed.




(********************************************************************************)
(************************     Other Hoare premitives     ************************)
(************************       1. weakest precondition  ************************)
(************************       1. angelic Hoare         ************************)
(********************************************************************************)
Section Hoare_defs.
Import MonadErr.
(* Weakest liberal precondition  *)
Definition weakestpre {Σ A: Type}
  (c: program Σ A)
  (Q: A -> Σ -> Prop): Σ -> Prop := 
    fun σ =>  ~ c.(err) σ /\ forall r σ', (σ, r, σ') ∈ c.(nrm) -> Q r σ'.

Definition valid_angelic_triple {Σ A: Type}
  (P: Σ -> Prop)
  (c: program Σ A)
  (Q: A -> Σ -> Prop): Prop := 
    forall s1, P s1 -> exists a s2, (s1, a, s2) ∈ c.(nrm) /\ Q a s2.

End Hoare_defs.
Section WLPrules.
Import MonadErr.
  Context {Σ A B: Type}.

  Theorem wp_spec (c: program Σ A) (s1 s2:Σ) a:
    c.(nrm) s1 a s2 -> 
    forall Q,
    s1 ∈ (weakestpre c Q) ->
    s2 ∈ (Q a).
  Proof.
    unfold weakestpre; intros H0 Q H1.
    sets_unfold in H1. destruct H1.
    apply H1;auto.
  Qed.

  Theorem wp_spec_err (c: program Σ A) (s1:Σ) Q:
    s1 ∈ (weakestpre c Q) ->
    ~ err c s1.
  Proof.
    unfold weakestpre; intros. 
    sets_unfold in H. tauto.
  Qed.

  Theorem wp_self (c: program Σ A) (s: Σ):
    ~ err c s ->
    s ∈ (weakestpre c (fun a s' => c.(nrm) s a s')).
  Proof.
    intros. unfold weakestpre. sets_unfold. split;auto. 
  Qed.
 
  Theorem wp_Hoare (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare (weakestpre c Q) c Q.
  Proof.
    unfold weakestpre, Hoare.
    split. 
    intros s1 a s2 [? H0]. auto.
    intros ? [? ?]. auto.
  Qed.

  Theorem wp_Hoare_iff (P: Σ -> Prop) (Q: A -> Σ -> Prop) (c: program Σ A):
    P ⊆ (weakestpre c Q) <->
    Hoare P c Q.
  Proof.
    split;intros.
    - 
    eapply Hoare_cons_pre;[ | apply wp_Hoare].
    sets_unfold in H.
    auto.
    - unfold weakestpre, Hoare in *.
      destruct H.
      sets_unfold. 
      intros.
      split. unfold not. apply H0;auto.
      intros. 
      eapply H;eauto.
  Qed.

  Lemma wp_progequiv (c1 c2: program Σ A) (Q: A -> Σ -> Prop):
    c2 == c1 ->
    (weakestpre c1 Q == weakestpre c2 Q)%sets.
  Proof.
    intros.
    destruct H. 
    unfold weakestpre. intros s1. 
    split;intros [? ?].
    - split. unfold not in *. intros. apply H. apply errequiv;auto. 
      intros. apply H0. apply nrmequiv. auto.
    - split. unfold not in *. intros. apply H. apply errequiv;auto. 
      intros. apply H0. apply nrmequiv. auto.
  Qed.

  Lemma wp_conseq (c: program Σ A) (Q1 Q2: A -> Σ -> Prop):
    Q1 ⊆ Q2 ->
    weakestpre c Q1 ⊆ weakestpre c Q2.
  Proof.
    unfold weakestpre; intros H s1 [? ?].
    split;auto.
    intros.
    apply H. 
    auto.
  Qed.

  Lemma wp_bind (f: program Σ A) (g: A -> program Σ B) (Q: B -> Σ -> Prop):
  (weakestpre (x <- f;; g x) Q ==  weakestpre f (fun a => weakestpre (g a) Q))%sets.
  Proof.
    intros s1. 
    unfold weakestpre. unfold_monad.
    split. 
    - intros [? ?].
      split.
      + sets_unfold in H.
        tauto.
      + split.
        { sets_unfold in H. unfold not in *. intros. apply H.
          right. do 2 eexists. split;eauto. apply H1. }  
        intros.
        apply H0.
        exists r , σ'.
        split;auto.
    - intros [? ?].
      split.
      + sets_unfold. unfold not. intros [ | ];[tauto | ].
        destruct H1 as [a [s2' [? ?]]].
        apply H0 in H1 as [? _].
        tauto.
      + intros.
        destruct H1 as [a [s2' [? ?]]].
        apply H0 in H1 as [_ ?].
        apply H1;auto.
  Qed.

  Lemma wp_ret (a: A) (Q: A -> Σ -> Prop):
    (weakestpre (ret a) Q == (Q a))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H as [_ ?].
      apply H.
      unfold_monad. sets_unfold.
      auto.
    - unfold weakestpre.
      unfold_monad.
      split;[auto | ].
      intros ? ? [? ?].
      subst.
      auto.
  Qed.

  Lemma wp_choice (c1 c2: program Σ A) (Q: A -> Σ -> Prop):
    (weakestpre (choice c1 c2) Q == (weakestpre c1 Q) ∩ (weakestpre c2 Q))%sets.
  Proof.
    intros s1.
    unfold weakestpre, choice. 
    cbn [err nrm].
    sets_unfold. 
    split;intros [? ?].
    - split.
      + split;auto.
      + split;auto. 
    - destruct H. destruct H0.
      split;[tauto | ].
      intros.
      destruct H3 as [H3 | H3].
      apply H1;auto.
      apply H2;auto.
  Qed.

  Lemma wp_assume_coqprop (P: Prop) (Q: unit -> Σ -> Prop):
    P ->
    (weakestpre (assume!! P) Q == (Q tt))%sets.
  Proof.
    intros H s1.
    split;intros.
    - unfold weakestpre in H0.
      destruct H0 as [_ ?].
      apply H0.
      unfold testPure in *. cbn [nrm] in *.
      sets_unfold.
      auto.
    - unfold weakestpre, testPure.
      simpl. split;[auto | ].
      intros ? ? [? ?].
      subst. destruct r.
      auto.
  Qed.

  Lemma wp_assume (P: Σ -> Prop) (Q: unit -> Σ -> Prop):
    (weakestpre (assume P) Q == (fun s => P s -> Q tt s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      apply H.
      unfold test.
      split;auto.
    - unfold weakestpre, test.
      simpl. split;[auto | ].
      intros ? ? [? ?].
      subst. destruct r.
      auto.
  Qed.

  Lemma wp_any (P: Type) (Q: P -> Σ -> Prop):
    (weakestpre (any P) Q == (fun s => forall a, Q a s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H as [_ H].
      apply H.
      unfold any. sets_unfold. simpl.
      auto.
    - unfold weakestpre.
      unfold any. simpl.
      split;[auto | ].
      intros. sets_unfold in H0.  
      subst.
      apply H.
  Qed.

  Lemma wp_assert (P: Prop) (Q: unit -> Σ -> Prop):
    (weakestpre (assert P) Q == (fun s => P /\ Q tt s))%sets.
  Proof.
    intros s1.
    split;intros.
    - unfold weakestpre in H.
      destruct H.
      unfold assert in *. 
      cbn in *.
      split;[tauto | ].
      apply H0.
      sets_unfold.
      tauto.
    - unfold weakestpre, assert.
      simpl. split;[tauto | ].
      intros ? ? [? ?].
      subst. destruct r.
      tauto.
  Qed.


End WLPrules.

