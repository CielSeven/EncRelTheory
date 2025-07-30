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
  Lemma Exec_Seq : forall (P P': @asrt Σ)  s ks,
    (forall X, Exec P s X -> Exec P' skip X) ->
    (forall X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof. 
    unfold Exec; sets_unfold;intros.
    simpl_hdefs.
    destructs H0. 
    specialize (H (fun x => s.(nrm) st x)).
    assert ((exists σₕ0 : Σ, P σₕ0 /\ safe σₕ0 s (fun x : Σ => nrm s st x))).
    { eexists;splits;eauto. 
      unfold safe. simpl. sets_unfold. unfold weakestpre. auto. }
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

  Lemma Exec_Pure : forall (P: @asrt Σ) s s' ks,
    (forall X, Exec P s X -> Exec P s' X) ->
    (forall X, Exec P (seq s ks) X -> Exec P (seq s' ks) X).
  Proof. 
    unfold Exec; sets_unfold;intros.
    simpl_hdefs.
    destructs H0. 
    specialize (H (fun x => s.(nrm) st x)).
    assert ((exists σₕ0 : Σ, P σₕ0 /\ safe σₕ0 s (fun x : Σ => nrm s st x))).
    { eexists;splits;eauto. 
      unfold safe. simpl. sets_unfold. unfold weakestpre. auto. }
    specialize (H H2);clear H2.
    destructs H.
    exists st0. split;auto. 
    unfold weakestpre. sets_unfold.
    intros. unfold seq in H3. sets_unfold in H3. simpl in H3.
    destructs H3.
    apply H1.
    unfold seq;sets_unfold;simpl.
    eexists.
    split;eauto.
    apply H2. auto.
  Qed.

  Lemma highstepseq_derive : forall s (P P' : Σ -> Prop),
    ⊢∃ {{P}} s {{P'}} -> (forall ks X, Exec P (seq s ks) X -> Exec P' ks X).
  Proof.
    intros * H ks.
    eapply Exec_Seq;eauto.
    eapply highstepend_derive;eauto.
  Qed.


  Lemma Exec_Assume: forall (P b: @asrt Σ) X,
    P |-- b ->
    Exec P (assume b) X -> Exec P skip X.
  Proof.
    unfold Exec, derivable1; sets_unfold;intros.
    simpl_hdefs.
    destructs H0.
    eexists.
    split;eauto.
    unfold weakestpre in *.  simpl in *.
    sets_unfold.
    intros. subst.
    apply H in H0.
    apply H1.
    split;auto.
  Qed.

  Lemma Exec_Choice_left: forall (P: @asrt Σ) c1 c2 X,
    Exec P (choice c1 c2) X -> Exec P c1 X.
  Proof.
    unfold Exec; sets_unfold; intros.
    simpl_hdefs.
    destructs H.
    eexists.
    split;eauto.
    unfold weakestpre in *.  simpl in *.
    sets_unfold in H0.
    intros.
    apply H0. auto.
  Qed.
  Lemma Exec_Choice_right: forall (P: @asrt Σ) c1 c2 X,
    Exec P (choice c1 c2) X -> Exec P c2 X.
  Proof.
    unfold Exec; sets_unfold; intros.
    simpl_hdefs.
    destructs H.
    eexists.
    split;eauto.
    unfold weakestpre in *.  simpl in *.
    sets_unfold in H0.
    intros.
    apply H0. auto.
  Qed.

  Lemma Exec_While_End: forall (P b: @asrt Σ) c X,
    P |-- notB b ->
    Exec P (while b c) X -> Exec P skip X.
  Proof.
    unfold Exec, derivable1; sets_unfold;intros.
    simpl_hdefs.
    destructs H0.
    eexists.
    split;eauto.
    unfold weakestpre in *.  simpl in *.
    sets_unfold.
    intros. subst.
    apply H in H0.
    apply H1.
    unfold SetsFixedpoints.Lfix. sets_unfold.
    exists 1.
    simpl.
    right.
    split;auto.
  Qed.

  Lemma Exec_While_Unroll: forall (P b: @asrt Σ) c X,
    P |-- b ->
    Exec P (while b c) X -> Exec P (seq (c) (while b c)) X.
  Proof.
    unfold Exec, derivable1; sets_unfold;intros.
    simpl_hdefs.
    destructs H0.
    eexists.
    split;eauto.
    unfold weakestpre in *.  simpl in *.
    sets_unfold.
    intros. subst.
    apply H in H0.
    apply H1.
    unfold SetsFixedpoints.Lfix in *. sets_unfold.
    destruct H2 as [st0 [? ?]]. sets_unfold in H3.
    destruct H3 as [n ?].
    exists (S n).
    simpl.
    left.
    exists st.
    split;auto.
    exists st0.
    split;auto.
  Qed.

End  safe_rules.

End  NormalDenoExecLib.


From Coq Require Import String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Bool.Bool.
From Coq Require Import Relations.

Import StringSyntax.  (* Optional: allows writing string literals more easily *)
Local Open Scope string_scope.
Local Open Scope nat_scope.


Module AssignmentRules.

Import normaldeno.
Import NormalDenoConstructs.
Import HoareNormalDeno.

Definition Var := string. (* or any identifier type *)
Definition Val := nat.    (* adjust as needed *)

Definition State := Var -> Val.

(* Expressions are interpreted as state -> value *)
Definition Expr := State -> Val.

Definition update (σ : State) (x : Var) (v : Val) : State :=
  fun y => if String.eqb y x then v else σ y.

Definition assign (x : Var) (e : Expr) : @normaldeno.denosem State :=
  {|
    normaldeno.nrm := fun σ σ' => σ' = update σ x (e σ);
  |}.

Definition in_range (v lo hi : Val) := lo <= v <= hi.

Definition nd_assign (x : Var) (e1 e2 : Expr) : @normaldeno.denosem State :=
  {|
    normaldeno.nrm := fun σ σ' =>
      let lo := e1 σ in
      let hi := e2 σ in
      in_range (σ' x) lo hi /\
      (forall y, y <> x -> σ' y = σ y);
  |}.

Lemma exec_assign:
  forall (P X : State -> Prop) (x : Var) (e : Expr),
    Exec (fun σ => P (update σ x (e σ))) (assign x e) X ->
    Exec P skip X.
Proof.
  intros P X x e [σ [HP Hwp]].
  exists (update σ x (e σ)). split.
  - apply HP.
  - intros σ' Hskip. subst. apply Hwp.
    simpl. simpl in Hskip. sets_unfold in Hskip. auto.
Qed.

Lemma exec_nd_assign_backward :
  forall (P X : State -> Prop) (x : Var) (e1 e2 : Expr) (v : Val),
    (forall σ, P (update σ x v) -> e1 σ <= v <= e2 σ) ->
    Exec (fun σ => P (update σ x v)) (nd_assign x e1 e2) X ->
    Exec P skip X.
Proof.
  intros P X x e1 e2 v Hv [σ [HP Hwp]].
  exists (update σ x v). split.
  - apply HP.
  - intros σ' Hskip. subst. apply Hwp.
    simpl.
    unfold nd_assign. simpl.
    split.
    + unfold in_range. sets_unfold in HP. 
      simpl in Hskip.  sets_unfold in Hskip.  subst.
      unfold update. 
      rewrite String.eqb_refl.
      apply Hv. apply HP.
    + intros y Hneq.
      simpl in Hskip.  sets_unfold in Hskip. subst.
      unfold update. destruct (String.eqb y x) eqn:Heq.
      * apply String.eqb_eq in Heq. contradiction.
      * reflexivity.
Qed.


End AssignmentRules.



