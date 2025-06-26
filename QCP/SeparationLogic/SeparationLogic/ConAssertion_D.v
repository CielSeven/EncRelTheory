Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Import Integers.

From SimpleC.SL Require Import Mem.


Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Parameter token : Type.

Parameter STS_state : Type.

Definition TokenSet : Type := token -> Prop.

Parameter InvownedToken : STS_state -> TokenSet -> Prop.
Parameter InvownedMem : STS_state -> mem -> Prop.

Definition valid_Lstate (s_STS : STS_state -> Prop) (s_token : TokenSet) := forall s t, s_STS s -> InvownedToken s t -> s_token ∩ t == ∅.

Record Lstate : Type := mk_Lstate {
  s_mem : mem ;
  s_STS : STS_state -> Prop; 
  s_token : TokenSet; 
  valid : valid_Lstate s_STS s_token
}.


Theorem Lstate_eq_split : forall n m, n.(s_mem) = m.(s_mem) -> n.(s_STS) == m.(s_STS) -> n.(s_token) == m.(s_token) ->
n = m.
Proof.
  intros.
  destruct n,m; simpl in *.
  assert (s_STS0 = s_STS1). { apply pred_ext1; tauto. }
  assert (s_token0 = s_token1). { apply pred_ext1; tauto. }
  subst.
  assert (valid0 = valid1). 
  {
    apply proof_irrelevance. 
  }
  subst. auto.
Qed.

Ltac Lstate_split := apply Lstate_eq_split.

Definition STS_state_transition : Type := (STS_state * TokenSet) -> (STS_state * TokenSet) -> Prop.

Definition TokenSet_join (s1 s2 s3 : TokenSet) : Prop :=
  s3 == s1 ∪ s2 /\ s1 ∩ s2 == ∅.

Definition valid_transtion (s1 s2: STS_state * TokenSet) : Prop := 
  match s1, s2 with 
  | (st1, token1), (st2, token2) =>  
      exists tk1 tk2 tkf, 
        InvownedToken st1 tk1 /\ InvownedToken st2 tk2 /\
        TokenSet_join tk1 token1 tkf /\ 
        TokenSet_join tk2 token2 tkf
  end.

Definition transtion_disjoint_preserved (T : STS_state_transition) := forall s1 s2 token1 token2 t1 t2,
  T (s1,token1) (s2,token2) ->
  InvownedToken s1 t1 -> InvownedToken s2 t2 ->
  token1 ∩ t1 == ∅ /\ token2 ∩ t2 == ∅.

Definition transition_token_preserved (T : STS_state_transition) := forall s1 s2 token1 token2 syst1 syst2 tf, 
  T (s1,token1) (s2,token2) ->
  InvownedToken s1 syst1 -> InvownedToken s2 syst2 ->
  TokenSet_join token1 syst1 tf <-> TokenSet_join token2 syst2 tf.  

Definition STS_state_join (s1 s2 s3 : STS_state -> Prop) : Prop :=
  s3 == s1 ∩ s2.

Definition state_join (s1 s2 s3: Lstate) : Prop := 
  mem_join s1.(s_mem) s2.(s_mem) s3.(s_mem) /\ 
  TokenSet_join s1.(s_token) s2.(s_token) s3.(s_token) /\ 
  STS_state_join s1.(s_STS) s2.(s_STS) s3.(s_STS).
  
Theorem valid_state_join : forall s1 s2 s3, 
  state_join s1 s2 s3 ->  
  valid_Lstate (s3.(s_STS)) (s3.(s_token)).
Proof.
  intros.
  assert (valid_Lstate (s1.(s_STS)) (s1.(s_token))) by (exact s1.(valid)).
  assert (valid_Lstate (s2.(s_STS)) (s2.(s_token))) by (exact s2.(valid)).
  unfold valid_Lstate.
  intros. unfold state_join in H.
  destruct H as [ ? [? ?]].
  unfold STS_state_join, TokenSet_join in *.
  destruct H4.
  rewrite H4.
  rewrite Sets_intersect_union_distr_r.
  unfold valid_Lstate in *.
  sets_unfold in H5.
  apply H5 in H2.
  destruct H2.
  specialize (H0 _ _  H2 H3).
  specialize (H1 _ _ H7 H3).
  rewrite H0. rewrite H1. rewrite Sets_empty_union. reflexivity.
Qed. 

(* rely_closed may be used when proof*)
Definition rely_closed (ls : Lstate) (T : STS_state_transition) : Prop := forall s1 s2 t1 t2, 
  ls.(s_STS) s1 -> 
  InvownedToken s1 t1 -> InvownedToken s2 t2 -> 
  T (s1 , Sets.complement (ls.(s_token) ∪ t1)) (s2, Sets.complement (ls.(s_token) ∪ t2)) -> 
  ls.(s_STS) s2 .

Axiom WZY_THM: forall (T : STS_state_transition) s1 s2 token1 token2 token3 t1 t2, 
  T (s1, token1) (s2, token2) ->
    token1 ∩ token3 == ∅ ->
    InvownedToken s1 t1 ->
    InvownedToken s2 t2 ->
    token3 ∩ t1 == ∅ ->
  T (s1, token1 ∪ token3) (s2, token2 ∪ token3).

Theorem keep_rely_closed : forall T ls1 ls2 ls3,
  state_join ls1 ls2 ls3 -> 
  rely_closed ls1 T ->
  rely_closed ls2 T ->
  transtion_disjoint_preserved T ->
  transition_token_preserved T ->
  rely_closed ls3 T.
Proof.
  intros.
  assert (valid_ls1 : valid_Lstate (ls1.(s_STS)) (ls1.(s_token))) by (exact ls1.(valid)).
  assert (valid_ls2 : valid_Lstate (ls2.(s_STS)) (ls2.(s_token))) by (exact ls2.(valid)).
  rename H2 into valid_trans_disjoin.
  rename H3 into valid_trans_token.
  unfold state_join in *.
  unfold rely_closed. intros.
  destruct H as [? [ ? ? ]].
  unfold TokenSet_join in H6.
  unfold STS_state_join in H7.
  sets_unfold in H7.
  intros.
  apply H7. apply H7 in H2. 
  clear H7.
  replace (s_token ls3) with (s_token ls1 ∪ s_token ls2) in H5.
  2: { 
    apply pred_ext1.
    intros.
    destruct H6. sets_unfold in H6.
    rewrite H6. sets_unfold. tauto.
  }
  destruct H6 , H2. sets_unfold in H7.
  assert (Sets.complement (s_token ls1 ∪ s_token ls2) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1) ∪ t1).
  {
    rewrite! Sets_complement_union.
    rewrite! Sets_union_intersect_distr_r.
    rewrite Sets_complement_self_union.
    rewrite Sets_intersect_full.
    rewrite <- Sets_union_intersect_distr_r.
    sets_unfold.
    intros.
    split ; intros ; try tauto.
    destruct H9 ; try tauto.
    split ; intro.
    + specialize (valid_ls1 _ _ H2 H3).
      sets_unfold in valid_ls1.
      eapply valid_ls1 ; eauto. 
    + specialize (valid_ls2 _ _ H8 H3).
      sets_unfold in valid_ls2.
      eapply valid_ls2 ; eauto.
  }
  assert (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1) ∩ t1 == ∅).
  {
    rewrite !Sets_complement_union.
    rewrite Sets_intersect_assoc.
    rewrite Sets_complement_self_intersect.
    rewrite Sets_intersect_empty. reflexivity.
  }
  split.
  - eapply (H0 s1) ; eauto ; try tauto.
    specialize (valid_trans_token _ _ _ _ _ _ (Sets.complement
    (s_token ls1 ∪ s_token ls2)) H5 H3 H4).
    unfold TokenSet_join in valid_trans_token.
    assert (Sets.complement (s_token ls1 ∪ t1) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1) ∪ (s_token ls2)).
    {
      rewrite! Sets_complement_union.
      rewrite! Sets_union_intersect_distr_r.
      rewrite Sets_complement_self_union.
      rewrite Sets_intersect_full.
      rewrite <- Sets_union_intersect_distr_r.
      sets_unfold.
      intros.
      split ; intros ; try tauto.
      destruct H11 ; split ; intro ; try tauto.
      + eapply H7 ; eauto.
      + specialize (valid_ls2 _ _ H8 H3).
        sets_unfold in valid_ls2.
        eapply valid_ls2 ; eauto.
    }
    assert (Sets.complement (s_token ls1 ∪ s_token ls2) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∪ t2 /\ Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∩ t2 == ∅). { apply valid_trans_token ; tauto. } 
    clear valid_trans_token.
    replace (Sets.complement (s_token ls1 ∪ t1)) with 
      ((Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1)) ∪ (s_token ls2)). 
    2: {
      sets_unfold.
      apply pred_ext1. sets_unfold in H11. intro. rewrite H11. reflexivity.
    }
    destruct H12.
    replace (Sets.complement (s_token ls1 ∪ t2)) with 
      (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∪ (s_token ls2)).
    2:{
      sets_unfold.
      apply pred_ext1. intros.
      sets_unfold in H7.
      split.
      - intros. intro. destruct H14 ; try tauto.
        destruct H15.
        + eapply H7 ; eauto.
        + assert (~ (s_token ls1 a \/ s_token ls2 a)).
          { sets_unfold in H12.
            apply H12. tauto.
          }
          tauto.
      - intros. tauto.
      }
    eapply WZY_THM ; eauto.
    sets_unfold. intros ; split ; intros ; tauto.
  - eapply (H1 s1) ; eauto ; try tauto.
  specialize (valid_trans_token _ _ _ _ _ _ (Sets.complement
  (s_token ls1 ∪ s_token ls2)) H5 H3 H4).
  unfold TokenSet_join in valid_trans_token.
  assert (Sets.complement (s_token ls2 ∪ t1) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1) ∪ (s_token ls1)).
  {
    rewrite! Sets_complement_union.
    rewrite! Sets_union_intersect_distr_r.
    rewrite Sets_complement_self_union.
    rewrite Sets_full_intersect.
    rewrite <- Sets_union_intersect_distr_r.
    sets_unfold.
    intros.
    split ; intros ; try tauto.
    destruct H11 ; split ; intro ; try tauto.
    + eapply H7 ; eauto.
    + specialize (valid_ls1 _ _ H2 H3).
      sets_unfold in valid_ls1.
      eapply valid_ls1 ; eauto.
  }
  assert (Sets.complement (s_token ls1 ∪ s_token ls2) == Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∪ t2 /\ Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∩ t2 == ∅). { apply valid_trans_token ; tauto. } 
  clear valid_trans_token.
  replace (Sets.complement (s_token ls2 ∪ t1)) with 
    ((Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t1)) ∪ (s_token ls1)). 
  2: {
    sets_unfold.
    apply pred_ext1. sets_unfold in H11. intro. rewrite H11. reflexivity.
  }
  destruct H12.
  replace (Sets.complement (s_token ls2 ∪ t2)) with 
    (Sets.complement (s_token ls1 ∪ s_token ls2 ∪ t2) ∪ (s_token ls1)).
  2:{
    sets_unfold.
    apply pred_ext1. intros.
    sets_unfold in H7.
    split.
    - intros. intro. destruct H14 ; try tauto.
      destruct H15.
      + eapply H7 ; eauto.
      + assert (~ (s_token ls1 a \/ s_token ls2 a)).
        { sets_unfold in H12.
          apply H12. tauto.
        }
        tauto.
    - intros. tauto.
    }
  eapply WZY_THM ; eauto.
  sets_unfold. intros ; split ; intros ; tauto.
Qed. 

Definition state_empty (s: Lstate) : Prop := 
  mem_empty s.(s_mem) /\ 
  s.(s_token) == ∅ /\ s.(s_STS) == Sets.full.

Theorem empty_state_valid : valid_Lstate (Sets.full) ∅.
Proof.
  unfold valid_Lstate.
  intros.
  rewrite Sets_empty_intersect.
  reflexivity.
Qed.  

Definition empty_state : Lstate :=  {|
  s_mem := empty_mem ;
  s_STS := Sets.full;
  s_token := ∅;
  valid := empty_state_valid
|}.

Lemma empty_state_is_empty : state_empty empty_state.
Proof.
  unfold empty_state.
  repeat split ; simpl ; auto. 
Qed.

Module ConCLang <: LanguageSig.

  Definition model : Type := Lstate.

  Definition expr := model -> Prop .

  Definition join : model -> model -> model -> Prop := state_join.
  
  Definition is_unit : model -> Prop := state_empty.
End ConCLang.

Module ConCPrimitiveRule <: PrimitiveRuleSig ConCLang.
  Include DerivedNames ConCLang.
  Theorem unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Proof.
    intros. exists empty_state.
    unfold is_unit , join , state_join.
    split ; [apply empty_state_is_empty | ].
    intros. 
    split ; solve_empmem ; split ; unfold empty_state ; simpl.
    - unfold TokenSet_join. sets_unfold. tauto.
    - unfold STS_state_join. sets_unfold.  tauto. 
  Qed.
      
  Theorem unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Proof.
    intros.
    unfold is_unit, join in *.
    destruct H0 as [? [? ?]].
    destruct H as [? [? ?]].
    apply mem_empty_IS_empty_mem' in H. 
    rewrite H in *.
    apply mem_join_emp_r in H0.
    unfold TokenSet_join in *.
    unfold STS_state_join in *.
    rewrite H3 in H1. rewrite H4 in H2.
    destruct H1.
    rewrite Sets_union_empty in H1.
    rewrite Sets_intersect_full in H2.
    Lstate_split ; auto ; try (symmetry ; tauto).
  Qed.

  Theorem join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m).
  Proof.
    intros.
    unfold join , state_join, TokenSet_join in *.
    destruct H as [? [? ?]].
    split ; [|split].
    - apply mem_join_comm ; auto.
    - destruct H0. rewrite H0. rewrite Sets_union_comm.
      split ; [reflexivity | rewrite Sets_intersect_comm ; auto]. 
    - unfold STS_state_join in *.
      rewrite H1. rewrite Sets_intersect_comm. reflexivity.
  Qed.  

  Theorem join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz).
  Proof.
    intros.
    unfold join , state_join, TokenSet_join, STS_state_join in *.
    destruct H as [? [[? ?] ?]].
    destruct H0 as [? [[? ?] ?]].
    assert (valid_Lstate (s_STS my ∩ s_STS mz) (s_token my ∪ s_token mz) ). {
      unfold valid_Lstate.
      intros.
      sets_unfold in H7.
      destruct H7.
      eapply my.(valid) in H7.
      eapply mz.(valid) in H9.
      rewrite Sets_intersect_union_distr_r.
      erewrite H9 ; eauto.
      erewrite H7 ; eauto.
      rewrite Sets_empty_union. reflexivity.
    }
    exists (mk_Lstate (merge (s_mem my) (s_mem mz)) (s_STS my ∩ s_STS mz) (s_token my ∪ s_token mz) H7).
    simpl. 
    split ; (split ; [ | split ]).
    - apply disjoint_merge_mem_join.
      pose proof (mem_join_disjoint H0).
      apply disjoint_comm.
      eapply disjoint_mem_join_r ; eauto.
      apply disjoint_comm ; auto.
    - split ; try reflexivity.
      revert H1 H2 H4 H5.
      sets_unfold ; intros.
      split ; try tauto.
      intros. destruct H8.
      erewrite <- H5.
      split ; eauto.
      apply H1 ; auto.
    - reflexivity.
    - apply mem_join_merge_assoc_l.
      + eapply mem_join_disjoint ; eauto.
      + apply mem_join_eqmerge in H.
        rewrite <- H. auto.
    - split.
      + rewrite H4. rewrite H1.
        rewrite Sets_union_assoc. reflexivity.
      + rewrite Sets_intersect_union_distr_l.
        rewrite H2. rewrite Sets_empty_union.
        revert H1 H2 H4 H5.
        sets_unfold ; intros.
        split ; try tauto.
        intros. destruct H8.
        erewrite <- H5.
        split ; eauto.
        apply H1 ; auto.
    - rewrite H6. rewrite H3.
      rewrite Sets_intersect_assoc. reflexivity.
  Qed.

End ConCPrimitiveRule.

Module ConCRules := LogicTheorem ConCLang ConCPrimitiveRule.

Arguments ConCRules.exp {A}.


(* The following are basic definitions *)

(* The following are notations *)  
Declare Scope consac_scope.
Delimit Scope consac_scope with consac.
Local Open Scope consac_scope.

Notation "x |--₂ y" := (ConCRules.derivable1 x y) (at level 70, no associativity) : consac_scope.
Notation "x ₂--||--₂ y" := (ConCRules.logic_equiv x y) (at level 60, no associativity) : consac_scope.
Notation "x -*₂ y" := (ConCRules.wand x y) (at level 45, right associativity) : consac_scope.
Notation "x ->₂ y" := (ConCRules.impp x y) (at level 44, left associativity) : consac_scope.
Notation "x ||₂ y" := (ConCRules.orp x y) (at level 43, right associativity) : consac_scope.
Notation "x &&₂ y" := (ConCRules.andp x y) (at level 42, right associativity) : consac_scope.
Notation "x **₂ y" := (ConCRules.sepcon x y) (at level 41, right associativity) : consac_scope.
Notation " !!₂ P " := (ConCRules.coq_prop P) (at level 35, no associativity) :consac_scope.
Notation " 'TT₂' " := (ConCRules.truep) (at level 34, no associativity) : consac_scope.
Notation "'EX₂' x , p " :=
  (ConCRules.exp (fun x => p))
    (at level 45, x name, right associativity) : consac_scope.
Notation "'EX₂' x : t , p " :=
  (ConCRules.exp (fun x : t => p))
    (at level 45, x name, right associativity) : consac_scope.
Notation "'EX₂' x .. y , p" :=
  (ConCRules.exp (fun x => .. (ConCRules.exp (fun y => p)) ..))
    (at level 45, x binder, right associativity) : consac_scope.