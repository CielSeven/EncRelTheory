Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From AUXLib Require Import List_lemma VMap ListLib BinaryTree.
From FP Require Import SetsFixedpoints.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersFacts.
From LangLib.ImpP Require Import bst_lib.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope monad.

Section insert_while.

Context (k: key)
        (v: value).
    

Definition insert_body: (tree * partial_tree)%type -> program unit (CntOrBrk (tree * partial_tree)%type tree) :=
  fun '(t, P) =>
    match t with
    | empty => return (by_break ( combine_tree P (make_tree empty k v empty)))
    | make_tree a y v' b => 
        match Z.compare k y with
        | Lt => return (by_continue (a, LH y v' b :: P))
        | Eq => return (by_break (combine_tree P (make_tree a k v b)))
        | Gt => return (by_continue (b, RH y v' a :: P))
        end
    end.


Definition insert_loop: (tree * partial_tree)%type -> program unit tree :=
  repeat_break insert_body.

End insert_while.


Section insert_rec.

Context (k: key)
        (v: value).

Definition F_insert (f: tree -> MONAD (tree)): tree -> MONAD (tree) :=
  fun t => 
    match t with
    | empty => return (make_tree empty k v empty)
    | make_tree a y v' b =>
        match Key.compare k y with
        | Lt => l <- (f a) ;; return (make_tree l y v' b)
        | Eq => return (make_tree a k v b)
        | Gt => r <- (f b) ;; return (make_tree a y v' r)
        end
    end.


Definition insert : tree -> MONAD (tree) :=
  Lfix F_insert.

  Lemma insert_unfold:  insert  == F_insert (insert) .
  Proof.
    intros. unfold insert. 
    apply (Lfix_fixpoint' F_insert).
    unfold F_insert.
    mono_cont_auto.
  Qed.

End insert_rec.

Section  algorithm_correctness.



Context (k: key)
        (v: value).

Lemma bst_insert_keyset:
  forall tr,
  Hoare (fun _ => True)
        (insert k v tr)
        (fun rtr _ => (rtr).(keys) == Sets_singleton_setoid k ∪ tr.(keys))%sets.
Proof.
  intros.
  unfold insert.
  hoare_fix_nolv_auto tree.
  clear tr.
  intros insert_W H tr0.
  unfold F_insert.
  destruct tr0.
  - apply Hoare_ret'.
    intros.
    rewrite (key_set_make_tree (k, v) empty empty).
    rewrite key_set_empty.
    rewrite Sets_empty_union.
    reflexivity.
  - destruct (Key.compare k k0) eqn:?.
    + apply Hoare_ret'.
      apply Z.compare_eq_iff in Heqc.
      subst k0.
      intros.
      rewrite !(key_set_make_tree (k, v) tr0_1 tr0_2).
      sets_unfold; intros.
      unfold Sets_singleton_setoid.
      tauto.
    + apply Z.compare_lt_iff in Heqc.
      assert (k < k0) by auto.
      eapply Hoare_bind.
      apply H.
      intros tr0_1'.
      simpl.
      apply Hoare_ret'.
      intros.
      rewrite (key_set_make_tree (k0, v0) tr0_1' tr0_2).
      rewrite (key_set_make_tree (k0, v0) tr0_1 tr0_2).
      rewrite H1.
      sets_unfold; intros; tauto.
    + apply Z.compare_gt_iff in Heqc.
      eapply Hoare_bind.
      apply H.
      intros tr0_2'.
      simpl.
      apply Hoare_ret'.
      intros.
      rewrite (key_set_make_tree (k0, v0) tr0_1 tr0_2).
      rewrite (key_set_make_tree (k0, v0) tr0_1 tr0_2').
      rewrite H0.
      sets_unfold; intros; tauto.
Qed.

Theorem bst_insert_SearchTree:
  forall tr,
  Hoare (fun _ => SearchTree tr)
        (insert k v tr)
        (fun rtr _ => SearchTree rtr).
Proof.
  intros.
  unfold insert.
  hoare_fix_lv_auto_conj tree unit tt.
  { instantiate (1:= (fun tr (d: unit) rtr _ => (rtr).(keys) == Sets_singleton_setoid k ∪ tr.(keys))%sets).
    instantiate (1:= (fun tr (d: unit) _ => True)).
    simpl.
    intros. eapply bst_insert_keyset. }
  clear tr.
  simpl.
  intros insert_W HT1 H tr x.
  clear x. 
  unfold F_insert.
  destruct tr.
  - apply Hoare_ret'.
    intros.
    rewrite (SearchTree_make_tree (k,v) empty empty).
    cbn.
    repeat split.
    apply keys_key_lt_iff. apply empty_set_keys_keys_lt.
    apply key_keys_lt_iff. apply keys_keys_lt_empty_set.
  - destruct (Key.compare k k0) eqn:?.
    + apply Z.compare_eq_iff in Heqc. subst k0.
      apply Hoare_ret'.
      intros.
      inversion H0.
      rewrite (SearchTree_make_tree (k,v) tr1 tr2).
      split;auto.
    + apply Z.compare_lt_iff in Heqc.
      assert (k < k0) by auto.
      eapply Hoare_bind.
      eapply Hoare_conj.
      ++ eapply Hoare_conj.
        { eapply Hoare_conseq_pre; [ | apply HT1].
          intros. simpl;auto. exact tt.  }
        eapply Hoare_conseq_pre; [ | apply H].
        intros.
        inversion H1. tauto. exact tt.
      ++ instantiate (1 := fun _ _ => tr1.(keys) =<- k0 /\ k0 -<= tr2.(keys) /\  SearchTree tr2).
        unfold Hoare. intros. inversion H1. tauto.
      ++  
        intros tr1'.  
        apply Hoare_ret'.
        intros ? [[? ?] [? [? ?]]].
        rewrite (SearchTree_make_tree (k0,v0) tr1' tr2).
        split;auto.
        apply keys_key_lt_iff.
        pose proof keys_keys_lt_congr _ _ H1 (Sets_singleton_setoid (k0, v0).(key)) _ (ltac:(reflexivity)).
        rewrite H6.
        apply union_keys_keys_lt.
        rewrite <- key_key_lt_iff.
        rewrite <- keys_key_lt_iff.
        tauto. 
    + apply Z.compare_gt_iff in Heqc.
      eapply Hoare_bind.
      eapply Hoare_conj.
      ++ eapply Hoare_conj.
        { eapply Hoare_conseq_pre; [ | apply HT1].
          intros. simpl;auto. exact tt.  }
        eapply Hoare_conseq_pre; [ | apply H].
        intros.
        inversion H0. tauto. exact tt.
      ++ instantiate (1 := fun _ _ => tr1.(keys) =<- k0 /\ k0 -<= tr2.(keys) /\  SearchTree tr1).
        unfold Hoare. intros. inversion H0. tauto.
      ++  
        intros tr2'.  
        apply Hoare_ret'.
        intros ? [[? ?] [? [? ?]]].
        rewrite (SearchTree_make_tree (k0,v0) tr1 tr2').
        split;auto. split;auto.
        apply key_keys_lt_iff.
        pose proof keys_keys_lt_congr (Sets_singleton_setoid (k0, v0).(key)) _ (ltac:(reflexivity)) _ _ H0 .
        rewrite H5.
        apply keys_keys_lt_union.
        rewrite <- key_key_lt_iff.
        rewrite <- key_keys_lt_iff.
        tauto.
Qed.

Ltac unfold_f f:=
    match f with 
    | ?f0 ?a ?b => unfold_f (f0 a)
    | ?f0 ?a => unfold f0 in * 
    end.

  Ltac hoare_fix_lv_auto_conj_H A C c Hlemma D d:=
    match goal with 
  | |- @Hoare ?Σ ?R ?P (Lfix ?F ?a) ?Q =>
      let P1 := fresh "P" in evar (P1: A -> C -> Σ  -> Prop);
      let Q1 := fresh "Q" in evar (Q1: A -> C -> R -> Σ -> Prop);
      let P2 := fresh "P" in evar (P2: A -> D -> Σ  -> Prop);
      let Q2 := fresh "Q" in evar (Q2: A -> D -> R -> Σ  -> Prop);
      let h := fresh "h" in assert (P1 = P1) as h;[ 
      let P0 := eval pattern (c) in P in
      match P0 with 
      | ?P0' _ => 
      let P' := eval pattern (a) in P0' in
      match P' with  
      | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
      clear h;
      let h := fresh "h" in assert (Q1 = Q1) as h;[ 
      let Q0 := eval pattern (c) in Q in
      match Q0 with 
      | ?Q0' _ => 
      let Q' := eval pattern (a) in Q0' in
      match Q' with  
      | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
    clear h;
  let H:= fresh "H" in pose proof Hlemma as H;
  let h:= fresh "h" in 
  evar (h: A -> Prop);
  let H1:= fresh "H" in
  assert (forall a, h a) as H1;[ 
  let a0 := fresh "a" in intro a0;
  specialize (H a0);
  match type of H with 
  | Hoare _ ?f _ =>  unfold_f f 
  end; 
  match type of H with 
  |  @Hoare ?Σ ?R ?P (Lfix ?F ?a) ?Q =>
    let h := fresh "h" in assert (P2 = P2) as h;[ 
      let P0 := eval pattern (d) in P in
    match P0 with 
    | ?P0' _ => 
    let P' := eval pattern (a) in P0' in
    match P' with  
    | ?P'' _  => exact (Logic.eq_refl P'') end end| ];
    clear h;
    let h := fresh "h" in assert (Q2 = Q2) as h;[
     let Q0 := eval pattern (d) in Q in
      match Q0 with 
      | ?Q0' _ => 
      let Q' := eval pattern (a) in Q0' in
      match Q' with  
      | ?Q'' _  => exact (Logic.eq_refl Q'') end end| ];
    clear h;
    exact H
  end| ];
  eapply (Hoare_fix_logicv_conj _ P1 Q1 a c P2 Q2);[ 
  subst P1 Q1 P2 Q2 h;simpl in *; intros; apply H|
  subst P1 Q1 P2 Q2 ; clear h H H1
  ]
  end.

Theorem bst_insert_Abs:
  forall tr m,
  Hoare (fun _ => SearchTree tr /\ Abs tr m)
        (insert k v tr)
        (fun rtr _ => Abs rtr (Map.insert k v m)).
Proof.
  intros.
  unfold insert.
  unfold Abs.
  unfold Hoare.
  intros ? ? ? [? ?] ?.
  intros x y.
  rewrite insert_iff.
  rewrite H0.
  clear m H0.
  revert x y.
  revert s1 a s2 H H1.
  change (Hoare (fun _ => SearchTree tr)
        (Lfix (F_insert k v) tr)
        (fun rtr _ => (forall (x : Z) (y : Value.t),
                        x = k /\ y = v \/
                        x ~= k /\ tree_kv tr x y <->
                        tree_kv rtr x y) )).
  hoare_fix_lv_auto_conj_H tree unit tt bst_insert_SearchTree unit tt.
  clear tr.
  simpl.
  intros insert_W HT1 H tr x. clear x.
  unfold F_insert.
  destruct tr.
  - apply Hoare_ret'.
    intros. 
    rewrite (tree_kv_make_tree_iff (k,v) empty empty).
    rewrite tree_kv_empty_iff.
    simpl.
    tauto.
  - destruct (Key.compare k k0) eqn:?.
    + apply Z.compare_eq_iff in Heqc. subst k0.
      apply Hoare_ret'.
      intros.
      rewrite (tree_kv_make_tree_iff (k,v) tr1 tr2).
      rewrite (tree_kv_make_tree_iff (k,v0) tr1 tr2).
      simpl.
      assert (tree_kv tr1 x y -> x ~= k). {
        intros HH.
        apply tree_kv_key_set in HH.
        inversion H0.
        pose proof H1 _ HH. simpl in H3.
        Key.order.
      }
      assert (tree_kv tr2 x y -> x ~= k). {
        intros HH.
        apply tree_kv_key_set in HH.
        inversion H0. destruct H3.
        pose proof H3 _ HH. simpl in H5.
        Key.order.
      }
      tauto.
    + apply Z.compare_lt_iff in Heqc.
      assert (k < k0) by auto. clear Heqc. rename H0 into Heqc.
      eapply Hoare_bind.
      { eapply Hoare_conj with (Q1:= fun _ _ => tr1.(keys) =<- k0 /\ k0 -<= tr2.(keys) /\  SearchTree tr2).
        { unfold Hoare. intros. inversion H0. tauto.  }
        eapply Hoare_conj.
        { eapply Hoare_conseq_pre;[ | apply HT1]. 
          intros. inversion H0. tauto. exact tt. }
        eapply Hoare_conseq_pre;[ | apply H].
        intros. inversion H0. tauto. exact tt. }
      intros tr1'. 
      apply Hoare_ret'.
      sets_unfold. simpl. intros ? [[? [? ?]] [? ?]] x y.
      specialize (H4 x y).
      rewrite (tree_kv_make_tree_iff (k0,v0) tr1 tr2).
      rewrite (tree_kv_make_tree_iff (k0,v0) tr1' tr2).
      rewrite <- H4.
      simpl.
      assert (x = k0 -> x ~= k) by Key.order. 
      assert (tree_kv tr2 x y -> x ~= k). {
        intros.
        apply tree_kv_key_set in H6.
        pose proof H1 _ H6.
        Key.order.
      }
      tauto.
    + apply Z.compare_gt_iff in Heqc.
      eapply Hoare_bind.
      { eapply Hoare_conj with (Q1:= fun _ _ => tr1.(keys) =<- k0 /\ k0 -<= tr2.(keys) /\  SearchTree tr1).
        { unfold Hoare. intros. inversion H0. tauto.  }
        eapply Hoare_conj.
        { eapply Hoare_conseq_pre;[ | apply HT1]. 
          intros. inversion H0. tauto. exact tt. }
        eapply Hoare_conseq_pre;[ | apply H].
        intros. inversion H0. tauto. exact tt. }
      intros tr2'. 
      apply Hoare_ret'.
      sets_unfold. simpl. intros ? [[? [? ?]] [? ?]] x y.
      specialize (H4 x y).
      rewrite (tree_kv_make_tree_iff (k0,v0) tr1 tr2).
      rewrite (tree_kv_make_tree_iff (k0,v0) tr1 tr2').
      rewrite <- H4.
      simpl.
      assert (x = k0 -> x ~= k) by Key.order. 
      assert (tree_kv tr1 x y -> x ~= k). {
        intros.
        apply tree_kv_key_set in H6.
        pose proof H0 _ H6.
        Key.order.
      }
      tauto.
Qed.


Theorem bst_insert_fc:
  forall tr m,
  Hoare (fun _ => SearchTree tr /\ Abs tr m)
        (insert k v tr)
        (fun rtr _ => SearchTree rtr /\ Abs rtr (Map.insert k v m)).
Proof.
  intros.
  apply Hoare_conj;[ | apply bst_insert_Abs].
  eapply Hoare_conseq_pre; [ | apply bst_insert_SearchTree].
  intros. tauto.
Qed.

End  algorithm_correctness.
