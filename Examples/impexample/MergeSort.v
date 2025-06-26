Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
Require Import MonadLib.MonadLib.
Import StateRelMonad.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope monad.




Section  merge_monad.

Definition merge_body:
  list Z * list Z * list Z ->
  MONAD (list Z * list Z * list Z + list Z) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => return (inr (l3 ++ l2))
    | _, nil => return (inr (l3 ++ l1))
    | x :: l1', y :: l2' =>
        choice
          (test (x <= y);; return (inl (l1', l2, l3 ++ x :: nil)))
          (test (y <= x);; return (inl (l1, l2', l3 ++ y :: nil)))
  end.

  Definition merge_rel l l0 :=
    repeat_break merge_body (l, l0, nil).

  Definition merge_from_mid_rel l1 l2 l3 := 
    repeat_break merge_body (l1, l2, l3).

End  merge_monad.


Section mergesort_monad.

  (* Definition ext_split (l: list Z): MONAD (list Z * list Z) :=
    fun _ '(l0, l1) _ =>  l = l0 ++ l1 /\ Zlength l1 <= Zlength l0  + 1 /\ Zlength l0 <= Zlength l1 + 1. *)

   Definition ext_split (l: list Z): MONAD (list Z * list Z) :=
    fun _ '(l0, l1) _ =>  l = l0 ++ l1.

  Definition mergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => '(p1, q1) <-  ext_split x ;; 
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- W (p1) ;; 
                                    q2 <- W (q1) ;; 
                                    merge_rel p2 q2
                      end.

  Definition mergesortrec := Lfix (mergesortrec_f).

  Definition mergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- mergesortrec p1 ;; 
                                    q2 <- mergesortrec q1 ;; 
                                    merge_rel p2 q2
                      end
             end.

  Definition mergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- mergesortrec q1 ;; 
              merge_rel p2 q2.

  Definition mergesortrec_loc2 p2: list Z -> MONAD (list Z) :=
    fun q2 => merge_rel p2 q2.

  Lemma mono_mergesortrec_f: mono mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_mono_compose_right.
    unfold mono. hnf.
    intros f1 f2 H x.
    destruct x as (p & q).
    destruct q.
    reflexivity.
    assert (forall x, f1 x ⊆ f2 x). { intros.  sets_unfold. intros. apply H. auto. }
    erewrite H0.
    assert (forall x, @Sets.included (list Z -> MONAD (list Z)) _ (fun p2 => q2 <- f1 x;; merge_rel p2 q2) 
    (fun p2 => (q2 <- f2 x;; merge_rel p2 q2))).
    { intros x0 p2.  
    erewrite H0. reflexivity. }
    erewrite H1.
    reflexivity.
  Qed.
  
  Lemma continuous_mergesortrec_f: continuous mergesortrec_f.
  Proof.
    intros.
    unfold mergesortrec_f.
    eapply bind_continuous_compose_right.
    unfold continuous, sseq_continuous, sseq_mono.
    intros l Hl.
    intros x.
    destruct x as (p & q).
    destruct q.
    + sets_unfold. intros. split;intros. exists 1%nat. auto. destruct H. auto.
    + rewrite (omega_union_introa 
      (fun (n : nat) (x0 : list Z * list Z) =>
      let (p1, q1) := x0 in
      match q1 with
      | nil => return p1
      | _ :: _ =>
          p2 <- l n p1;;
          q2  <- l n q1;;
          merge_rel p2 q2
      end) (p, z :: q)).
      assert (increasing (fun (n:nat) (p2:list Z) => q2 <- l n (z::q) ;; 
      merge_rel p2 q2)) as Hl2. 
      { eapply (increasing_mono_increasing (fun ln => 
          fun p2 => q2 <- ln (z::q);; merge_rel p2 q2 ));eauto.
        eapply bind_mono_left'. }
      pose proof program_para_equiv (bind_omega_union_distr_both l _ Hl Hl2) p.
      clear Hl2.
      rewrite omega_union_introa in H.
      rewrite <- H. clear H.
      eapply bind_equiv;[reflexivity | ].
      intros p2.
      rewrite omega_union_introa.
      erewrite bind_omega_union_distr_r' with (c1 := l) (a:= (z :: q)).
      reflexivity.
  Qed.

  Lemma mergesortrec_unfold: mergesortrec == mergesortrec_f mergesortrec.
  Proof.
    apply Lfix_fixpoint.
    apply mono_mergesortrec_f.
    apply continuous_mergesortrec_f.
  Qed.

End mergesort_monad.

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

