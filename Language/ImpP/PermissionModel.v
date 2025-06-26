Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import QArith.
Require Import Coq.QArith.Qcanon.
Require Import Eqdep_dec.
Require Import Lqa.


Local Open Scope Qc_scope.
Notation " 2 " := (Q2Qc 2) : Qc_scope.
Notation "x '+ᶜ' y" := (Qcplus x y) (left associativity, at level 21):  Qc_scope.
Notation "x '-ᶜ' y" := (Qcminus x y) (left associativity, at level 21):  Qc_scope.

Definition Qc_leb := 
fun x y : Qc  => match (x ?= y)%Qc with
	           | Gt => false
               | _ => true
end.

Definition Qc_ltb := 
fun x y : Qc  => match (x ?= y)%Qc with
	           | Lt => true 
               | _ => false
end.

Ltac Qdes := match goal with
 | q:Q |- _ => let p:= fresh "z" in let p0:= fresh "z" in
               destruct q as [p p0]; Qdes
 | |- _ => idtac   end.
Ltac Qcdes := match goal with
 | q:Qc |- _ => let p:= fresh "q" in 
               destruct q as [p ?]; Qcdes
 | |- _ => cbn [this] in * end.
Ltac unfoldlt := try unfold Qclt, Qlt in *; try unfold  Qcle, Qle in *; try unfold  Qeq in *.

Ltac simpl_qc := 
  repeat progress match goal with 
  | H: ?x # ?y = ?u # ?z |- _ => inversion H;subst u z; clear H 
  | H: context [let (_, _) := snd (Z.ggcd ?x ?y) in _ ] |- _ => 
                                      let h:= fresh "H" in 
                                      pose proof Z.ggcd_correct_divisors x y as h;
                                      pose proof Z.ggcd_gcd x y;
                                      pose proof Z.gcd_nonneg x y;
                                      destruct (Z.ggcd x y) as [? [? ?]];simpl in *;
                                      destruct h
  | |-  context [let (_, _) := snd (Z.ggcd ?x ?y) in _ ]  => 
                                      let h:= fresh "H" in 
                                      pose proof Z.ggcd_correct_divisors x y as h;
                                      pose proof Z.ggcd_gcd x y;
                                      pose proof Z.gcd_nonneg x y;
                                      destruct (Z.ggcd x y) as [? [? ?]];simpl in *;
                                      destruct h
  | |- _ =>   rewrite ! Z.mul_1_r in *
  end.

Ltac qc_unfold := unfold Qclt, Qcdiv, Qcmult, Qcinv, Qcminus, Qcplus, Qcopp, 
                         Qc_ltb, Qc_leb, Qccompare, Qc_eq_bool in *.

Ltac qc_simpl:= cbn [Q2Qc this] in *;
                rewrite ? Qred_correct in *.

Module Perm.

Definition perRange (qc : Qc) : Prop := Q2Qc 0 < qc /\  (qc < Q2Qc 1 \/ qc == Q2Qc 1). 
Record t := mkper { frac: Qc; rpf: perRange frac }.
Lemma fullpermission_range: perRange 1.
Proof.
  intros. unfold perRange, Qclt. simpl. lra.
Qed.

Ltac permdes := match goal with
 | q:t |- _ => let p:= fresh "qc" in
              let rpf0 := fresh "rpf" in destruct q as [q rpf0]; 
              unfold perRange, Qclt in rpf0; simpl in rpf0;
              permdes
 | |- _ => cbn [frac] in * end.

Definition fullperm : t := mkper (1) fullpermission_range.

Definition readable_perm (p: t) := p.(frac) < 1.

Definition writable_perm (p: t) := p.(frac) = 1.

Definition writable_permB (p: t) : bool := Qc_eq_bool p.(frac) 1.

Lemma mkper_eq:
  forall x y Px Py, x = y -> mkper x Px = mkper y Py.
Proof.
  intros. subst y.
  assert (forall (n m: Qc) (P1 P2: n < m), P1 = P2).
  {
    unfold Qclt, Qlt, Z.lt; intros.
    apply  eq_proofs_unicity.
    intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  assert (forall (n m: Qc) (P1 P2: n == m), P1 = P2).
  {
    unfold Qeq;  intros.
    apply eq_proofs_unicity.


    intros c1 c2. pose proof Z.eq_dec c1 c2 as [? | ?];tauto.
  }
  destruct Px as [Px1 [Px2 | Px3]]; destruct Py as [Py1 [Py2 | Py3]].
  - rewrite (H _ _ Px1 Py1).
    rewrite (H _ _ Px2 Py2).
    reflexivity.
  - exfalso.
    apply Qc_is_canon in Py3.
    subst x.
    unfold Qclt, Qlt in *. lia.  
  - exfalso.
    apply Qc_is_canon in Px3.
    subst x.
    unfold Qclt, Qlt in *. lia.
  - rewrite (H _ _ Px1 Py1).
    rewrite (H0 _ _ Px3 Py3).
    reflexivity.   
Qed.

Local Open Scope Q_scope.
Lemma div2range : forall (q: Qc),   perRange q ->
  perRange (q/2).
Proof. unfold perRange, Qclt, Qlt, Qeq;simpl; intros. 
       destruct q as [[x y] ?]. simpl in *.
       pose proof Z.ggcd_correct_divisors x (Z.pos y).
       pose proof Z.ggcd_correct_divisors (x * 1) (Z.pos (y * 2)).
       pose proof Z.ggcd_gcd x (Z.pos y).
       pose proof Z.ggcd_gcd (x * 1) (Z.pos (y * 2)).
       pose proof Z.gcd_nonneg x (Z.pos y).
       pose proof Z.gcd_nonneg (x * 1) (Z.pos (y * 2)).
       destruct (Z.ggcd x (Z.pos y)) as [? [? ?]] eqn:?.
       destruct ((Z.ggcd (x * 1) (Z.pos (y * 2)))) as [? [? ?]] eqn:?.
       simpl in *.
       rewrite Z.mul_1_r in *.
       destruct H0; destruct H1.
       rewrite Z2Pos.id by lia.
       rewrite (Pos2Z.inj_mul y 2) in *.
       assert ((0 < x <= Z.pos y * 2 )%Z ) by lia.
       rewrite H1, H7 in H8.
       assert (z2 <> 0)%Z.
       { unfold not;intros. rewrite H3 in *.
         apply Z.gcd_eq_0_l in H9.
         lia.  }
       assert (z3 <= z4)%Z.
        { apply Zmult_lt_0_le_reg_r with (p := z2);lia. }   
       lia.
Qed.

Definition split (p: t) : t * t := 
  let q := p.(frac) in (mkper (q/2) (div2range q p.(rpf)), mkper (q/2) (div2range q p.(rpf)) ).

Lemma split_readable1: forall p x y,  split p = (x, y) -> 
  readable_perm x. 
Proof.
  unfold split, readable_perm;intros.
  inversion H. clear y H H2.
  destruct x. inversion H1;subst. clear H1.
  permdes. Qcdes. Qdes.
  unfold perRange in *.
  unfoldlt;simpl in *.
  pose proof Z.ggcd_correct_divisors (z * 1) (Z.pos (z0 * 2)).
  pose proof Z.ggcd_correct_divisors (z) (Z.pos (z0)).
  pose proof Z.gcd_nonneg (z * 1) (Z.pos (z0 * 2)) .
  pose proof Z.ggcd_gcd (z * 1) (Z.pos (z0 * 2)).
  destruct (Z.ggcd (z * 1) (Z.pos (z0 * 2))) as [? [? ?]] eqn:?.
  destruct (Z.ggcd (z) (Z.pos (z0))) as [? [? ?]] eqn:?.
  simpl in *.
  rewrite Z.mul_1_r in *.
  inversion canon. subst z5 z0.
  destruct H0, H. subst z.
  assert (z1 * z2 < (z1 * z3))%Z by lia.
  rewrite Z2Pos.id by lia.
  apply Zmult_gt_0_lt_reg_r  with (p := z1) .
  lia. lia. 
Qed.

Lemma split_readable2: forall p x y,  split p = (x, y) -> 
  readable_perm y.
Proof.
  unfold split, readable_perm;intros.
  inversion H. clear x H H1.
  destruct y. inversion H2;subst. clear H2.
  permdes. Qcdes. Qdes.
  unfold perRange in *.
  unfoldlt;simpl in *.
  pose proof Z.ggcd_correct_divisors (z * 1) (Z.pos (z0 * 2)).
  pose proof Z.ggcd_correct_divisors (z) (Z.pos (z0)).
  pose proof Z.gcd_nonneg (z * 1) (Z.pos (z0 * 2)) .
  pose proof Z.ggcd_gcd (z * 1) (Z.pos (z0 * 2)).
  destruct (Z.ggcd (z * 1) (Z.pos (z0 * 2))) as [? [? ?]] eqn:?.
  destruct (Z.ggcd (z) (Z.pos (z0))) as [? [? ?]] eqn:?.
  simpl in *.
  rewrite Z.mul_1_r in *.
  inversion canon. subst z5 z0.
  destruct H0, H. subst z.
  assert (z1 * z2 < (z1 * z3))%Z by lia.
  rewrite Z2Pos.id by lia.
  apply Zmult_gt_0_lt_reg_r  with (p := z1) .
  lia. lia. 
Qed.

Definition join (x y z: t) : Prop := 
  (z.(frac) = (  x.(frac) +ᶜ y.(frac))).

Lemma join_comm : forall x y z, join x y z -> join y x z.
Proof. unfold join; intros. erewrite Qcplus_comm. auto. Qed.
Arguments join_comm [x] [y] [z].

Lemma split_join : forall x y z, split x = (y, z) -> join y z x.
Proof. 
  unfold split,join;intros.
  permdes.
  inversion H;clear H.
  subst.
  apply Qc_is_canon.
  qc_unfold.
  Qcdes. qc_simpl.
  unfold Qinv. simpl.
  lra.
Qed.


Definition minus_compute (x y: t) : Qc :=
  if (Qc_ltb y.(frac) x.(frac)) then ( (x.(frac) -ᶜ y.(frac))%Qc) else 1.

Lemma minus_compute_perRange : forall x y, perRange (minus_compute x y). 
Proof.
  intros. unfold minus_compute, Qc_ltb.
  permdes.
  unfold Qccompare.
  destruct ((y ?= x)%Q) eqn:?.
  - unfold perRange, Qclt. simpl. lra.
  - apply Qlt_alt in Heqc.
    qc_unfold. 
    unfold perRange, Qclt. cbn [this].
    Qcdes. qc_simpl.
    split;lra.
  - unfold perRange, Qclt. simpl. lra.
Qed.


Definition minus (x y: t) : t := mkper (minus_compute x y) (minus_compute_perRange x y).

End Perm.



Notation "x '.(frac)'" := (Perm.frac x)
  (at level 1).


(***********************************************************************************************************)
(* Q arith lemmas *)
Lemma plus_positives_gt0 : forall (x y : Qc), 0 < x -> 0 < y -> 0 < x + y.
Proof. intros. Qcdes. 
       qc_unfold. qc_simpl.
       simpl (Qred _) in *.
       lra.
Qed.

Arguments plus_positives_gt0 [x] [y].

Lemma plus_range_l : forall x y,  Perm.perRange (x + y)  -> 0 < x -> 0 < y -> Perm.perRange x.
Proof. 
  intros.
  unfold Perm.perRange in *.
  qc_unfold.
  Qcdes. qc_simpl. 
  split;try lra.
Qed.
Arguments plus_range_l [x] [y].

Lemma plus_positives_gtself : forall q q0, 0 < q0  ->  q < q +ᶜ q0.
Proof.  intros. qc_unfold. Qcdes. qc_simpl. lra.  Qed.

Lemma lt_refl_false : forall q, ~ q < q .
Proof.  intros. qc_unfold. Qcdes.  lra.  Qed.

Lemma plus_same_eq_same: forall x y z, x +ᶜ y =  z +ᶜ y -> x = z.
Proof.  intros. qc_unfold. Qcdes.
        rewrite Q2Qc_eq_iff in H. apply Qc_is_canon.
        qc_simpl. lra.  Qed.

Lemma perRange_compare : forall x, Perm.perRange x -> (x ?= 1)%Qc <> Gt.
Proof. intros. Qcdes. unfold Perm.perRange in H. qc_unfold.
       qc_simpl. rewrite <- Qle_alt. lra.  Qed.



(***********************************************************************************************************)
(* Perm lemmas *)

Ltac permdes := match goal with
 | q:Perm.t |- _ => let p:= fresh "qc" in
              let rpf0 := fresh "rpf" in destruct q as [q rpf0]; 
              unfold Perm.perRange, Qclt in rpf0; simpl in rpf0;
              permdes
 | |- _ => cbn [Perm.frac] in * end.

Definition Perm_leb := 
fun x y : Perm.t  => Qc_leb (x.(frac)) (y.(frac)).

Definition Perm_ltb := 
fun x y : Perm.t  => Qc_ltb (x.(frac)) (y.(frac)).


Lemma Perm_join_eq_r_false : forall t t0, ~ Perm.join t t0 t0.
Proof. 
  unfold Perm.join;intros. permdes.
  qc_unfold. unfold not;intros.
  assert (t0 == Q2Qc (t + t0)). { rewrite H at 1. reflexivity.  }
  qc_simpl. lra. 
Qed.

Lemma Perm_join_same_eq_same : forall x y z u, Perm.join x y u -> Perm.join z y u -> x = z.
Proof. 
  unfold Perm.join;intros. permdes.
  qc_unfold. unfold not;intros.
  apply Perm.mkper_eq.
  apply Qc_is_canon.
  subst.
  apply Q2Qc_eq_iff in H0.
  qc_simpl. lra. 
Qed.

Arguments  Perm_join_same_eq_same [x] [y] [z] [u].

Lemma Perm_join_full_l_false : forall x y, ~ Perm.join Perm.fullperm x y.
Proof.
  unfold Perm.join, Perm.fullperm;intros. permdes.
  qc_unfold. unfold not;intros.
  assert (y == Q2Qc (1 + x)). { rewrite H at 1. reflexivity.  }
  qc_simpl. lra. 
Qed.


Lemma writable_perm_bool_true : forall p, Perm.writable_perm p <-> Perm.writable_permB p = true.
Proof.
  unfold Perm.writable_perm, Perm.writable_permB;intros. permdes.
  qc_unfold.
  destruct (Qc_eq_dec p 1 );[tauto | ].
  split;intros; congruence.
Qed.

Lemma writable_perm_eq_full : forall p, Perm.writable_perm p <-> p = Perm.fullperm.
Proof.
  unfold Perm.writable_perm, Perm.fullperm;intros. permdes.
  split;intros.
  - apply Perm.mkper_eq.
    auto.
  - inversion H. auto.
Qed.

Lemma  Perm_full_leb_eq: forall t, Perm_leb Perm.fullperm t = true -> t = Perm.fullperm.
Proof. 
  unfold Perm_leb, Perm.fullperm;intros. permdes.
  apply Perm.mkper_eq.
  apply Qc_is_canon.
  Qcdes.
  qc_unfold. qc_simpl.
  destruct (1 ?= q)%Q eqn:?;try congruence.
  - apply Qeq_alt in Heqc. lra.
  - apply Qlt_alt in Heqc. lra.
Qed.

Lemma Perm_leb_refl:  forall x, Perm_leb x x = true.
Proof.
  unfold Perm_leb;intros. permdes.
  qc_unfold. 
  destruct (x ?= x)%Q eqn:?;auto.
  apply Qgt_alt in Heqc. lra.
Qed.

Lemma Perm_ltb_refl:  forall x, Perm_ltb x x = false.
Proof.
  unfold Perm_ltb;intros. permdes.
  qc_unfold. 
  destruct (x ?= x)%Q eqn:?;auto.
  apply Qlt_alt in Heqc. lra.
Qed.

Lemma Perm_leb_ltb : forall t t0, Perm_leb t t0 = true -> Perm_ltb t t0 = true \/ t = t0.
Proof. 
  unfold Perm_leb, Perm_ltb;intros. permdes.
  qc_unfold. 
  destruct (t ?= t0)%Q eqn:?;auto.
  right. apply Perm.mkper_eq.
  apply Qeq_alt in Heqc. apply  Qc_is_canon. auto.
Qed.

Lemma Perm_ltb_leb : forall t t0, Perm_ltb t t0 = true -> Perm_leb t t0 = true.
Proof.
  unfold Perm_leb, Perm_ltb;intros. permdes.
  qc_unfold. 
  destruct (t ?= t0)%Q eqn:?;auto.
Qed.

Lemma Perm_ltb_minus_correct : forall t t0, Perm_ltb t t0 = true -> Perm.join t (Perm.minus t0 t) t0.
Proof. 
  unfold Perm_ltb, Perm.join, Perm.minus, Perm.minus_compute;intros. permdes.
  rewrite H. 
  qc_unfold.
  destruct (t ?= t0)%Q eqn:?; try congruence.
  apply Qlt_alt in Heqc.
  clear H.
  apply Qc_is_canon.
  qc_simpl.
  lra.
Qed.

Lemma Perm_join_ltb_l : forall t t0 t1, Perm.join t t0 t1 -> Perm_ltb t t1 = true.
Proof. 
  unfold Perm_ltb, Perm.join;intros. permdes.
  rewrite H. clear H. 
  qc_unfold.
  destruct ((t ?= Q2Qc (t + t0))%Q) eqn:?; try congruence.
  - apply Qeq_alt in Heqc.
    qc_simpl. lra.
  - apply Qgt_alt in Heqc.
    qc_simpl. lra.
Qed.

Lemma eq_Qeq : forall (x y : Qc), x = y -> x == y.
Proof. intros. subst. reflexivity. Qed.
Arguments eq_Qeq [x] [y].  
Lemma Perm_join_assoc1: forall m1 m2 m3 m23 m123,
  Perm.join m2 m3 m23 ->
  Perm.join m1 m23 m123 ->
  exists m12,
  Perm.join m1 m2 m12 /\ Perm.join m12 m3 m123.
Proof.
  unfold Perm.join;intros. permdes.
  apply eq_Qeq in H, H0.
  assert (Perm.perRange (m1 +ᶜ m2)).
  { unfold Perm.perRange.
    Qcdes. qc_unfold. qc_simpl.
    split;lra.  }
  exists (Perm.mkper (m1 +ᶜ m2) H1).
  split;auto.
  cbn.
  apply Qc_is_canon.
  Qcdes. qc_unfold. qc_simpl.
  lra.
Qed.

Arguments Perm_join_assoc1 [m1] [m2] [m3] [m23] [m123].


