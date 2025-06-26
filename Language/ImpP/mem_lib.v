Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qcanon.
Require Import Lia.

Require Import AUXLib.Axioms.
Require Import AUXLib.Feq.
Require Import AUXLib.ListLib.
From LangLib.ImpP Require Import PermissionModel Mem.


Ltac qc_ca := 
  match goal with 
  | H : ?x == ?y |- _ => apply Qc_is_canon in H; qc_ca 
  | |- _ => idtac end.

Ltac permdes := match goal with
 | q:Perm.t |- _ => let p:= fresh "qc" in destruct q as [q ?]; permdes
 | |- _ => simpl (Perm.frac _ ) in *; unfold Perm.perRange in *  end.

Lemma single_mem_get_eq : forall x v, (single_mem x v) x = Some v.
Proof.  unfold single_mem;intros. rewrite addr_eqb_refl. reflexivity. Qed.

Lemma single_mem_get_neq : forall x v y,  x <> y -> (single_mem x v) y = None.
Proof. unfold single_mem;intros.
    destruct (addr_eqb y x) eqn:?;auto.
    rewrite addr_eqb_eq in Heqb.
    congruence. Qed.

Lemma mem_join_emp : mem_join empty_mem empty_mem empty_mem.
Proof. unfold mem_join, empty_mem;intros;auto. Qed.

Lemma mem_empty_IS_empty_mem' : forall m, mem_empty m -> m = empty_mem.
Proof.
  intros. apply fun_ext1;eapply mem_empty_IS_empty_mem;eauto. Qed.

Lemma mem_join_emp_l: forall m m1, mem_join empty_mem m m1 -> m1 = m.
Proof.
  unfold mem_join, empty_mem;intros.
  apply fun_ext1. intros.
  specialize (H a).
  destruct (m1 a) eqn:? ; destruct (m a) eqn:?;auto; my_destruct H.
  congruence.
Qed.

Lemma mem_join_emp_r: forall m m1, mem_join m empty_mem m1 -> m1 = m.
Proof.
  unfold mem_join, empty_mem;intros.
  apply fun_ext1. intros.
  specialize (H a).
  destruct (m1 a) eqn:? ; destruct (m a) eqn:?;auto; my_destruct H.
  congruence.
Qed.

Lemma mem_join_emp1 : forall m,
  mem_join empty_mem m m.
Proof.
  intros. unfold mem_join.
  intros. destruct (m p) eqn:?.
  - right; left. exists m0. auto.
  - left. auto.
Qed.

Lemma mem_join_emp2 : forall m,
  mem_join m empty_mem m.
Proof.
  intros. unfold mem_join.
  intros. destruct (m p) eqn:?.
  - right; right. left. exists m0. auto.
  - left. auto.
Qed.


Lemma mem_join_eq_inv1 : forall m1 m1' m2 m2' m m',
  f_eq m2 m2' ->
  f_eq m m' ->
  mem_join m1 m2 m ->
  mem_join m1' m2' m' ->
  f_eq m1 m1'.
Proof.
  unfold mem_join, f_eq.
  intros. rename x into p.
  specialize (H p). specialize (H0 p).
  specialize (H1 p);specialize (H2 p).
  my_destruct H1;my_destruct H2; try congruence;
  repeat progress match goal with 
  | H: Perm.join ?t ?t0 ?t0 |- _ => apply Perm_join_eq_r_false in H;contradiction
  | H: (?t, ?i) = (?t0, ?i0) |- _ => inversion H;subst;clear H
  | H: ?m p = ?m0 p, H0: ?m p = Some ?b, H1: ?m0 p = Some ?b0 
    |- _ => rewrite H0, H1 in H; inversion H;clear H; subst
  end.
  pose proof Perm_join_same_eq_same H1 H2.
  subst.
  congruence.
Qed.

Lemma mem_join_eq_inv2 : forall m1 m1' m2 m2' m m',
  f_eq m1 m1' ->
  f_eq m m' ->
  mem_join m1 m2 m ->
  mem_join m1' m2' m' ->
  f_eq m2 m2'.
Proof.
  intros.
  apply mem_join_comm in H1.
  apply mem_join_comm in H2.
  eapply (mem_join_eq_inv1 m2 m2'  m1 m1');eauto.
Qed.

Lemma mem_join_None1 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m1 p = None ->
  m p = m2 p.
Proof.
  intros. unfold mem_join in H.
  specialize (H p);my_destruct H;congruence.
Qed.

Arguments mem_join_None1 [m1] [m2] [m].

Lemma mem_join_None2 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m2 p = None ->
  m p = m1 p.
Proof.
  intros. unfold mem_join in H.
  specialize (H p);my_destruct H;congruence.
Qed.

Arguments mem_join_None2 [m1] [m2] [m].

Lemma mem_join_None3 : forall m1 m2 m p,
  mem_join m1 m2 m ->
  m p = None ->
  m1 p = None /\ m2 p = None.
Proof.
  intros. unfold mem_join in H.
  specialize (H p);my_destruct H;
  split; congruence.
Qed.

Arguments mem_join_None3 [m1] [m2] [m].

Lemma mem_join_Some1 : forall m1 m2 m p v t,
  mem_join m1 m2 m ->
  m1 p = Some (v, t)->
  exists t0, m p = Some (v, t0) /\ Perm_leb t t0 = true.
Proof.
  intros. unfold mem_join in H.
  specialize (H p);my_destruct H;
  try (congruence).
  - rewrite H in H0. inversion H0. subst b.
    exists t. split;eauto.
    apply Perm_leb_refl.
  - rewrite H1 in H0. inversion H0; subst v0 t0.
    exists t2.
    split;auto.
    apply Perm_ltb_leb.
    eapply Perm_join_ltb_l;eauto.
Qed.

Lemma mem_join_Some2 : forall m1 m2 m p v t,
  mem_join m1 m2 m ->
  m2 p = Some  (v, t) ->
  exists t0, m p = Some (v, t0) /\ Perm_leb t t0 = true.
Proof.
  intros.
  apply mem_join_comm in H.
  eapply mem_join_Some1;eauto.
Qed.

Lemma mem_join_Some3 : forall m1 m2 m p n,
  mem_join m1 m2 m ->
  m p = Some n ->
  (m1 p = Some n /\ m2 p = None) \/ (m1 p = None /\ m2 p = Some n) \/ 
  (exists t t0,  Perm.join t t0 (snd n) /\ m1 p = Some (fst n, t) /\ m2 p = Some (fst n, t0) ).
Proof.
  intros. destruct n.
  unfold mem_join in H.
  specialize (H p);my_destruct H.
  - congruence.
  - right. left; split; congruence.
  - left. split; congruence.
  - right. right. simpl.
    rewrite H3 in H0;inversion H0. subst. 
    exists t0, t1.
    splits;auto. 
Qed.
 

Lemma mem_join_eq:
  forall m1  m2 m m' : addr -> option memblock,
  mem_join m1 m2 m -> mem_join m1 m2 m' -> m = m'.
Proof.
  unfold mem_join;intros.
  apply fun_ext1. intros.
  specialize (H a).
  specialize (H0 a).
  destruct (m1 a) eqn:? ; destruct (m2 a) eqn:?;auto; my_destruct H;my_destruct H0.
  all: try congruence.
  rewrite H1 in H4. rewrite H2 in H5.
  inversion H4;inversion H5;subst t2 t3 v0;clear H4 H5.
  unfold Perm.join in *.
  qc_ca.
  assert (t1 = t4).
  {
  destruct t1 as [q ?];destruct t4 as [q0 ?].
  apply Perm.mkper_eq. simpl (Perm.frac _) in *. congruence. }
  subst.
  congruence.
Qed.

Arguments mem_join_eq [m1] [m2] [m] [m'].


Lemma mem_join_eq_l:
  forall m1 m1' m2 m : addr -> option memblock,
  mem_join m1 m2 m -> mem_join m1' m2 m -> m1 = m1'.
Proof.
  intros.
  apply fun_ext1.
  eapply (mem_join_eq_inv1 m1 m1' m2 m2 m m);eauto.
  apply f_eq_refl.
  apply f_eq_refl.
Qed.

Arguments mem_join_eq_l [m1] [m1'] [m2] [m].

Lemma mem_join_eq_r:
  forall m1 m2 m2' m : addr -> option memblock,
  mem_join m1 m2 m -> mem_join m1 m2' m -> m2 = m2'.
Proof.
  intros.
  apply fun_ext1.
  eapply (mem_join_eq_inv1 m2 m2' m1 m1 m m);eauto.
  apply f_eq_refl.
  apply f_eq_refl.
  apply mem_join_comm;auto.
  apply mem_join_comm;auto.
Qed.

Arguments mem_join_eq_r [m1] [m2] [m2'] [m].

Lemma mem_join_Some_eq_l : forall m1 m2 m3 x v1 v2,
  mem_join m1 m2 m3 ->
  m1 x = Some v1 ->
  m3 x = Some v2 ->
  fst v2 = fst v1.
Proof.
  unfold mem_join; intros.
  specialize (H x).
  my_destruct H;try congruence.
  rewrite H2 in H0;inversion H0;subst.
  rewrite H4 in H1;inversion H1;subst.
  simpl. reflexivity.
Qed.

Arguments mem_join_Some_eq_l [m1] [m2] [m3] [x] [v1] [v2].

Lemma mem_join_Some_eq_r : forall m1 m2 m3 x v1 v2,
  mem_join m1 m2 m3 ->
  m2 x = Some v1 ->
  m3 x = Some v2 ->
  fst v2 = fst v1.
Proof.
  unfold mem_join; intros.
  specialize (H x).
  my_destruct H;try congruence.
  rewrite H3 in H0;inversion H0;subst.
  rewrite H4 in H1;inversion H1;subst.
  simpl. reflexivity.
Qed.

Arguments mem_join_Some_eq_r [m1] [m2] [m3] [x] [v1] [v2].

Lemma mem_join_None: forall m1 m2 m3 x,
  mem_join m1 m2 m3 ->
  m3 x = None ->
  m1 x = None /\ m2 x = None.
Proof.
  unfold mem_join;intros.
  specialize (H x).
  my_destruct H;try congruence.
  tauto.
Qed.

Arguments mem_join_None [m1] [m2] [m3] [x].



Definition canjoin (m1 m2:mem)  :=
  forall (x : addr),
    match m1 x, m2 x with
    |  Some _, None => True
    |  None , Some  _ => True
    |  None, None => True
    |  Some (i,t), Some (i0,t0)=> i = i0 /\ exists t1, Perm.join t t0 t1
    end.


Definition minus (m1 m2: mem) : mem := 
  fun (a : addr) =>
  match (m1 a, m2 a) with
  | (Some (i,t), Some (i0,t0)) => if Perm_ltb t0 t then Some (i, Perm.minus t t0)  else None 
  | (Some b1, None) => Some b1
  | (None, Some b2) => None
  | (None, None) => None
  end.

Definition sub (m1 m2: mem) : Prop := 
  forall (x : addr) y t, m1 x = Some (y, t) -> exists t0,  m2 x = Some (y, t0) /\ Perm_leb t t0  = true.

Lemma mem_get_single_mem_sub : forall m x v, m x = Some v -> sub (single_mem x v) m.
Proof.
  unfold sub,single_mem;intros.
  destruct (addr_eqb x0 x) eqn:?.
  - rewrite addr_eqb_eq in Heqb.
    subst.
    destruct v.
    inversion H0. subst.
    exists t.
    split;auto.
    apply Perm_leb_refl.
  - discriminate.
Qed.

Arguments mem_get_single_mem_sub [m] [x] [v].

Lemma  value_eqb_refl: forall v, value_eqb v v = true .
Proof.
  intros [? [ | ] ];
  unfold value_eqb;
  rewrite Z.eqb_refl;auto. 
Qed.


Lemma Perm_join_bjoin : forall i t t0 t1, Perm.join t t0 t1 -> bjoin (i, t) (i, t0) = Some (i, t1).
Proof. 
  unfold Perm.join, bjoin; intros.
  permdes.
  qc_ca.
  rewrite value_eqb_refl.
  pose proof rpf.
  apply perRange_compare in H0. 
  subst t1.
  assert (Perm_add_aux {| Perm.frac := t; Perm.rpf := rpf1 |}
  {| Perm.frac := t0; Perm.rpf := rpf0 |} = t +ᶜ t0).
 { unfold Perm_add_aux;simpl; destruct ((t +ᶜ t0 ?= 1)) eqn:?;try contradiction;
   reflexivity. }
  erewrite (Perm.mkper_eq _ _ _ rpf H).
  destruct ((t +ᶜ t0 ?= 1)) eqn:?;try contradiction;reflexivity.
Qed.
       

Lemma canjoin_merge_mem_join : forall m1 m2, canjoin m1 m2 -> mem_join m1 m2 (merge m1 m2).
Proof.
  unfold canjoin, mem_join, merge;intros.
  specialize (H p).
  destruct (m1 p), (m2 p);try contradiction;auto.
  - right;right. right.
    destruct m, m0.
    my_destruct H.
    subst.
    do 4 eexists.
    splits;eauto.
    apply Perm_join_bjoin;auto.
  - right. right. left. eexists;eauto.
  - right;left. eexists;eauto.
Qed. 

Arguments canjoin_merge_mem_join [m1] [m2].

Lemma sub_minus_mem_join : forall m1 m2, sub m1 m2 -> mem_join m1 (minus m2 m1) m2.
Proof.
  unfold sub, mem_join, minus;intros.
  specialize (H p).
  destruct (m1 p) eqn:?.
  + destruct m.
    specialize (H v t (ltac:(reflexivity))) as [? [? ?]].
    rewrite H.
    right;right.
    apply Perm_leb_ltb in H0 as [? | ?].
    - rewrite H0;right.
      exists t, (Perm.minus x t), x, v.
      splits;auto.
      apply Perm_ltb_minus_correct;auto.
    - subst;left.
      rewrite Perm_ltb_refl.
      exists (v, x). auto.
  + destruct (m2 p);auto.
    destruct m.
    right;left. eexists. eauto.
Qed.

Arguments sub_minus_mem_join [m1] [m2].

Lemma mem_join_sub_l : forall m1 m2 m,  mem_join m1 m2 m -> sub m1 m.
Proof.
  unfold sub, mem_join;intros.
  specialize (H x).
  rewrite H0 in *.
  my_destruct H;try congruence.
  - inversion H. subst b. eexists. splits;eauto.
    apply Perm_leb_refl.
  - inversion H1;subst.
    eexists.
    splits;eauto.
    apply Perm_ltb_leb.
    eapply Perm_join_ltb_l;eauto.
Qed.

Arguments mem_join_sub_l [m1] [m2] [m].


Lemma mem_join_canjoin : forall m1 m2 m3, mem_join m1 m2 m3 -> canjoin m1 m2.
Proof.
  unfold mem_join, canjoin;intros.
  specialize (H x).
  my_destruct H;try rewrite H;try rewrite H0; try rewrite H1; auto.
  destruct b;auto.
  split;auto.
  eexists. eauto. 
Qed.

Arguments mem_join_canjoin [m1] [m2] [m3].

Lemma mem_join_eqmerge : forall m1 m2 m3, mem_join m1 m2 m3 -> m3 = merge m1 m2.
Proof.
  intros.
  eapply mem_join_eq;eauto.
  eapply canjoin_merge_mem_join.
  eapply mem_join_canjoin;eauto.
Qed.

Arguments mem_join_eqmerge [m1] [m2] [m3].


Ltac solve_empmem :=
  repeat match goal with
  | H: mem_empty ?m |- _ => apply mem_empty_IS_empty_mem' in H; subst m
  | H: mem_join _ empty_mem _ |- _ => apply mem_join_emp_r in H;subst 
  | H: mem_join empty_mem _ _ |- _ => apply mem_join_emp_l in H;subst
  | |- mem_join _ _ empty_mem => apply mem_join_emp
  | |- mem_join ?x _ ?x => apply mem_join_emp2
  | |- mem_join _ ?x ?x => apply mem_join_emp1
  | |- mem_join _ empty_mem ?x => apply mem_join_emp2
  | |- mem_join empty_mem _ ?x => apply mem_join_emp1
  | |- mem_empty _ => apply empty_mem_empty 
  end.



Lemma mem_join_assoc1: forall m1 m2 m3 m23 m123,
  mem_join m2 m3 m23 ->
  mem_join m1 m23 m123 ->
  exists m12,
  mem_join m1 m2 m12 /\ mem_join m12 m3 m123.
Proof.
  unfold mem_join. intros.
  exists (merge m1 m2).
  split; intros.
  - unfold merge.
    specialize (H p); specialize (H0 p);my_destruct H; my_destruct H0; 
    match goal with 
    | H: m1 p = _, H0: m2 p = _ |- _ => rewrite H, H0 end;
    try (tauto || congruence || solve [right;left;eexists;eauto]  || 
    solve [right;right;left; eexists;eauto]).
    + right;right;right.
      rewrite H2 in H4. inversion H4;subst b.
      exists t, t0, t1, v.
      splits;auto.
      apply Perm_join_bjoin;auto.
    + right;right;right.
      rewrite H3 in H5. inversion H5;subst v0 t3.
      pose proof Perm_join_assoc1 H H0 as [? [? ?]]. 
      exists t2, t, x, v.
      splits;auto.
      apply Perm_join_bjoin;auto.
  - unfold merge.
    specialize (H p); specialize (H0 p);my_destruct H; my_destruct H0; 
    match goal with 
    | H: m1 p = _, H0: m2 p = _ |- _ => rewrite H, H0 end;
    try match goal with 
    | H: m23 p = Some ?b, H0: m23 p = Some ?b0 |- _ => rewrite H in H0; inversion H0;subst end;
    match goal with 
    | H: m3 p = _, H0: m123 p = _ |- _ => rewrite H, H0  end;
    try (tauto || congruence || solve [right;left;eexists;eauto]  || 
    solve [right;right;left; eexists;eauto]).
    + right;right;right.
      exists t, t0, t1, v.
      splits;auto.
    + right;right;left.
      eexists;splits;eauto.
      apply Perm_join_bjoin;auto.
    + right;right;right.
      exists t, t0, t1, v.
      splits;auto.
    + right;right;right.
      pose proof Perm_join_assoc1 H H0 as [? [? ?]]. 
      exists  x, t0, t4, v0.
      splits;auto.
      apply Perm_join_bjoin;auto.
Qed.

Arguments mem_join_assoc1 [m1] [m2] [m3] [m23] [m123].

Lemma mem_join_assoc2: forall m1 m2 m3 m12 m123,
  mem_join m1 m2 m12 ->
  mem_join m12 m3 m123 ->
  exists m23,
  mem_join m2 m3 m23 /\ mem_join m1 m23 m123.
Proof.
  intros. apply mem_join_comm in H. apply mem_join_comm in H0.
  pose proof (mem_join_assoc1 H H0).
  destruct H1 as [m23 [? ?] ].
  apply mem_join_comm in H1. apply mem_join_comm in H2.
  exists m23. auto.
Qed.

Arguments mem_join_assoc2 [m1] [m2] [m3] [m12] [m123].


Definition writable_m (m : mem) (x: addr) := match m x with | None => False | Some (i, p) => Perm.writable_perm p end.

Lemma mem_update_eq : forall m x v, 
    writable_m m x ->
    (mem_update m x v) x = Some (v, Perm.fullperm). 
Proof.
  unfold writable_m,  mem_update, mem_update';intros.
  destruct (m x) eqn:?;[ | contradiction].
  destruct m0.
  apply writable_perm_eq_full in H as ?.
  apply writable_perm_bool_true in H.
  rewrite H. subst.
  rewrite addr_eqb_refl. auto. 
Qed.

Lemma mem_update_Neq : forall m x v x', 
  writable_m m x ->
  x' <> x -> (mem_update m x v) x' = m x'. 
Proof.
  unfold writable_m,  mem_update, mem_update';intros.
  destruct (m x) eqn:?;[ | contradiction].
  destruct m0.
  apply writable_perm_bool_true in H.
  rewrite H.
  apply addr_eqb_neq in H0.
  rewrite H0.
  auto.
Qed.

Lemma mem_update_single_eq : forall x v v0, 
  Perm.writable_perm (snd v) ->
  (mem_update (single_mem x v) x v0) = single_mem x (v0, Perm.fullperm). 
Proof.
  unfold mem_update,mem_update', single_mem;intros.
  apply fun_ext1. intro.
  destruct v. simpl in *.
  rewrite addr_eqb_refl.
  apply writable_perm_eq_full in H as ?.
  subst t.
  apply writable_perm_bool_true in H.
  rewrite H. 
  destruct (addr_eqb a x);auto.
Qed.
  
Lemma mem_update_unfold : forall m m' x v v0, 
  writable_m m x -> m x = Some v ->
  writable_m m' x -> m' x = Some v0 ->
  (forall p' : Z, p' <> x -> m p' = m' p') -> m' = mem_update m x (fst v0).
Proof.
  unfold mem_update;intros.
  apply fun_ext1.
  intro.
  destruct v, v0.
  unfold writable_m in *.
  rewrite ?H0, ?H2 in *.
  apply writable_perm_eq_full in H as ?.
  apply writable_perm_eq_full in H1 as ?.
  subst t t0.
  apply writable_perm_bool_true in H.
  unfold mem_update'; rewrite H0, H;simpl.
  destruct (addr_eqb a x) eqn:?.
  - apply addr_eqb_eq in Heqb. subst.
    rewrite H2. auto.
  - apply addr_eqb_neq in Heqb. 
    erewrite H3;eauto.
Qed.

Lemma mem_join_mem_update_l : forall m1 m2 m3 x v, mem_join m1 m2 m3 -> 
  writable_m m1 x -> mem_join (mem_update m1 x v) m2 (mem_update m3 x v).
Proof.
  unfold mem_update, mem_update', writable_m;intros.
  destruct (m1 x ) as [[? ?] | ]eqn:?;[ | contradiction].
  apply writable_perm_eq_full in H0 as ?.
  apply writable_perm_bool_true in H0 .
  pose proof mem_join_Some1  _ _ _ _ _ _ H Heqo as [? [? ?]].
  subst t.
  apply Perm_full_leb_eq in H3.
  subst x0.
  rewrite H2,H0.
  unfold mem_join in *.
  intros p.
  specialize (H p).
  my_destruct H.
  - left. 
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb.
    subst p. congruence.
  - right;left.
    exists b.
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb0.
    subst p.
    congruence.
  - right;right;left.
    destruct (addr_eqb p x) eqn:?.
    + exists (v, Perm.fullperm).
      apply addr_eqb_eq in Heqb0.
      subst p.
      rewrite H in Heqo.
      inversion Heqo. subst b.
      auto.
    + exists b.
      auto.
  - right;right;right.
    destruct (addr_eqb p x) eqn:?.
    + exfalso.
      apply addr_eqb_eq in Heqb.
      subst p.
      rewrite H1 in Heqo.
      inversion Heqo.
      subst.
      apply Perm_join_full_l_false in H.
      auto.
    + exists t, t0, t1, v1.
      splits;auto.
Qed. 

Lemma mem_join_update_None1 : forall m1 m1' m2 m m' p,
  mem_join m1 m2 m ->
  m p = None ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_None3 _ H H0). destruct H4.
    destruct (m1' p).
    + right. right. left. exists m0. tauto.
    + left. tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    specialize (H p0).
    my_destruct H.
    + left. repeat split; congruence.
    + right. left. exists b. repeat split; congruence.
    + right. right. left. exists b. repeat split; congruence.
    + right. right. right. exists t, t0, t1, v. splits;congruence.
Qed.

Lemma mem_add_N_notin : forall m p v tl n p',
  (p' < p \/ p' >= p + Z.of_nat n)%Z ->
  mem_add_N m p v tl n p' = m p'.
Proof.
  unfold mem_add_N.
  intros. generalize dependent p. revert tl.
  induction n, tl; intros; simpl in *.
  - auto.
  - auto.
  - auto. 
  - unfold mem_add. addr_destruct p' p.
    + subst. lia.
    + apply IHn. lia.
Qed.

Lemma mem_add_N_in : forall m p v tl n p',
  (p' >= p)%Z->
  (p' < p + Z.of_nat n)%Z -> (length tl >= n)%nat ->
  mem_add_N m p v tl n p' = Some ((v, Znth (p' - p) tl vint), Perm.fullperm).
Proof.
  unfold mem_add_N.
  intros. generalize dependent p. revert tl H1.
  induction n, tl; intros; simpl in *.
  - lia.
  - lia.
  - lia.
  - unfold mem_add. addr_destruct p' p.
    + replace (p' - p)%Z with (0%Z) by lia.
      rewrite Znth0_cons. auto.
    + erewrite IHn by lia;eauto. 
      rewrite Znth_cons by lia. 
      replace (p' - (p + 1))%Z with (p' - p - 1)%Z by lia.
      auto.
Qed.

Lemma mem_join_add_range : forall m1 m1' m2 m m' p1 p2,
  mem_join m1 m2 m ->
  (forall p, (p >= p1)%Z -> (p < p2)%Z -> m p = None) ->
  (forall p, (p >= p1)%Z -> (p < p2)%Z -> m1' p = m' p) ->
  (forall p, (p < p1 \/ p >= p2)%Z -> m1 p = m1' p) ->
  (forall p, (p < p1 \/ p >= p2)%Z -> m p = m' p) ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join in *. intros p.
  assert ((p >= p1 /\ p < p2) \/ (p < p1 \/ p >= p2))%Z as HR by lia.
  destruct HR as [ [HR1 HR2] | HR].
  - specialize (H0 p HR1 HR2). specialize (H1 p HR1 HR2).
    specialize (H p).
    my_destruct H;try congruence.
    destruct (m' p) eqn:?.
    * right; right. left.  exists m0. tauto.
    * left. tauto.
  - specialize (H2 p HR). specialize (H3 p HR).
    specialize (H p).
    my_destruct H;try congruence.
    + left. repeat split; congruence.
    + right; left. exists b. repeat split; congruence.
    + right; right; left. exists b. repeat split; congruence.
    + right;right;right. exists t, t0, t1, v. splits;congruence.
Qed.

Lemma mem_join_two_single : forall pm1 pm2 pm, 
  Perm.join pm1 pm2 pm ->
  forall p vi,
  mem_join (single_mem p (vi, pm1)) (single_mem p (vi, pm2)) (single_mem p (vi, pm)).
Proof.
  unfold mem_join, single_mem;intros.
  destruct (addr_eqb p0 p);[ |auto].
  right;right;right.
  do 4 eexists.
  splits;eauto.
Qed.

Arguments mem_join_two_single [pm1] [pm2] [pm].

Lemma mem_join_single_mem_remove_l : forall m p v m1, 
  Perm.writable_perm (snd v) -> 
  mem_join m (single_mem p v) m1 -> m = (mem_remove m1 p ).
Proof.
  unfold mem_remove, mem_remove';intros.
  apply fun_ext1;intros.
  destruct v.
  simpl in *.
  pose proof mem_join_Some2 _ _ _ _ _ _ H0 (single_mem_get_eq p (v, t)) as [? [? ?]].
  apply writable_perm_eq_full in H as ?.
  subst t.
  apply writable_perm_bool_true in H.
  apply Perm_full_leb_eq in H2.
  subst x.
  rewrite H1, H.
  destruct (addr_eqb a p) eqn:?.
  - apply addr_eqb_eq in Heqb.
    subst p.
    specialize (H0 a).
    my_destruct H0;try congruence.
    + rewrite single_mem_get_eq in H2.
      congruence.
    + rewrite single_mem_get_eq in H3.
      inversion H3;subst.
      apply Perm.join_comm in H0.
      apply Perm_join_full_l_false in H0.
      contradiction.
  - apply addr_eqb_neq in Heqb.
    pose proof single_mem_get_neq p (v, Perm.fullperm) a (ltac:(congruence)).
    specialize (H0 a).
    my_destruct H0;try congruence.
Qed. 

Arguments  mem_join_single_mem_remove_l [m] [p] [v] [m1].

Lemma mem_remove_eq : forall m x,
 mem_remove m x x = None.
Proof.
  unfold mem_remove, mem_remove';intros.
  destruct (m x) as [[? ?] | ] eqn:?;auto.
  destruct (Perm.writable_permB t);auto.
  rewrite addr_eqb_refl. auto. Qed.

Lemma mem_remove_neq : forall m x x', writable_m m x -> x' <> x -> mem_remove m x x' = m x'.
Proof.
  unfold mem_remove,mem_remove', writable_m ;intros.
  destruct (m x) as [[? ?] | ] eqn:?;[ | contradiction].
  apply writable_perm_bool_true in H.
  rewrite H.
  apply addr_eqb_neq in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma mem_remove_unfold : forall m m' x , m' x = None -> writable_m m x -> 
  (forall p' : Z, p' <> x -> m p' = m' p') -> m' = mem_remove m x.
Proof.
  unfold mem_remove,mem_remove', writable_m ;intros.
  apply fun_ext1. intros.
  destruct (m x) as [[? ?] | ] eqn:?;[ | contradiction].
  apply writable_perm_bool_true in H0.
  rewrite H0.
  destruct (addr_eqb a x) eqn:?.
  - apply addr_eqb_eq in Heqb. subst. auto.
  - apply addr_eqb_neq in Heqb. erewrite H1;eauto.
Qed.

Lemma mem_join_mem_remove_l : forall m1 m2 m3 x, 
  mem_join m1 m2 m3 -> writable_m m1 x -> mem_join (mem_remove m1 x) m2 (mem_remove m3 x).
Proof.
  unfold mem_remove, mem_remove', writable_m;intros.
  destruct (m1 x) as [[? ?] | ] eqn:?;[ | contradiction].
  pose proof mem_join_Some1 _ _ _ _ _ _ H Heqo as [? [? ?]].
  apply writable_perm_eq_full in H0 as ?. subst t.
  apply Perm_full_leb_eq in H2. subst x0.
  apply writable_perm_bool_true in H0.
  rewrite H1, H0.
  unfold mem_join in *.
  intros p.
  specialize (H p).
  my_destruct H.
  - left.
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb.
    subst p.
    congruence.
  - right;left.
    exists b.
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb0.
    subst p.
    congruence.
  - destruct (addr_eqb p x) eqn:?.
    + left.
      auto.
    + right;right. left. exists b.
      auto.
  - destruct (addr_eqb p x) eqn:?.
    + exfalso.
      apply addr_eqb_eq in Heqb.
      subst p.
      rewrite H2 in Heqo.
      inversion Heqo. subst.
      apply Perm_join_full_l_false in H.
      auto.
    + right. right. right.
      exists t,t0,t1,v0.
      splits;auto. 
Qed. 



(*
Lemma mem_join_mem_update_l' : forall m1 m2 m3 x v, mem_join m1 m2 m3 -> m3 x= None -> mem_join (mem_update m1 x v) m2 (mem_update m3 x v).
Proof.
  unfold mem_join,mem_update;intros.
  specialize (H p).
  my_destruct H.
  - 
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb.
    subst p.
    right;right.
    eexists;eauto.
  - right;left.
    exists i.
    destruct (addr_eqb p x) eqn:?;[ | auto].
    apply addr_eqb_eq in Heqb.
    subst p.
    congruence.
  - right;right.
    destruct (addr_eqb p x) eqn:?.
    + exists v.
      auto.
    + exists i.
      auto.
Qed. 

Lemma mem_join_single_mem_update_l : forall m p v, m p = None -> mem_join m (single_mem p v) (mem_update m p v).
Proof.
  unfold mem_join, single_mem, mem_update;intros.
  destruct (addr_eqb p0 p) eqn:?.
  -  apply addr_eqb_eq in Heqb.
  subst p.
  right;left.
  eexists.
  eauto.
  - destruct (m p0) eqn: ?.
    right;right.
    eexists;eauto.
    auto.
Qed. 



Lemma mem_join_update1 : forall m1 m1' m2 m m' p n0,
  mem_join m1 m2 m ->
  m1 p = Some n0 ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_Some1 _ _ _ _ _ H H0). destruct H4.
    destruct (m1' p).
    + right. right. exists i. tauto.
    + left. tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    destruct (H p0) as [ [? [? ?] ] | [ [n' [? [? ?] ] ] | [n' [? [? ?] ] ] ] ].
    + left. repeat split; congruence.
    + right. left. exists n'. repeat split; congruence.
    + right. right. exists n'. repeat split; congruence.
Qed.

Lemma mem_join_update_None1 : forall m1 m1' m2 m m' p,
  mem_join m1 m2 m ->
  m p = None ->
  (forall p', p' <> p -> m1 p' = m1' p') ->
  m' p = m1' p ->
  (forall p', p' <> p -> m p' = m' p') ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join. intros.
  addr_destruct p0 p.
  - subst. pose proof (mem_join_None3 _ H H0). destruct H4.
    destruct (m1' p).
    + right. right. exists i. tauto.
    + left. tauto.
  - specialize (H1 _ E). specialize (H3 _ E).
    destruct (H p0) as [ [? [? ?] ] | [ [n' [? [? ?] ] ] | [n' [? [? ?] ] ] ] ].
    + left. repeat split; congruence.
    + right. left. exists n'. repeat split; congruence.
    + right. right. exists n'. repeat split; congruence.
Qed.

Lemma mem_join_update_list : forall m1 m1' m2 m m' ps,
  mem_join m1 m2 m ->
  (forall p, In p ps -> m p = None) ->
  (forall p, In p ps -> m1' p = m' p) ->
  (forall p, ~ In p ps -> m1 p = m1' p) ->
  (forall p, ~ In p ps -> m p = m' p) ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join in *. intros p.
  destruct (in_dec addr_dec p ps) as [HIN | HIN].
  - specialize (H0 p HIN). specialize (H1 p HIN).
    destruct (H p) as [ [? [? ?] ] | [ [n [? [? ?] ] ] | [n [? [? ?] ] ] ] ];
    try congruence.
    + rewrite H5. rewrite H1.
      destruct (m' p).
      * right; right. exists i. tauto.
      * left. tauto.
  - specialize (H2 p HIN). specialize (H3 p HIN).
    destruct (H p) as [ [? [? ?] ] | [ [n [? [? ?] ] ] | [n [? [? ?] ] ] ] ].
    + left. repeat split; congruence.
    + right; left. exists n. repeat split; congruence.
    + right; right. exists n. repeat split; congruence.
Qed.

Lemma mem_join_update_range : forall m1 m1' m2 m m' p1 p2,
  mem_join m1 m2 m ->
  (forall p, p >= p1 -> p < p2 -> m p = None) ->
  (forall p, p >= p1 -> p < p2 -> m1' p = m' p) ->
  (forall p, (p < p1 \/ p >= p2) -> m1 p = m1' p) ->
  (forall p, (p < p1 \/ p >= p2) -> m p = m' p) ->
  mem_join m1' m2 m'.
Proof.
  intros. unfold mem_join in *. intros p.
  assert ((p >= p1 /\ p < p2) \/ (p < p1 \/ p >= p2)) as HR by lia.
  destruct HR as [ [HR1 HR2] | HR].
  - specialize (H0 p HR1 HR2). specialize (H1 p HR1 HR2).
    destruct (H p) as [ [? [? ?] ] | [ [n [? [? ?] ] ] | [n [? [? ?] ] ] ] ];
    try congruence.
    + rewrite H5. rewrite H1.
      destruct (m' p).
      * right; right. exists i. tauto.
      * left. tauto.
  - specialize (H2 p HR). specialize (H3 p HR).
    destruct (H p) as [ [? [? ?] ] | [ [n [? [? ?] ] ] | [n [? [? ?] ] ] ] ].
    + left. repeat split; congruence.
    + right; left. exists n. repeat split; congruence.
    + right; right. exists n. repeat split; congruence.
Qed.

Lemma mem_add_N_in : forall m p v n p',
  p' >= p ->
  p' < p + n ->
  mem_add_N m p v n p' = Some v.
Proof.
  unfold mem_add_N.
  intros. generalize dependent p.
  induction n; intros; simpl in *.
  - lia.
  - unfold mem_update. addr_destruct p' p; auto.
    apply IHn; lia.
Qed.
 *)
