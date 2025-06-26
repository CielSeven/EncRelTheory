Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.Morphisms.
Require Import Permutation.

From Coq Require Import Relations.
From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap ListLib GraphLib.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ArrayLib ImpTactics ImpHoareTactics ImpEHoareTactics.

Import SetsNotation.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope Z.

Lemma prop_equiv1 {X:Type} {P Q R: X -> Prop}:
(forall e:X, P e <-> Q e) ->
(forall e:X, Q e <-> R e) -> (forall e:X, P e <-> R e).
Proof.
intros.
split;intro.
- apply H0. apply H. auto.
- apply H. apply H0. auto.
Qed.

Lemma prop_equiv2 {X:Type} {P Q R: X -> Prop}:
(forall e:X, P e <-> Q e) ->
(forall e:X, P e <-> R e) -> (forall e:X, Q e <-> R e).
Proof.
intros.
split;intro.
- apply H0. apply H. auto.
- apply H. apply H0. auto.
Qed.

Lemma prop_equiv3 {X:Type} {P Q R: X -> Prop}:
(forall e:X, Q e <-> P e) ->
(forall e:X, R e <-> P e) -> (forall e:X, Q e <-> R e).
Proof.
intros.
split;intro.
- apply H0. apply H. auto.
- apply H. apply H0. auto.
Qed.

Lemma prop_equiv4 {X:Type} {P Q R: X -> Prop}:
(forall e:X, P e <-> Q e) ->
(forall e:X, P e <-> R e) -> (forall e:X, R e <-> Q e).
Proof.
intros.
split;intro.
- apply H. apply H0. auto.
- apply H0. apply H. auto.
Qed.

Lemma hd_app {X:Type}: forall s1 s2 (z:X), (hd (hd z s2) s1 = hd z (s1 ++ s2)).
Proof.
intros.
destruct s1;simpl;auto.
Qed.

Lemma StronglySorted_sublist {E:Type}: forall Eorder es1 (e:E) es2,
StronglySorted Eorder (es1++e::es2) ->
forall e', In e' es2 -> Eorder e e'.
Proof.
intros.
induction es1.
- rewrite app_nil_l in H. inversion H;subst.
  pose proof (proj1 (Forall_forall (Eorder e) es2) H4).
  apply H1. auto.
- apply IHes1. rewrite <- app_comm_cons in H.
  inversion H;subst. apply H3.
Qed.


Lemma NoDup_Permutation_1: forall X l1 l2 (x:X), NoDup (l1 ++ x::l2) <-> NoDup (x::l1++l2).
Proof.
intros. split;intro.
- econstructor.
+ apply NoDup_remove_2 in H;auto.
+ apply NoDup_remove_1 in H;auto.
- generalize dependent x. induction l1;intros.
+ simpl. apply H.
+ simpl in H.
  inversion H;subst.
  inversion H3;subst.
  assert (NoDup (x :: l1 ++ l2)).
  { econstructor.
    { intros C. apply (in_cons a) in C. contradiction. }
    auto.
  }
  pose proof (IHl1 _ H0).
  simpl. econstructor;auto.
  intros C. apply in_app_or in C. destruct C.
  * subst. apply H4. apply in_or_app. auto.
  * destruct H6;subst.
    { inversion H;subst. apply H8. left. auto. }
    { apply H4. apply in_or_app. auto. }
Qed.


Lemma cons_app: forall X (x:X) y,
(x :: nil) ++ y = x::y.
Proof. intros. reflexivity. Qed.

Lemma in_cons_app: forall {X} {x:X} {y z},
In x (y ++ x :: z).
Proof.
intros.
apply in_or_app.
right. left. auto.
Qed.


Class Edge_Order : Type :=
{
  Eorder : Z -> Z->Prop;
  Eorder_PreOrder: PreOrder Eorder;
  Eorder_antisym: antisymmetric _ Eorder;
}.


Section graph_def_lemmas.

Context {E_Order:Edge_Order}.
Context (G:PreGraph Z Z).

Class vlis_prop (vlis : list Z) : Prop := {
  Vlis_Rep: forall v, In v vlis <->  G.(vvalid) v;
  Vlis_NoDup: NoDup vlis;
}.

Class elis_prop  (v: Z) (elis : list Z) : Prop := {
  Elis_Rep: forall e, In e elis <-> out_edges G v e;
  Elis_NoDup: NoDup elis;
  Elis_Order: StronglySorted Eorder elis
}.

(*** ***********************************  vlis/elis_prop lemmas ***************************)


Lemma vertex_in_vprop {v sigma}:
  vlis_prop sigma -> G.(vvalid) v ->
  exists vs, vlis_prop (v::vs).
Proof.
  intros.
  destruct H as [Hrep Hnd].
  apply Hrep in H0.
  apply in_split in H0.
  destruct H0 as [l1 [l2 H]]. subst.
  exists (l1++l2).
  split.
  + 
    intros;split;intro.
    - apply Hrep. apply in_or_app. simpl. 
      destruct H;auto. apply in_app_or in H.
      tauto.
    - apply Hrep in H. 
      rewrite app_comm_cons. apply in_or_app.
      simpl. apply in_app_or in H. simpl in H.
      tauto.
  + constructor.
    - apply NoDup_remove_2. auto.
    - apply NoDup_remove_1 in Hnd. auto.
Qed.

Lemma edge_deterministic {es1 es2:list Z} {v: Z}
  (E1: elis_prop v es1) (E2: elis_prop v es2): es1 = es2.
Proof.
  destruct E1 as [Ea E1].
  destruct E2 as [Eb E2].
  specialize (prop_equiv3 Ea Eb) as H.
  simpl in H. clear Ea Eb v.
  generalize dependent es2.
  induction E1 as [|e1 es1].
  - intros. destruct es2. auto.
    exfalso. pose proof (in_eq z es2).
    apply H in H0. inversion H0.
  - intros es2 E3 E4 H0.
    destruct es2 as [|e2 es2].
    + pose proof (in_eq e1 es1). apply H0 in H1.  inversion H1. 
    + assert (e2 = e1).
      { pose proof (in_eq e1 es1). apply H0 in H1.
        destruct H1;auto.
        pose proof (in_eq e2 es2). apply H0 in H2.
        destruct H2;auto.
        assert (Eorder e1 e2).
        { eapply Forall_forall.
          inversion Elis_Order0;subst. apply H6. auto. }
        assert (Eorder e2 e1). 
        { eapply Forall_forall. 
          inversion E4;subst. apply H7. auto. }
        apply Eorder_antisym;auto. }
      subst.
      inversion E4;subst;clear E4.
      inversion E3;subst;clear E3.
      inversion Elis_Order0;subst.
      f_equal.
      apply IHE1;auto;split;intro.
      * pose proof (in_cons e1 e es1 H1). apply H0 in H2.
        destruct H2. { subst. contradiction. } { auto. }
      * pose proof (in_cons e1 e es2 H1). apply H0 in H2.
        destruct H2. { subst. contradiction. } { auto. }
Qed.

Lemma vprop_src: forall v es, elis_prop v es  ->
  forall e, In e es -> G.(src) e = v.
Proof.
  intros.
  destruct H.
  apply Elis_Rep0 in H0.
  destruct H0.
  auto.
Qed.

Lemma vprop_evalid: forall v es, elis_prop v es  ->
  forall e, In e es -> G.(evalid) e.
Proof.
  intros.
  destruct H.
  apply Elis_Rep0 in H0.
  destruct H0.
  auto.
Qed.

Lemma vprop_in_list: forall v es, elis_prop v es ->
  forall e, G.(evalid) e /\ G.(src) e = v -> In e es.
Proof.
  intros.
  destruct H.
  apply Elis_Rep0.
  auto.
Qed.

Lemma vprop_step: forall v es, elis_prop v es  ->
  G.(vvalid) v ->
  forall e, G.(vvalid) (G.(dst) e) -> In e es -> step G v (G.(dst) e).
Proof.
  intros.
  destruct H.
  apply Elis_Rep0 in H2.
  destruct H2.
  repeat split;auto.
  exists e.
  econstructor;auto.
Qed.

Lemma eprop_NoDup: forall v es, elis_prop v es ->
  NoDup es.
Proof.
  intros. inversion H;auto.
Qed.

Lemma eprop_NoDup_remove_2: forall v e' es1 es2,
  elis_prop v (es1 ++ e' :: es2)
  -> ~ In e' es1.
Proof. intros.
  apply eprop_NoDup in H.
  apply NoDup_remove_2 in H.
  intros C. apply H. apply in_or_app. auto.
Qed.

Lemma  vlis_elis_dst_invlis : forall v vs es e,
  vlis_prop (v::vs) ->
  elis_prop v es ->
  In e es -> G.(vvalid) (G.(dst) e) -> In (G.(dst) e) vs.
Proof.
  intros.
  destruct H0 as [H0 H0_ H0_1].
  assert (out_edges G v e) as [? ?].
  { eapply H0;eauto. }
  destruct H as [H H_].
  apply H in H2 as[? | ?].
  subst.
Abort.


Lemma  vlis_permutation : forall vs vs1,
  vlis_prop vs -> vlis_prop vs1 -> Permutation vs vs1.
Proof.
  intros.
  destruct H as [H H_].
  destruct H0 as [H0 H0_].
  apply NoDup_Permutation;auto.
  intros.
  split;intros.
  apply H0. apply H;auto.
  apply H;apply H0;auto.
Qed.

Lemma vlis_prop_length: forall vs1 vs2, vlis_prop vs1 ->
  vlis_prop vs2 -> length vs1 = length vs2.
Proof.
  intros. 
  apply Permutation_length. apply vlis_permutation;auto.
Qed.

Lemma elis_in_midlle_neq_r : forall v l1 l2 (e e0: Z), 
  elis_prop v (l1 ++ e:: l2) -> In e0 l2 -> e0 <> e.
Proof.
  intros. destruct H. 
  apply NoDup_app_r in Elis_NoDup0. 
  inversion Elis_NoDup0. subst.
  unfold not;intros. subst. contradiction.
Qed.
End graph_def_lemmas.

(*************************************************************************************)
(*  2. the aux definitions for graph represitations                                  *)  
(*                                                                                   *)                 
(*  struct vertex {                                                                  *)
(*    struct edge* vedge;                                                            *)
(*    int visited; };                                                                *)
(*  struct edge {                                                                    *)
(*   struct vertex* etail;                                                           *)
(*   struct edge* next; };                                                           *)
(*                                                                                   *)
(*************************************************************************************)
Import ImpRules.
Local Open Scope asrt_scope.
Record Vertex_field : Type := {
   vist: Z -> Z;
}.

Definition field_storage (vpm: Perm.t) (vl: Vertex_field) (v: Z) : assertion :=
  PV (v + 1) @ vint ↦ₗ (vist vl v) $ vpm.

Definition data_at_t_edge_node (gpm: Perm.t) (vl : Z * Z) e :assertion :=
  let (v, y) := vl in 
  PV e @ vptr ↦ₗ v $ gpm ** PV (e + 1) @ vptr ↦ₗ  y $ gpm.


Section model_def.

(**************************************  Edge Storage Specifications ***************************)
Context {E_Order:Edge_Order}.
Context (Gsh Vsh: Perm.t).
Context (GshH: Perm.readable_perm Gsh).
Context (G:PreGraph Z Z).
Context (V_field:Vertex_field).

Definition AVertex pedge v: assertion := 
  PV v @ vptr ↦ₗ pedge $ Gsh **
  field_storage Vsh V_field v.

Fixpoint edge_storage (sigma: list Z) : assertion := 
match sigma with
 | nil => emp
 | e::es => !! ( G.(vvalid) (G.(dst) e)) &&   !! (isvalidptr e) && 
   data_at_t_edge_node Gsh ((G.(dst) e), (hd 0 es) ) e
   ** edge_storage es
end.

Arguments edge_storage sigma: simpl never.

Fixpoint edge_seg (sigma: list Z) (pend:Z) : assertion:= 
match sigma with
 | nil => ImpRules.emp
 | e::es => !! ( G.(vvalid) (G.(dst) e)) && !! (isvalidptr e) && 
 data_at_t_edge_node Gsh ((G.(dst) e),(hd pend es) ) e
 ** edge_seg es pend
end.

Arguments edge_seg sigma pend: simpl never.

(**************************************  Graph Storage Specifications ***************************)
Fixpoint vertex_storage (sigma: list Z):  assertion:= 
 match sigma with
 | nil => emp
 | v::vs =>
   EX es:list Z, !! (elis_prop G v es) && !! (isvalidptr v) && 
   AVertex (hd 0 es) v **
   edge_storage es **
   vertex_storage vs
 end.

Definition graphrep : assertion:= 
EX vs: list Z, !! (vlis_prop G vs) &&
  vertex_storage vs.

(************************** Specification About Particular Graph Field ***************************)

Definition rest_of_graph v : assertion:= 
  EX vs: list Z, EX es: list Z,
  !! (elis_prop G v es) && !! (vlis_prop G (v::vs)) && 
  !! (isvalidptr v) &&
  PV v @ vptr ↦ₗ (hd 0 es) $ Gsh **
  vertex_storage vs **
  edge_storage es.

(** ***************************************
lemmas    *)

Lemma field_rep_valid_pointer v:
   field_storage Vsh V_field v **
   rest_of_graph v
   |-- !! isvalidptr v.
Proof.
  unfold rest_of_graph.
  Intros vs es.
  quick_entailer!.
Qed.

Hint Resolve field_rep_valid_pointer : valid_pointer.

(** ***************************************
***************Lemmas About Edge *********)

Lemma fold_edge_node  : forall gpm e v y,
  PV e @ vptr ↦ₗ v $ gpm ** PV (e + 1) @ vptr ↦ₗ  y $ gpm |-- 
  data_at_t_edge_node gpm (v,y) e.
Proof.
  unfold data_at_t_edge_node; intros.
  refl.
Qed.

Lemma edge_storage_local_facts:
  forall sigma,
   edge_storage sigma |--
   !! ((hd 0 sigma = 0 <-> sigma = nil)).
Proof.
  intros.
  induction sigma;unfold edge_storage; fold edge_storage; intros.
  - quick_entailer!. intuition.
  - simpl. quick_entailer!.  split;intro.
    + subst a. inversion H0.
    + inversion H1. 
Qed.

Hint Resolve edge_storage_local_facts : saturate_local.


Lemma edge_deterministic_sep {es1 es2:list Z} {v: Z}
  (E1: elis_prop G v es1) (E2: elis_prop G v es2):
  edge_storage es1 |-- edge_storage es2.
Proof.
  intros.
  assert (es1 = es2).
  { eapply edge_deterministic. apply E1. apply E2. }
  subst. apply derivable1_refl.
Qed.

Lemma singleton_eseg: forall  (x y: Z),
  G.(vvalid) (G.(dst) x) -> isvalidptr x ->
  data_at_t_edge_node Gsh ((G.(dst) x),y) x
  |-- edge_seg (x::nil) y.
Proof.
  intros.
  unfold edge_seg.
  quick_entailer!.
Qed.


Lemma edgeseg_zero: forall sigma,
  edge_seg sigma 0 |-- edge_storage sigma.
Proof.
  intros.
  induction sigma; intros.
  + unfold edge_storage, edge_seg.
    quick_entailer!.
  + unfold edge_seg; fold edge_seg.
    unfold edge_storage; fold edge_storage.
    rewrite (IHsigma).
    quick_entailer!.
Qed.

Lemma eseg_eseg: forall (s1 s2: list Z) (z: Z),
  edge_seg s1 (hd z s2) ** edge_seg s2 z |-- edge_seg (s1 ++ s2) z.
Proof.
  intros.
  induction s1; intros.
  - rewrite app_nil_l. induction s2.
    + unfold edge_seg. quick_entailer!.
    + unfold edge_seg;fold edge_seg.
      quick_entailer!.
  - rewrite <- app_comm_cons. unfold edge_seg;fold edge_seg.
    Intros.
    rewrite (IHs1). rewrite hd_app.
    quick_entailer!.
Qed.

Lemma eseg_split: forall (s1 s2: list Z) (z: Z),
  edge_seg (s1 ++ s2) z --||--
    edge_seg s1 (hd z s2) ** edge_seg s2 z.
Proof.
  intros.
  induction s1; intros.
  - rewrite app_nil_l.
    apply logic_equiv_derivable1;split.
    unfold edge_seg;entailer!.
    unfold edge_seg;entailer!.
  - rewrite <- app_comm_cons. unfold edge_seg;fold edge_seg.
    apply logic_equiv_derivable1;split.
    + Intros.
      rewrite IHs1.
      rewrite hd_app.  quick_entailer!.
    + Intros.
      rewrite IHs1.
      rewrite hd_app.  quick_entailer!.
Qed.

Lemma edge_seg_list: forall (s1 s2: list Z),
  edge_seg s1 (hd 0 s2) ** edge_storage s2 
  --||-- edge_storage (s1 ++ s2).
Proof.
  intros.
  induction s1; intros.
  - rewrite app_nil_l. 
    apply logic_equiv_derivable1;split.
    unfold edge_seg. quick_entailer!.
    unfold edge_seg. quick_entailer!.
  - rewrite <- app_comm_cons. unfold edge_seg, edge_storage.
    fold edge_seg. fold edge_storage.
    apply logic_equiv_derivable1;split.
    + Intros.
    rewrite (IHs1).
    rewrite hd_app. quick_entailer!.
    + Intros.
    rewrite (IHs1).
    rewrite hd_app. quick_entailer!.
Qed.

Lemma edge_storage_simpl: forall v s,
 edge_storage (v::s) |--
 edge_seg (v::nil) (hd 0 s) ** edge_storage s.
Proof. intros. simpl.
  unfold edge_storage;fold edge_storage.
  unfold edge_seg.
  rewrite hd_app. simpl. quick_entailer!.
Qed.

Lemma edge_storage_zero: forall s,
 edge_storage s |--
 edge_seg s 0.
Proof. intros. induction s.
  - simpl. unfold edge_storage. unfold edge_seg. quick_entailer!.
  - intros. unfold edge_storage;fold edge_storage.
    unfold edge_seg;fold edge_seg.
    Intros.
    rewrite IHs.
    quick_entailer!.
Qed.



(**************************************
 ********************** Vertex Lemmas *)
 
Lemma fold_pure_storage: forall pedge v,
  field_storage Vsh V_field v **
  PV v @ vptr ↦ₗ pedge $ Gsh 
  |-- AVertex pedge v.
Proof. intros.
  unfold  AVertex.
  cancel.
Qed.

Lemma fold_vertex_storage {v es} 
  (Hes: elis_prop G v es):
    isvalidptr v ->
   AVertex (hd 0 es) v ** edge_storage es
   |-- vertex_storage (v::nil).
Proof.
  intros.
  unfold vertex_storage.
  Exists es.
  quick_entailer!.
Qed.

Lemma unfold_vertex_storage {v es} (Hes: elis_prop G v es):
   vertex_storage (v::nil) |--
   AVertex (hd 0 es) v ** edge_storage es.
Proof.
  intros.
  unfold vertex_storage.
  Intros es0.
  rewrite (edge_deterministic G Hes H) in *.
  quick_entailer!.
Qed.

Lemma vertex_storage_local_facts:
  forall sigma v, In v sigma ->
   vertex_storage sigma |--
   !! (isvalidptr v) .
Proof.
intros.
generalize dependent v.
induction sigma.
- intros. inversion H.
- intros. destruct H.
  + subst. unfold vertex_storage;fold vertex_storage.
    Intros es. unfold AVertex. quick_entailer!.
  + apply IHsigma in H. unfold vertex_storage;fold vertex_storage.
    Intros es. rewrite H.
    quick_entailer!. 
Qed.
Hint Resolve vertex_storage_local_facts : saturate_local.

Lemma vertex_single_local_facts:
  forall v,
   vertex_storage (v::nil) |--
   !! (isvalidptr v).
Proof.
  intros.
  apply vertex_storage_local_facts.
  simpl;auto.
Qed.

Hint Resolve vertex_single_local_facts : saturate_local.

Lemma vertex_storage_valid_pointer:
  forall sigma v, In v sigma -> 
   vertex_storage sigma |-- !! isvalidptr v.
Proof.
  intros. 
  generalize dependent v.
  induction sigma.
  - intros. inversion H.
  - intros. destruct H.
    + subst. unfold vertex_storage;fold vertex_storage.
      Intros es.
      unfold AVertex.
      Intros.
      quick_entailer!.
    + apply IHsigma in H. unfold vertex_storage;fold vertex_storage.
      Intros es. rewrite H. quick_entailer!.
Qed.

Hint Resolve vertex_storage_valid_pointer : valid_pointer.

Lemma vertex_single_valid_pointer:
  forall v,
   vertex_storage (v::nil) |-- !! isvalidptr v.
Proof.
  intros. 
  apply vertex_storage_valid_pointer;simpl;auto.
Qed.

Hint Resolve vertex_single_valid_pointer : valid_pointer.



Lemma vertex_storage_app: forall sigma1 sigma2,
  vertex_storage sigma1 ** vertex_storage sigma2
  |-- vertex_storage (sigma1 ++ sigma2).
Proof.
  intros. revert sigma2.
  induction sigma1.
  - intros. unfold vertex_storage;fold vertex_storage.
    rewrite app_nil_l. quick_entailer!.
  - intros. rewrite <- app_comm_cons.
    unfold vertex_storage;fold vertex_storage.
    Intros es.
    Exists es .
    rewrite (IHsigma1 sigma2).
    quick_entailer!.
Qed.

Lemma vertex_storage_cons: forall v sigma,
  vertex_storage (v::nil) ** vertex_storage sigma
  |-- vertex_storage (v::sigma).
Proof.
  intros. rewrite vertex_storage_app.
  rewrite cons_app.
  apply derivable1_refl.
Qed.


Arguments vertex_storage sigma: simpl never.

Lemma vertex_storage_split: forall sigma1 sigma2,
  vertex_storage (sigma1++sigma2) 
  |-- vertex_storage sigma1 **  vertex_storage sigma2.
Proof.
  intros. revert sigma2.
  induction sigma1.
  - intros. unfold vertex_storage;fold vertex_storage.
    rewrite app_nil_l. quick_entailer!.
  - intros. rewrite <- app_comm_cons.
    unfold vertex_storage;fold vertex_storage.
    Intros es.
    Exists es.
    rewrite (IHsigma1 sigma2).
    quick_entailer!.
Qed.

Lemma vertex_storage_cons_split: forall v sigma,
  vertex_storage (v::sigma) 
  |-- vertex_storage (v::nil) ** vertex_storage sigma.
Proof.
  intros. pose proof (cons_app _ v sigma).
  rewrite <- H.
  rewrite vertex_storage_split.
  quick_entailer!.
Qed.

Lemma vertex_storage_cons_comm: forall sigma v,
  vertex_storage ((v::nil) ++ sigma)
  |-- vertex_storage (sigma ++ (v::nil)).
Proof.
  intros.
  induction sigma.
  - rewrite app_nil_l. rewrite app_nil_r. quick_entailer!.
  - simpl.
    unfold vertex_storage; fold vertex_storage.
    Intros es1.
    Intros es2.
    Exists es2.
    quick_entailer!.
    rewrite (fold_vertex_storage H).
    rewrite sepcon_comm_logic_equiv.
    rewrite vertex_storage_app.
    quick_entailer!.
    auto.
Qed.

Lemma vertex_storage_cons_comm_r: forall sigma v,
  vertex_storage (sigma++(v::nil))
  |-- vertex_storage ((v::nil)++sigma).
Proof.
  intros.
  induction sigma.
  - rewrite app_nil_l. rewrite app_nil_r. quick_entailer!.
  - simpl. simpl in IHsigma.
    unfold vertex_storage; fold vertex_storage.
    Intros es1.
    rewrite IHsigma. 
    unfold vertex_storage; fold vertex_storage.
    Intros es2.
    Exists es2.
    Exists es1.
    quick_entailer!.
Qed.

Lemma vertex_storage_app_comm: forall sigma1 sigma2 (*(E: NoDup (v::sigma))*),
  vertex_storage (sigma1 ++ sigma2)
  |-- vertex_storage (sigma2 ++ sigma1).
Proof.
  intros.
  revert sigma1.
  induction sigma2.
  - intros. rewrite app_nil_l. rewrite app_nil_r. quick_entailer!.
  - intros.  rewrite app_cons_assoc.
    sep_apply IHsigma2.
    rewrite <- app_comm_cons.
    rewrite app_assoc.
    assert (a :: sigma2 ++ sigma1 = (a::nil) ++ (sigma2++sigma1));auto.
    rewrite H.
    sep_apply vertex_storage_cons_comm_r.
    quick_entailer!.
Qed.

(**************************************************
***********Lemmas About Equivalent Vertex Storage *)

Lemma vertex_storage_equiv { vs1 vs2}: 
  vlis_prop G vs1 -> vlis_prop G vs2 ->
  vertex_storage vs1 |-- vertex_storage vs2.
Proof.
  intros.
  destruct H,H0.
  pose proof (prop_equiv3 Vlis_Rep0 Vlis_Rep1).
  simpl in H. clear Vlis_Rep0 Vlis_Rep1.
  generalize dependent vs1.
  induction vs2;intros.
  - destruct vs1.
    { quick_entailer!. }
    { exfalso.
      pose proof (in_eq z vs1).
      apply H in H0. destruct H0. }
  - pose proof (in_eq a vs2).
    apply H in H0.
    apply in_split in H0.
    destruct H0 as [l1 [l2 H0]].
    subst vs1.
    sep_apply vertex_storage_split.
    sep_apply vertex_storage_cons_split.
    inversion Vlis_NoDup1;subst;simpl.
    pose proof NoDup_remove_1 _ _ _ Vlis_NoDup0.
    assert ((forall e : Z, In e (l1 ++ l2) <-> In e vs2)).
    { intros. split;intro.
      - assert (In e (l1 ++ a :: l2)).
        { apply in_or_app. apply in_app_or in H1.
          simpl. tauto. }
        apply H in H4.
        destruct H4;auto.
        subst. 
        apply NoDup_remove_2 in Vlis_NoDup0.
        contradiction.
      - pose proof (in_cons a _ _ H1).
        apply H, in_app_or in H4;simpl in H4.
        apply in_or_app. destruct H4 as [? |[? | ?]];auto.
        subst. inversion Vlis_NoDup1. contradiction.
    }
    specialize (IHvs2 H3 _ H0 H1).
    assert (vertex_storage l1 ** vertex_storage l2 |-- vertex_storage vs2).
    { rewrite vertex_storage_app. auto. }
    sep_apply_pre H4.
    rewrite sepcon_assoc_logic_equiv.
    unfoldimpmodel.
    sep_apply H4. rewrite vertex_storage_app.
    sep_apply vertex_storage_cons_comm_r.
    simpl. apply derivable1_refl.
Qed.

Theorem vertex_in_storage {v sigma}: 
  vlis_prop G sigma -> G.(vvalid) v ->
  vertex_storage sigma 
  |-- EX vs:list Z,  !! (vlis_prop G (v::vs)) &&
  vertex_storage (v::nil) ** vertex_storage vs.
Proof.
  intros.
  pose proof vertex_in_vprop G H H0.
  destruct H1 as [vs H1].
  Exists vs.
  sep_apply (vertex_storage_equiv H H1).
  sep_apply vertex_storage_cons_split.
  quick_entailer!.
Qed.

Theorem vertex_in_vertex_list {v sigma}: 
  vlis_prop G sigma -> In v sigma ->
  vertex_storage sigma 
  |-- EX vs:list Z, !! (vlis_prop G (v::vs)) &&
  vertex_storage (v::nil) ** vertex_storage vs.
Proof.
  intros.
  apply vertex_in_storage;auto.
  destruct H.
  apply Vlis_Rep0.
  auto.
Qed.

Theorem vertex_in_storage_list {v1 v2 vlis}: 
  vlis_prop G (v1::vlis) -> In v2 vlis ->
  vertex_storage vlis 
  |-- EX vs:list Z, !! (vlis_prop G (v2::v1::vs)) &&
  vertex_storage (v2::nil) ** vertex_storage vs.
Proof.
  intros. apply in_split in H0.
  destruct H0 as [l1 [l2 H0]].
  subst vlis.
  Exists (l1++l2).
  sep_apply vertex_storage_split.
  sep_apply vertex_storage_cons_split.
  quick_entailer!.
  { rewrite sepcon_comm_logic_equiv. unfoldimpmodel. rewrite vertex_storage_app.  quick_entailer!. }
  { destruct H as [H1 H2].
    split.
    - apply (prop_equiv4 H1). intros. split;intro.
      + eapply Permutation_in;[|apply H].
        rewrite <- Permutation_middle.
        apply perm_swap.
      + eapply Permutation_in;[|apply H].
        rewrite <- Permutation_middle.
        apply perm_swap.
    - eapply Permutation_NoDup;[|apply H2].
      rewrite <- Permutation_middle.
      apply perm_swap.
  }
Qed.


(** ***************************************
 **********   Lemmas About Graph *)
Lemma make_graph:
  graphrep |-- graphrep && 
  !! (exists vs, vlis_prop G vs).
Proof.
  unfold graphrep.
  Intros vs.
  Exists vs.
  quick_entailer!.
  exists vs.
  intuition.
Qed.

Lemma unfold_graph {vs}: vlis_prop G vs ->
  graphrep |-- vertex_storage vs.
Proof.
  intros.
  unfold graphrep.
  Intros vs0.
  apply (vertex_storage_equiv H0 H).
Qed.

Lemma fold_graph {vs}: vlis_prop G vs ->
  vertex_storage vs |-- graphrep.
Proof.
  intros.
  unfold graphrep.
  Exists vs.
  quick_entailer!.
Qed.

Lemma fold_field_storage v:
  PV (v + 1) @ vint ↦ₗ (vist V_field v) $ Vsh 
  |-- field_storage Vsh V_field v.
Proof.
  unfold field_storage.
  cancel.
Qed.


Theorem fold_graph_field (v:Z):
  field_storage Vsh V_field v 
  ** rest_of_graph v
  |-- graphrep.
Proof.
  unfold graphrep.
  unfold field_storage.
  unfold rest_of_graph.
  Intros vs es.
  sep_apply (fold_field_storage).
  sepcon_lift (field_storage Vsh V_field v).
  sepcon_lift (PV v @ vptr ↦ₗ hd 0 es $ Gsh).
  sep_apply (fold_pure_storage).
  sep_apply (fold_vertex_storage H).
  rewrite vertex_storage_app. simpl.
  Exists (v::vs).
  quick_entailer!.
  auto.
Qed.

Theorem fold_graph_field' :forall  (v:Z) (vs: list Z) (es: list Z),
  elis_prop G v es -> vlis_prop G (v::vs) -> isvalidptr v ->
  field_storage Vsh V_field v 
  ** PV v @ vptr ↦ₗ (hd 0 es) $ Gsh **
  vertex_storage vs **
  edge_storage es
  |-- graphrep.
Proof.
  intros.
  eapply derivable1_trans.
  2: eapply (fold_graph_field v).
  unfold rest_of_graph.
  Exists vs es.
  quick_entailer!.
Qed.

Theorem unfold_field_storage (v:Z):
  G.(vvalid) v ->
  graphrep |-- field_storage Vsh V_field v 
  ** rest_of_graph v.
Proof.
  intros.
  unfold graphrep.
  unfold field_storage.
  unfold rest_of_graph.
  Intros vs.
  pose proof vertex_in_vprop G H0 H.
  destruct H1 as [vs' H1].
  sep_apply (vertex_storage_equiv H0 H1).
  sep_apply vertex_storage_cons_split.
  unfold vertex_storage at 1.
  Intros es.
  Exists vs' es.
  unfold AVertex.
  unfold field_storage.
  quick_entailer!.
Qed.

End model_def.


(** ***************************************
 **********   Lemmas About Vertex Field, vertex storage, rest_of_graph_aux graphrep   *)
Definition rest_of_graph_aux {E_Order : Edge_Order} Gsh Vsh G vf v vs es : assertion:= 
  !! (elis_prop G v es) && !! (vlis_prop G (v::vs)) && !! (isvalidptr v) &&
  PV v @ vptr ↦ₗ (hd 0 es) $ Gsh **
  vertex_storage Gsh Vsh G vf vs **
  edge_storage Gsh G es.

Lemma fold_rest_of_graph_aux : forall {E_Order : Edge_Order} Gsh Vsh G vf v vs es,
  elis_prop G v es -> vlis_prop G (v::vs) -> isvalidptr v ->
  PV v @ vptr ↦ₗ (hd 0 es) $ Gsh **
  vertex_storage Gsh Vsh G vf vs **
  edge_storage Gsh G es
  |--  rest_of_graph_aux Gsh Vsh G vf v vs es.
Proof.
  intros.
  unfold rest_of_graph_aux.
  quick_entailer!.
Qed.

Lemma vertex_storage_permutation : forall {E_Order : Edge_Order} Gsh Vsh G vf vs vs',
  Permutation vs vs' ->
  vertex_storage Gsh Vsh G vf vs --||-- vertex_storage Gsh Vsh G vf vs'.
Proof.
  intros.
  induction H.
  - simpl. apply logic_equiv_refl.
  - cbn. apply ex_logic_euiqv_elim_both. intros.
    rewrite IHPermutation.
    apply logic_equiv_refl.
  - cbn.
    apply logic_equiv_derivable1. unfoldimpmodel. split.
    + Intros es es0.
      Exists es0 es.
      quick_entailer!.
    + Intros es es0.
      Exists es0 es.
      quick_entailer!.
  - rewrite IHPermutation1.
    auto.
Qed.

Lemma vertex_storage_in: forall {E_Order : Edge_Order} Gsh Vsh G vf vs v,
  In v vs ->
  vertex_storage Gsh Vsh G vf vs --||-- 
  EX vs', !! Permutation vs (v::vs') &&
          vertex_storage Gsh Vsh G vf (v::vs').
Proof.
  intros. revert v H.
  induction vs;intros.
  - simpl in H. contradiction.
  - destruct H.
    + subst.
      apply logic_equiv_derivable1. unfoldimpmodel. split.
      * Exists vs.
        quick_entailer!.
      * Intros vs'.
        quick_entailer!.
        erewrite (vertex_storage_permutation Gsh Vsh G vf (v::vs));eauto.
        refl.
    + cbn. 
      apply logic_equiv_derivable1. unfoldimpmodel. split.
      * Intros es.
        rewrite (IHvs _ H). cbn.
        Intros vs' es0.
        Exists (a::vs') es0. cbn. Exists es.
        quick_entailer!.
        rewrite H4.
        constructor.
      * Intros vs' es.
        specialize (IHvs _ H).
        quick_entailer!.
        eapply derivable1_trans with (vertex_storage Gsh Vsh G vf (a::vs)).
        unfoldimpmodel.
        { erewrite (vertex_storage_permutation Gsh Vsh G vf (a::vs));eauto.
        simpl.
        Exists es. quick_entailer!. }
        cbn.
        refl.
Qed.

Lemma vertex_storage_app_r {E_Order : Edge_Order}: forall vs1 vs2 Gsh pm pg vf vf_new,
  vlis_prop pg (vs1 ++ vs2) ->
  (forall v', ~ List.In v' vs1 -> vist vf v' = vist vf_new v') ->
  vertex_storage Gsh pm pg vf vs2
  |-- vertex_storage Gsh pm pg vf_new vs2.
Proof.
  intros vs1 vs2. revert vs1. 
  induction vs2;intros.
  - simpl. refl.
  - assert (~ In a vs1). 
    { pose proof H as [H4 H5].
      apply NoDup_remove_2 in H5.
      unfold not;intros.
      apply H5.
      apply in_or_app.
      tauto. }
    pose proof H0 a H1.
    rewrite app_cons_assoc in H.
    simpl.
    eapply ex_elim_both.
    intros es.
    unfold AVertex, field_storage.
    rewrite H2.
    asrt_simpl.
    quick_entailer!.
    eapply IHvs2;eauto.
    intros. eapply H0. 
    unfold not. intros.
    apply H5. apply in_or_app. tauto.
Qed.

Lemma vertex_storage_hd {E_Order : Edge_Order}: forall v vs2 Gsh pm pg vf vf_new,
  vlis_prop pg (v:: vs2) ->
  (forall v', v' <> v -> vist vf v' = vist vf_new v') ->
  vertex_storage Gsh pm pg vf vs2
  |-- vertex_storage Gsh pm pg vf_new vs2.
Proof.
  intros.
  rewrite <- cons_app in H.
  eapply vertex_storage_app_r;eauto.
  simpl;intros; eapply H0.
  unfold not;intros; apply H1;left;auto.
Qed.


(* Ltac fold_field_storage' v vsh new_field := 
  match goal with 
  | |- ?Q |-- _ =>  
      match Q with 
      | context [PV Z.add v (Z.repr 1) ↦ₗ ?dfn_v $ vsh ] =>
        match Q with 
        | context [PV Z.add v (Z.repr 2) ↦ₗ ?low_v $ vsh ] 
          => match Q with 
          | context [PV Z.add v (Z.repr 3) ↦ₗ ?instack_v $ vsh ] 
          => match Q with 
          | context [PV Z.add v (Z.repr 4) ↦ₗ ?scc_v  $ vsh ] => 
            try strongseplift (PV Z.add v (Z.repr 4) ↦ₗ scc_v  $ vsh );
            strongseplift (PV Z.add v (Z.repr 3) ↦ₗ instack_v $ vsh);
            strongseplift (PV Z.add v (Z.repr 2) ↦ₗ low_v $ vsh);
            strongseplift (PV Z.add v (Z.repr 1) ↦ₗ dfn_v $ vsh);
            replace dfn_v with (dfn new_field v) at 1;[ 
            replace low_v with (low new_field v) at 1;[ 
            replace instack_v with (instack new_field v) at 1;[ 
            replace scc_v with (scc new_field v) at 1;[ 
              let a:= fresh "P" in 
              match goal with 
              | |- ?P |-- _ =>  sep_remember 4%nat P a end;
              strongseplift a;
              eapply derivable1_sepcon_mono;[subst a;refl | eapply fold_field_storage ]
            | try (simpl;congruence)] 
            | try (simpl;congruence)] 
            | try (simpl;congruence)] 
            | try (simpl;congruence)]
          | _ => fail end
          | _ => fail end
        | _ => fail end
      | _ => fail end
  end.

Ltac fold_t_edge_node' Gsh e :=
  match goal with 
  | |- ?P |-- _ => match P with 
                  | context [PV e ↦ₗ ?v $ Gsh ] =>
                      match P with 
                      | context [ PV (Z.add e (Z.repr 1)) ↦ₗ  ?y $ Gsh] =>
                          strongseplift (PV (Z.add e (Z.repr 1)) ↦ₗ  y $ Gsh);
                          strongseplift (PV e ↦ₗ v $ Gsh);
                          let a:= fresh "P" in 
                          match goal with 
                          | |- ?P |-- _ =>  sep_remember 2%nat P a end;
                          strongseplift a;
                          eapply derivable1_sepcon_mono;
                          [subst a;refl | eapply (fold_edge_node Gsh e v y)]
                      | _ => fail
                      end
                  | _ => fail
                  end
  | |- _ => fail
  end.

Ltac edge_node2edge_seg' :=
  match goal with 
  | |- context [data_at_t_edge_node ?gpm ?vl ?e ] => rewrite singleton_eseg;[refl | solve [subst;auto] ] end.

Ltac edgeseg_storage_append' vs1 vs2 :=
  match goal with 
  | |- context [edge_seg ?gpm ?pg vs1 ?pend1] => 
      match goal with 
      | |- context [edge_storage ?gpm ?pg vs2] => 
            let h:= fresh "H" in assert (pend1 = (hd 0 vs2));[
              simpl;congruence | ];
              change (edge_seg gpm pg vs1 pend1) with (edge_seg gpm pg vs1 (hd 0 vs2));
              clear h;
              strongseplift (edge_storage gpm pg vs2);
              strongseplift (edge_seg gpm pg vs1 (hd 0 vs2));
              let a:= fresh "P" in 
              match goal with 
              | |- ?P |-- _ =>  sep_remember 2%nat P a end;
              strongseplift a;
              eapply derivable1_sepcon_mono;
              [subst a;refl | rewrite (edge_seg_list gpm pg vs1 vs2);refl ]

      | |- _ => fail
      end 
  | |- _ => fail
  end.

Ltac fold_graphrep' Gsh v vs es :=
    match goal with 
    | |- context [field_storage ?Vsh ?vf v] =>
        match goal with 
        | |- context [PV v ↦ₗ ?e $ Gsh] =>
          match goal with 
          | |- context [vertex_storage Gsh Vsh ?pg vf vs] =>
              match goal with 
              | |- context [edge_storage Gsh pg es] => 
                let h:= fresh "H" in assert (e = hd 0 es);
                [simpl;congruence | ];
                try rewrite h;
                clear h;
                strongseplift (edge_storage Gsh pg es);
                strongseplift (vertex_storage Gsh Vsh pg vf vs);
                strongseplift (PV v ↦ₗ hd 0 es $ Gsh);
                strongseplift (field_storage Vsh vf v);
                let a:= fresh "P" in 
                match goal with 
                | |- ?P |-- _ =>  sep_remember 4%nat P a end;
                strongseplift a;
                eapply derivable1_sepcon_mono;[subst a;refl | 
                eapply (fold_graph_field' Gsh Vsh pg vf v vs es);eauto ]
              end
          end
        end
    end. *)

Section graph_subst_rules.


Lemma  subst_local_fieldstorage:  forall pm V_field v x n, 
 subst_local x n (field_storage pm V_field v) --||-- field_storage pm V_field v.
Proof.
  unfold field_storage;intros.
  erewrite ! subst_local_pv.
  apply logic_equiv_refl.
Qed.

Lemma  subst_local_AVertex:  forall Gpm Vpm  V_field pedge v x n, subst_local x n (AVertex Gpm Vpm V_field pedge v) --||-- AVertex Gpm Vpm V_field pedge v.
Proof.
  unfold AVertex;intros.
  rewrite ! subst_local_sepcon.
  rewrite ! subst_local_fieldstorage.
  erewrite ! subst_local_pv.
  apply logic_equiv_refl.
Qed.

Lemma  subst_local_edgestorage:  forall Gpm G l x n, subst_local x n (edge_storage Gpm G l) --||-- edge_storage Gpm G l.
Proof.
  intros Gpm G l;revert G.
  induction l;intros.
  - simpl.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite ! subst_local_and.
    erewrite ! subst_local_sepcon.
    erewrite ! subst_local_pv.
    rewrite ! subst_local_pure.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma  subst_local_edgeseg:  forall Gpm G l pend x n, subst_local x n (edge_seg Gpm G l pend) --||-- edge_seg Gpm G l pend.
Proof.
  intros Gpm G l;revert G.
  induction l;intros.
  - simpl.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
  rewrite ! subst_local_and.
  erewrite ! subst_local_sepcon.
  erewrite ! subst_local_pv.
  rewrite ! subst_local_pure.
  erewrite IHl.
  apply logic_equiv_refl.
Qed.


Lemma  subst_local_vertexstorage {E_Order : Edge_Order}:  forall Gpm Vpm G vf l x n, subst_local x n (vertex_storage Gpm Vpm G vf l) --||-- vertex_storage Gpm Vpm G vf l.
Proof.
  intros  Gpm Vpm  G vf l;revert G vf.
  induction l;intros.
  - simpl.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_local_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    rewrite ! subst_local_and.
    erewrite ! subst_local_sepcon.
    rewrite ! subst_local_pure.
    erewrite IHl.
    rewrite subst_local_AVertex.
    rewrite subst_local_edgestorage.
    apply logic_equiv_refl.
Qed.

Lemma  subst_local_graphrep {E_Order : Edge_Order}:  forall  Gpm Vpm  G V_field x n, subst_local x n (graphrep Gpm Vpm G V_field) --||-- graphrep Gpm Vpm G V_field.
Proof.
  intros;unfold graphrep.
  rewrite subst_local_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v.
  rewrite subst_local_coqprop.
  rewrite subst_local_vertexstorage.
  apply logic_equiv_refl.
Qed.

Lemma  subst_local_rest_of_graph {E_Order : Edge_Order}:  forall  Gpm Vpm  G V_field v x n, subst_local x n (rest_of_graph Gpm Vpm G V_field v) --||-- rest_of_graph Gpm Vpm G V_field v.
Proof.
  intros;unfold rest_of_graph.
  rewrite subst_local_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v0.
  rewrite subst_local_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v1.
  rewrite ! subst_local_and.
  rewrite ! subst_local_pure.
  rewrite ! subst_local_sepcon.
  rewrite ! subst_local_pv.
  rewrite subst_local_vertexstorage.
  rewrite subst_local_edgestorage.
  apply logic_equiv_refl.
Qed.


(** ***************************************
 **********   Lemmas About substglobal *)

Lemma  subst_global_fieldstorage:  forall Vpm V_field v x n, subst_global x n (field_storage Vpm V_field v) --||-- field_storage Vpm V_field v.
Proof.
  unfold field_storage;intros.
  erewrite ! subst_global_pv.
  apply logic_equiv_refl.
Qed.

Lemma  subst_global_AVertex:  forall Gpm Vpm  V_field pedge v x n, subst_global x n (AVertex Gpm Vpm V_field pedge v) --||-- AVertex Gpm Vpm V_field pedge v.
Proof.
  unfold AVertex;intros.
  rewrite ! subst_global_sepcon.
  rewrite ! subst_global_fieldstorage.
  erewrite ! subst_global_pv.
  apply logic_equiv_refl.
Qed.

Lemma  subst_global_edgestorage:  forall Gpm G l x n, subst_global x n (edge_storage Gpm G l) --||-- edge_storage Gpm G l.
Proof.
  intros Gpm G l;revert G.
  induction l;intros.
  - simpl.
    rewrite subst_global_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite ! subst_global_and. 
    erewrite ! subst_global_sepcon.
    erewrite ! subst_global_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma  subst_global_edgeseg:  forall Gpm G l pend x n, subst_global x n (edge_seg Gpm G l pend) --||-- edge_seg Gpm G l pend.
Proof.
  intros Gpm G l;revert G.
  induction l;intros.
  - simpl.
    rewrite subst_global_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite ! subst_global_and. 
    erewrite ! subst_global_sepcon.
    erewrite ! subst_global_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma  subst_global_vertexstorage {E_Order : Edge_Order}:  forall Gpm Vpm G vf l x n, subst_global x n (vertex_storage Gpm Vpm G vf l) --||-- vertex_storage Gpm Vpm G vf l.
Proof.
  intros Gpm Vpm G vf l;revert G vf.
  induction l;intros.
  - simpl.
    rewrite subst_global_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_global_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    rewrite ! subst_global_and. 
    erewrite ! subst_global_sepcon.
    erewrite ! subst_global_AVertex.
    erewrite ! subst_global_edgestorage.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma  subst_global_graphrep {E_Order : Edge_Order}:  forall Gpm Vpm G V_field x n, subst_global x n (graphrep Gpm Vpm G V_field) --||-- graphrep Gpm Vpm G V_field.
Proof.
  intros;unfold graphrep.
  rewrite subst_global_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v.
  rewrite subst_global_coqprop.
  rewrite subst_global_vertexstorage.
  apply logic_equiv_refl.
Qed.

Lemma  subst_global_rest_of_graph {E_Order : Edge_Order}:  forall  Gpm Vpm  G V_field v x n, subst_global x n (rest_of_graph Gpm Vpm G V_field v) --||-- rest_of_graph Gpm Vpm G V_field v.
Proof.
  intros;unfold rest_of_graph.
  rewrite subst_global_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v0.
  rewrite subst_global_exp.
  eapply ex_logic_euiqv_elim_both.
  intro v1.
  rewrite ! subst_global_and.
  rewrite ! subst_global_pure.
  rewrite ! subst_global_sepcon.
  rewrite ! subst_global_pv.
  rewrite subst_global_vertexstorage.
  rewrite subst_global_edgestorage.
  apply logic_equiv_refl.
Qed.


(** ***************************************
 **********   Lemmas About closed *)
Lemma closedlvars_edge_storage: forall Gpm G l vs, 
 closed_wrt_lvars vs (edge_storage Gpm G l).
Proof.
  intros Gpm G l. induction l;intros.
  - simpl. solve_closedlvars assumption.
  - cbn.
    solve_closedlvars assumption.
    apply IHl.
Qed. 

Lemma closedlvars_edge_seg: forall Gpm G l pend vs, 
 closed_wrt_lvars vs (edge_seg Gpm G l pend).
Proof.
  intros Gpm G l. induction l;intros.
  - simpl. solve_closedlvars assumption.
  - cbn.
    solve_closedlvars assumption.
    apply IHl.
Qed. 

Lemma closedlvars_field_storage : forall Vpm V_field v vs, 
 closed_wrt_lvars vs (field_storage Vpm V_field v).
Proof.
  intros. unfold field_storage. solve_closedlvars assumption. Qed.

Lemma closedlvars_AVertex: forall Gpm Vpm V_field pedge v vs, 
 closed_wrt_lvars vs (AVertex Gpm Vpm V_field pedge v).
Proof.
  intros. unfold AVertex. solve_closedlvars assumption. apply closedlvars_field_storage. Qed.

Lemma closedlvars_vertex_storage {E_Order : Edge_Order}:  forall Gpm Vpm G vf l vs, 
 closed_wrt_lvars vs (vertex_storage Gpm Vpm G vf l).
Proof.
  intros Gpm Vpm G vf l. induction l;intros.
  - simpl. solve_closedlvars assumption.
  - cbn.
    solve_closedlvars assumption.
    apply closedlvars_AVertex.
    apply closedlvars_edge_storage.
    apply IHl.
Qed. 

Lemma closedgvars_edge_storage: forall Gpm G l vs, 
 closed_wrt_gvars vs (edge_storage Gpm G l).
Proof.
  intros Gpm G l. induction l;intros.
  - simpl. solve_closedgvars assumption.
  - cbn.
    solve_closedgvars assumption.
    apply IHl.
Qed. 

Lemma closedgvars_edge_seg: forall Gpm G l pend vs, 
 closed_wrt_gvars vs (edge_seg Gpm G l pend).
Proof.
  intros Gpm G l. induction l;intros.
  - simpl. solve_closedgvars assumption.
  - cbn.
    solve_closedgvars assumption.
    apply IHl.
Qed. 

Lemma closedgvars_field_storage : forall Vpm V_field v vs, 
 closed_wrt_gvars vs (field_storage Vpm V_field v).
Proof.
  intros. unfold field_storage. solve_closedgvars assumption. Qed.

Lemma closedgvars_AVertex: forall Gpm Vpm V_field pedge v vs, 
 closed_wrt_gvars vs (AVertex Gpm Vpm V_field pedge v).
Proof.
  intros. unfold AVertex. solve_closedgvars assumption. apply closedgvars_field_storage. Qed.

Lemma closedgvars_vertex_storage {E_Order : Edge_Order}:  forall Gpm Vpm G vf l vs, 
 closed_wrt_gvars vs (vertex_storage Gpm Vpm G vf l).
Proof.
  intros Gpm Vpm G vf l. induction l;intros.
  - simpl. solve_closedgvars assumption.
  - cbn.
    solve_closedgvars assumption.
    apply closedgvars_AVertex.
    apply closedgvars_edge_storage.
    apply IHl.
Qed. 
  
End graph_subst_rules.


Ltac graph_asrt_simpl := 
    repeat progress ( match goal with 
    | |- context [subst_local ?x ?xv (field_storage ?vpm ?vf ?v) ] => erewrite (subst_local_fieldstorage vpm vf v x xv)
    | |- context [subst_local ?x ?xv (AVertex ?gpm ?vpm ?vf ?e ?v) ] => erewrite (subst_local_AVertex gpm vpm vf e v x xv)
    | |- context [subst_local ?x ?xv (edge_storage ?gpm ?G ?l) ] => erewrite (subst_local_edgestorage gpm G l x xv)
    | |- context [subst_local ?x ?xv (edge_seg ?gpm ?G ?l ?pend) ] => erewrite (subst_local_edgeseg gpm G l pend x xv)
    | |- context [subst_local ?x ?xv (vertex_storage ?gpm ?vpm ?G ?vf ?l) ] => erewrite (subst_local_vertexstorage gpm vpm G vf l x xv)
    | |- context [subst_local ?x ?xv (graphrep ?gpm ?vpm ?G ?vf) ] => erewrite (subst_local_graphrep gpm vpm G vf x xv)
    | |- context [subst_local ?x ?xv (rest_of_graph ?gpm ?vpm ?G ?vf ?v)] => erewrite (subst_local_rest_of_graph gpm vpm G vf v x xv)
    | |- context [subst_global ?x ?xv (field_storage ?vpm ?vf ?v) ] => erewrite (subst_global_fieldstorage vpm vf v x xv)
    | |- context [subst_global ?x ?xv (AVertex ?gpm ?vpm ?vf ?e ?v) ] => erewrite (subst_global_AVertex gpm vpm vf e v x xv)
    | |- context [subst_global ?x ?xv (edge_storage ?gpm ?G ?l) ] => erewrite (subst_global_edgestorage gpm G l x xv)
    | |- context [subst_global ?x ?xv (edge_seg ?gpm ?G ?l ?pend) ] => erewrite (subst_global_edgeseg gpm G l pend x xv)
    | |- context [subst_global ?x ?xv (vertex_storage ?gpm ?vpm ?G ?vf ?l) ] => erewrite (subst_global_vertexstorage gpm vpm G vf l x xv)
    | |- context [subst_global ?x ?xv (graphrep ?gpm ?vpm ?G ?vf) ] => erewrite (subst_global_graphrep gpm vpm G vf x xv)
    | |- context [subst_global ?x ?xv (rest_of_graph ?gpm ?vpm ?G ?vf ?v)] => erewrite (subst_global_rest_of_graph gpm vpm G vf v x xv)
    end).

Ltac graph_closedlvars := 
    match goal with 
    | |- closed_wrt_lvars ?vs (field_storage ?vpm ?vf ?v) => apply (closedlvars_field_storage vpm vf v vs)
    | |- closed_wrt_lvars ?vs (AVertex ?gpm ?vpm ?vf ?e ?v) => apply closedlvars_AVertex
    | |- closed_wrt_lvars ?vs (edge_storage ?gpm ?G ?l) => apply closedlvars_edge_storage
    | |- closed_wrt_lvars ?vs (edge_seg ?gpm ?G ?l ?pend) => apply closedlvars_edge_seg
    | |- closed_wrt_lvars ?vs (vertex_storage ?gpm ?vpm ?G ?vf ?l) => apply closedlvars_vertex_storage
    end.

Ltac graph_closedgvars := 
    match goal with 
    | |- closed_wrt_gvars ?vs (field_storage ?vpm ?vf ?v) => apply (closedgvars_field_storage vpm vf v vs)
    | |- closed_wrt_gvars ?vs (AVertex ?gpm ?vpm ?vf ?e ?v) => apply closedgvars_AVertex
    | |- closed_wrt_gvars ?vs (edge_storage ?gpm ?G ?l) => apply closedgvars_edge_storage
    | |- closed_wrt_gvars ?vs (edge_seg ?gpm ?G ?l ?pend) => apply closedgvars_edge_seg
    | |- closed_wrt_gvars ?vs (vertex_storage ?gpm ?vpm ?G ?vf ?l) => apply closedgvars_vertex_storage
    end.
    


