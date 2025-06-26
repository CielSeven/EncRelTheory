Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents List_lemma int_auto VMap ListLib.
From FP Require Import SetsFixedpoints.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp.



Local Open Scope Z_scope.
Local Open Scope sets_scope.


(**********************************************************************************)
(*                     imp err language's assertion                               *)
(*                                                                                *)
(**********************************************************************************)

Module impmodel <: sepLang.
  Definition state := state.
  Definition expr := (state -> Prop) .
  Definition join : (state -> state -> state -> Prop):= fun st1 st2 st3 => 
     mem_join (st_mem st1) (st_mem st2) (st_mem st3) /\ 
     (lenv st1) = (lenv st2) /\  (lenv st2) = (lenv st3) /\ 
     (genv st1) = (genv st2) /\  (genv st2) = (genv st3).
  Definition is_unit : (state -> Prop) := fun st => mem_empty (st_mem st).
End impmodel.

Module impmodelrules <: sepRuleSig impmodel.
  Include impmodel.
  Lemma unit_join : (forall n : state, exists u : state, is_unit u /\ join n u n) .
  Proof. unfold is_unit, join. intros [l  g m].
         exists (mk_lstate l g empty_mem). cbn. split;auto.
         solve_empmem. split;auto. solve_empmem. Qed.
  Lemma unit_spec : (forall n m u : state, is_unit u -> join n u m -> n = m) .
  Proof. unfold is_unit, join. intros [l g m] [l0 g0 m0] [l1 g1 m1] H H0.
        cbn in *. my_destruct H0. subst. solve_empmem. auto. Qed.
  Lemma join_comm : (forall m1 m2 m : state, join m1 m2 m -> join m2 m1 m) .
  Proof. unfold is_unit, join. intros [l g m] [l0 g0 m0] [l1 g1 m1] H.
        cbn in *. my_destruct H. subst. split;auto.  apply mem_join_comm. auto. Qed.
  Lemma join_assoc : (forall mx my mz mxy mxyz : state, join mx my mxy -> join mxy mz mxyz -> exists myz : state, join my mz myz /\ join mx myz mxyz) .
  Proof. unfold is_unit, join. intros [l g m] [l0 g0 m0] [l1 g1 m1] [l2 g2 m2] [l3 g3 m3] H H0.
  cbn in *. my_destruct H. my_destruct H0. subst. 
  pose proof mem_join_assoc2 H H0. my_destruct H1.
  exists (mk_lstate l3 g3 m4). cbn. split;auto.  Qed.

End impmodelrules.

Module imprulesinstance := sep_rules impmodel impmodelrules.
Module ImpRules := imprulesinstance.sepRules.


Local Open Scope asrt_scope. 
(* non-addressable variables *)
Definition gveq (x : var) (i : value) : ImpRules.expr := fun st => (genv st) x  = i. 
Definition lveq (x : var) (i : value) : ImpRules.expr := fun st => (lenv st) x  = i.  
Definition mstore (pi: addr) (i: value) (p: Perm.t) : ImpRules.expr := fun st => (st_mem st) = single_mem pi (i, p).
Definition aeval_expr (e: aexp) (i : value) : ImpRules.expr := fun st => (aeval e).(nrm) st i.
Definition beval_expr (e: bexp) (i : value) : ImpRules.expr := fun st => (beval e).(nrm) st i.
Definition isvalidptr (pi : addr) :=  pi > 0. 

Notation "'LV' x ↦ₗ v" := (lveq x v) (at level 25, no associativity).
Notation "'GV' x ↦ₗ v" := (gveq x v) (at level 25, no associativity).
Notation "'PV' x ↦ₗ v '$' p " := ( mstore x v p) (at level 25, no associativity).
Notation "'vPV' x ↦ₗ v '$' p " := (!! isvalidptr x && (PV x ↦ₗ v $ p)) (at level 25, no associativity).
Notation "'EV' e ↦ₗ v" := (aeval_expr e v) (at level 25, no associativity).
Notation "'BV' e ↦ₗ z" := (beval_expr e (z ,vint)) (at level 25, no associativity).

Notation "'LV' x '@' t ↦ₗ v" := (lveq x (v,t)) (at level 25, no associativity).
Notation "'GV' x '@' t ↦ₗ v" := (gveq x (v,t)) (at level 25, no associativity).
Notation "'PV' x '@' t ↦ₗ v '$' p " := ( mstore x (v,t) p) (at level 25, no associativity).
Notation "'vPV' x '@' t ↦ₗ v '$' p " := (!! isvalidptr x && (PV x ↦ₗ (v,t) $ p)) (at level 25, no associativity).
Notation "'EV' e '@' t ↦ₗ v" := (aeval_expr e (v,t)) (at level 25, no associativity).


Fixpoint Alvars (PL : list (var * value)) : ImpRules.expr :=
match PL with 
| nil =>  TT 
| (x, v) :: PL' => LV x ↦ₗ v && Alvars PL'
end. 

Ltac unfoldimpmodel :=
  try unfold ImpRules.derivable1;
  try unfold ImpRules.impp;
  try unfold ImpRules.andp;
  try unfold ImpRules.orp;
  try unfold ImpRules.exp;
  try unfold ImpRules.sepcon;
  (* try unfold ImpRules.emp; *)
  try unfold ImpRules.coq_prop;
  try unfold ImpRules.truep;
  try unfold ImpRules.logic_equiv.


Section asrtrules.

Import ImpRules.
Context (pm : Perm.t).


(**********************************************************************************)
(*                     more rules for imp assertion                               *)
(**********************************************************************************)



Lemma logic_equiv_andp_swap : forall x y (z: assertion), x && (y && z) --||-- y && (x && z).
Proof.
  intros.
  do 2 erewrite <- logic_equiv_andp_assoc.
  erewrite (logic_equiv_andp_comm x y).
  apply logic_equiv_refl.
Qed.


Lemma sepcon_andp_prop_equiv:
forall (P : assertion) (Q : Prop) (R : assertion),
P ** (!! Q && R) --||--  !! Q && P ** R .
Proof.
  intros.
  split.
  eapply sepcon_andp_prop1.
  eapply sepcon_andp_prop2_.
Qed.


Lemma logic_equiv_derivable1_andp: 
  forall q x x0 y (y0: assertion), x --||-- x0 -> y --||-- y0 -> (x0 && y0) |-- q  -> (x && y) |-- q.
Proof.
  intros.
  apply logic_equiv_derivable1 in H as [? ?].
  rewrite H;auto.
  apply logic_equiv_derivable1 in H0 as [? ?].
  rewrite H0.
  auto.
Qed.




Lemma sepcon_swap_logic_equiv : forall x y z, x ** (y ** z)  --||--  y ** (x ** z).
Proof.
  intros.
  do 2 erewrite sepcon_assoc_logic_equiv.
  rewrite (sepcon_comm_logic_equiv x y).
  apply logic_equiv_refl.
Qed.

Lemma sepcon_andp_lveq1:
  forall x v (P : assertion) (R : assertion),
  P ** (LV x ↦ₗ v && R) |-- LV x ↦ₗ v && P ** R.
Proof.
  unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.andp, lveq;intros.
  my_destruct H.
  destruct_st st. destruct_st x0. destruct_st x1.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H. subst.
  split;auto.
  exists (mk_lstate l g m0), (mk_lstate l g m1).
  cbn. 
  splits;eauto.
Qed.

Lemma sepcon_andp_lveq2:
  forall x v (P : assertion) (R : assertion),
  LV x ↦ₗ v && P ** R |-- P ** (LV x ↦ₗ v && R) .
Proof.
  unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.andp, lveq;intros.
  my_destruct H.
  destruct_st st. destruct_st x0. destruct_st x1.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H0. subst.
  exists (mk_lstate l g m0), (mk_lstate l g m1).
  cbn. 
  splits;eauto.
Qed.

Lemma sepcon_andp_Alvars1:
  forall  Q (P : assertion) (R : assertion),
  P ** (Alvars Q && R) |-- Alvars Q && P ** R.
Proof.
  induction Q;intros.
  - simpl.
    pose proof truep_andp_elim1 R.
    apply logic_equiv_derivable1 in H as [_ ?].
    rewrite H.
    pose proof truep_andp_elim1 (P ** R).
    apply logic_equiv_derivable1 in H0 as [? _].
    auto.
  - destruct a. 
    simpl.
    erewrite derivable1_andp_assoc.
    rewrite sepcon_andp_lveq1.
    erewrite IHQ.
    erewrite <- (logic_equiv_derivable1_2 (logic_equiv_andp_assoc _ (Alvars Q) _ )).
    apply derivable1_refl.
Qed.

Lemma sepcon_andp_Alvars2:
  forall  Q (P : assertion) (R : assertion),
  Alvars Q && P ** R |-- P ** (Alvars Q && R).
Proof.
  induction Q;intros.
  - simpl.
    rewrite (logic_equiv_derivable1_2 (truep_andp_elim1 (P ** R))).
    rewrite (logic_equiv_derivable1_1 (truep_andp_elim1 R)) at 1.
    apply derivable1_refl.
  - destruct a. 
    simpl.
    erewrite derivable1_andp_assoc.
    erewrite IHQ.
    rewrite sepcon_andp_lveq2.
    erewrite <- (logic_equiv_derivable1_2 (logic_equiv_andp_assoc _ (Alvars Q) _ )).
    apply derivable1_refl.
Qed.

Lemma sepcon_andp_lveq:
  forall x v (P : assertion) (R : assertion),
  P ** (LV x ↦ₗ v && R) --||-- LV x ↦ₗ v && P ** R.
Proof.
  intros;split.
  eapply sepcon_andp_lveq1.
  eapply sepcon_andp_lveq2.
Qed.

Lemma sepcon_andp_gveq:
  forall x v (P : assertion) (R : assertion),
  P ** (GV x ↦ₗ v && R) --||-- GV x ↦ₗ v && P ** R.
Proof.
  unfold basicasrt.sepcon,basicasrt.derivable1, basicasrt.andp, gveq.
  intros;split;intros.
  - my_destruct H.
    destruct_st st.  destruct_st x0. destruct_st x1.
    cbn in *. unfold impmodelrules.join in *. cbn in *.
    my_destruct H. subst.
    splits;eauto.
    exists (mk_lstate l g m0), (mk_lstate l g m1).
    cbn. splits;auto.
  - my_destruct H.
    destruct_st st.  destruct_st x0. destruct_st x1.
    cbn in *. unfold impmodelrules.join in *. cbn in *.
    my_destruct H0. subst.
    splits;eauto.
    exists (mk_lstate l g m0), (mk_lstate l g m1).
    cbn. splits;auto.
Qed.

Lemma sepcon_emp_equiv : 
  forall x, x ** emp --||-- x.
Proof.
  intros. eapply logic_equiv_derivable1. split.
  apply sepcon_emp_left.
  apply sepcon_emp_right.
Qed.

Lemma sepcon_cancel_res_emp : 
  forall P Q, emp |-- Q -> P |-- P ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono.
  apply derivable1_refl.
  auto.
Qed.

Lemma sepcon_cancel_res_emp_right : 
  forall P Q, Q |-- emp -> P ** Q |-- P.
Proof.
  intros.
  rewrite H.
  rewrite  sepcon_emp_equiv.
  apply derivable1_refl.
Qed.


Lemma sepcon_andp_lveqemp:
  forall x v (P : assertion),
  P ** (LV x ↦ₗ v && emp) --||-- P && LV x ↦ₗ v.
Proof.
  intros.
  rewrite sepcon_andp_lveq.
  rewrite sepcon_emp_equiv.
  rewrite logic_equiv_andp_comm.
  reflexivity.
Qed.

Lemma sepcon_andp_gveqemp:
  forall x v (P : assertion),
  P ** (GV x ↦ₗ v && emp) --||-- P && GV x ↦ₗ v.
Proof.
  intros.
  rewrite sepcon_andp_gveq.
  rewrite sepcon_emp_equiv.
  rewrite logic_equiv_andp_comm.
  reflexivity.
Qed.



Lemma sepcon_cancel_end : 
  forall P Q R, P |-- R -> emp |-- Q -> P |-- R ** Q.
Proof.
  intros.
  rewrite <- sepcon_emp_equiv at 1.
  apply derivable1_sepcon_mono ; auto.
Qed.



Definition subst_local  x i (p : assertion) : assertion :=
  fun st => p (mk_lstate (vmap_update (lenv st) x i) (genv st) (st_mem st)).
Definition subst_global  x i (p : assertion) : assertion :=
  fun st => p (mk_lstate (lenv st)  (vmap_update (genv st) x i) (st_mem st)).
Definition isptr (x : int64) := Int64.signed x >= 0.

Lemma  subst_local_and : 
  forall p q x n, subst_local x n (p && q) --||-- (subst_local x n p) && (subst_local x n q).
Proof.
  intros;unfold subst_local, basicasrt.andp, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;tauto.
Qed.

Lemma  subst_local_or : 
  forall p q x n, subst_local x n (p || q) --||-- (subst_local x n p) || (subst_local x n q).
Proof.
  intros;unfold subst_local, basicasrt.orp, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;tauto.
Qed.

Lemma  subst_local_sepcon : 
  forall p q x n, subst_local x n (p ** q) --||-- (subst_local x n p) ** (subst_local x n q).
Proof.
  intros;unfold subst_local, basicasrt.sepcon, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;unfold impmodelrules.join;simpl.
  split;intros.
  - my_destruct H. destruct_st x0. destruct_st x1. cbn in *. subst.
    exists (mk_lstate l g m0), (mk_lstate l g m1).
    cbn. splits;auto.
  - my_destruct H. destruct_st x0. destruct_st x1. cbn in *. subst.
    exists (mk_lstate (vmap_update l x n) g m0), (mk_lstate (vmap_update l x n) g m1).
    cbn. splits;auto.
Qed.

Lemma  subst_local_lveq  : 
  forall x n n', subst_local x n (LV x ↦ₗ n') --||-- !! (n = n').
Proof.
  intros;unfold subst_local, lveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. unfold vmap_update. rewrite var_eqb_refl;tauto.
Qed.

Lemma  subst_local_lvneq  : 
  forall x y n n', y <> x -> subst_local x n (LV y ↦ₗ n') --||-- LV y ↦ₗ n'.
Proof.
  intros;unfold subst_local, lveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. unfold vmap_update. 
  rewrite <- var_eqb_neq in H.
  rewrite H.
  tauto.
Qed.

Lemma  subst_local_pv  : 
  forall x n l v,  subst_local x n (PV l ↦ₗ v $ pm) --||-- PV l ↦ₗ v $ pm.
Proof.
  intros;unfold subst_local, mstore, basicasrt.coq_prop, basicasrt.logic_equiv, basicasrt.andp.
  intros. destruct_st st;simpl. tauto.
Qed.

Lemma  subst_local_gv  : 
  forall x y n n', subst_local x n (GV y ↦ₗ n') --||-- GV y ↦ₗ n'.
Proof.
  intros;unfold subst_local, lveq, gveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. 
  tauto.
Qed.

Lemma subst_local_pure : 
  forall (P: Prop) x n, subst_local x n (!! P) --||-- !! P.
Proof.
  intros;unfold subst_local, basicasrt.coq_prop, basicasrt.logic_equiv;tauto. Qed.


Lemma subst_local_derives : forall P Q x n, P |-- Q -> subst_local x n P |-- subst_local x n Q.
Proof.
  unfold subst_local, basicasrt.derivable1;intros.
  eapply H.
  eauto.
Qed. 

Lemma subst_local_coqprop : forall Q P x n, subst_local x n (!! Q && P) --||-- !! Q && subst_local x n P.
Proof.
  unfold subst_local, basicasrt.coq_prop, basicasrt.andp, basicasrt.derivable1;split;intros.
  eapply H.
  eapply H.
Qed.

Lemma  subst_local_emp  : 
  forall x n,  subst_local x n emp --||-- emp.
Proof.
  intros;unfold subst_local, basicasrt.emp, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. tauto.
Qed.

Lemma  subst_local_exp  : 
  forall {A:Type} x n (P: A -> assertion),  subst_local x n (EX v, P v) --||-- EX v, (subst_local x n (P v)).
Proof.
  intros;unfold subst_local, basicasrt.exp, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. tauto.
Qed.

Lemma  subst_global_and : 
  forall p q x n, subst_global x n (p && q) --||-- (subst_global x n p) && (subst_global x n q).
Proof.
  intros;unfold subst_global, basicasrt.andp, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;tauto.
Qed.

Lemma  subst_global_or : 
  forall p q x n, subst_global x n (p || q) --||-- (subst_global x n p) || (subst_global x n q).
Proof.
  intros;unfold subst_global, basicasrt.orp, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;tauto.
Qed.

Lemma  subst_global_sepcon : 
  forall p q x n, subst_global x n (p ** q) --||-- (subst_global x n p) ** (subst_global x n q).
Proof.
  intros;unfold subst_global, basicasrt.sepcon, basicasrt.logic_equiv.
  intros st. destruct_st st;simpl;unfold impmodelrules.join;simpl.
  split;intros.
  - my_destruct H. destruct_st x0. destruct_st x1. cbn in *. subst.
    exists (mk_lstate l g m0), (mk_lstate l g m1).
    cbn. splits;auto.
  - my_destruct H. destruct_st x0. destruct_st x1. cbn in *. subst.
    exists (mk_lstate l (vmap_update g x n) m0), (mk_lstate l (vmap_update g x n) m1).
    cbn. splits;auto.
Qed.

Lemma  subst_global_gveq  : 
  forall x n n', subst_global x n (GV x ↦ₗ n') --||-- !! (n = n').
Proof.
  intros;unfold subst_global, gveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. unfold vmap_update. rewrite var_eqb_refl;tauto.
Qed.

Lemma  subst_global_gvneq  : 
  forall x y n n', y <> x -> subst_global x n (GV y ↦ₗ n') --||-- GV y ↦ₗ n'.
Proof.
  intros;unfold subst_global, gveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. unfold vmap_update.
  rewrite <- var_eqb_neq in H.
  rewrite H.
  tauto.
Qed.

Lemma  subst_global_lv  : 
  forall x y n n',  subst_global x n (LV y ↦ₗ n') --||-- LV y ↦ₗ n'.
Proof.
  intros;unfold subst_global, gveq, lveq, basicasrt.coq_prop, basicasrt.logic_equiv.
  intros. destruct_st st;simpl.
  tauto.
Qed.

Lemma  subst_global_pv  : 
  forall x n l v,  subst_global x n (PV l ↦ₗ v $ pm) --||-- PV l ↦ₗ v $ pm.
Proof.
  intros;unfold subst_global, mstore, basicasrt.coq_prop, basicasrt.logic_equiv, basicasrt.andp.
  intros. destruct_st st;simpl. tauto.
Qed.

Lemma subst_global_pure : 
  forall (P: Prop) x n, subst_global x n (!! P) --||-- !! P.
Proof.
  intros;unfold subst_global, basicasrt.coq_prop, basicasrt.logic_equiv;tauto. Qed.
  
Lemma subst_global_derives : forall P Q x n, P |-- Q -> subst_global x n P |-- subst_global x n Q.
Proof.
  unfold subst_global, basicasrt.derivable1;intros.
  eapply H.
  eauto.
Qed. 

Lemma subst_global_coqprop : forall Q P x n, subst_global x n (!! Q && P) --||-- !! Q && subst_global x n P.
Proof.
  unfold subst_global, basicasrt.coq_prop, basicasrt.andp, basicasrt.derivable1;split;intros.
  eapply H.
  eapply H.
Qed.

Lemma  subst_global_emp  : 
  forall x n,  subst_global x n emp --||-- emp.
Proof.
  intros;unfold subst_global, basicasrt.emp, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. tauto.
Qed.

Lemma  subst_global_exp  : 
  forall {A:Type} x n (P: A -> assertion),  subst_global x n (EX v, P v) --||-- EX v, (subst_global x n (P v)).
Proof.
  intros;unfold subst_global, basicasrt.exp, basicasrt.logic_equiv.
  intros. destruct_st st;simpl. tauto.
Qed.



Definition valLt xv yv := (if zcmp Clt xv yv then  1 else  0).
Definition valLe xv yv := (if zcmp Cle xv yv then  1 else  0).

Definition valand x y := (if Z.eqb x ( 0) then  0 else 
                          (if Z.eqb y ( 0) then  0 else  1)  ).
Definition valeq x y := (if Z.eqb x y then 1 else 0 ).
Definition valneq x y := (if Z.eqb x y then  0 else 1 ).


Lemma aeval_expr_lvar_derives : forall x v, LV x ↦ₗ v |--  EV (EVarLocal x) ↦ₗ v.
Proof.
  unfold lveq, aeval_expr, basicasrt.derivable1; simpl; intros; auto. Qed.  

Lemma aeval_expr_gvar_derives : forall x v, GV x ↦ₗ v |--  EV (EVarGlobal x) ↦ₗ v.
Proof.
  unfold gveq, aeval_expr, basicasrt.derivable1; simpl; intros; auto. Qed.  

Lemma  aeval_expr_const_derives : forall z P, 
   Int64.min_signed <= z <= Int64.max_signed ->
  P |-- EV (ENum z) @ vint ↦ₗ z.
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl;intros. auto.
Qed.

Lemma  aeval_expr_null_derives : forall P, 
  P |-- EV (ENull) @ vptr ↦ₗ (0).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl;intros. auto.
Qed.

Lemma aeval_expr_EAdd_int_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  P |-- EV (EAdd e1 e2) @ vint ↦ₗ Int64.signed (Int64.repr (v1 + v2)).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.

Lemma aeval_expr_EAdd_ptr_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vptr ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  P |-- EV (EAdd e1 e2) @ vptr ↦ₗ (v1 + v2).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.

Lemma aeval_expr_ESub_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  P |-- EV (ESub e1 e2) @ vint ↦ₗ Int64.signed (Int64.repr (v1 - v2)).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.

Lemma aeval_expr_ESub_ptr_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vptr ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  P |-- EV (ESub e1 e2) @ vptr ↦ₗ (v1 - v2).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.

Lemma aeval_expr_EMul_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  P |-- EV (EMul e1 e2) @ vint ↦ₗ Int64.signed (Int64.repr (v1 * v2)).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.

Lemma aeval_expr_EDiv_derive : forall e1 e2 v1 v2  P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 ->
  (v2 <> 0) ->
  P |-- EV (EDiv e1 e2) @ vint ↦ₗ Int64.signed (Int64.repr (Z.div v1 v2)).
Proof.
  unfold aeval_expr, basicasrt.derivable1;simpl.
  intros.
  unfold arith_sem_nrm.
  do 2 eexists.
  splits;intuition eauto.
  unfold arith_compute. auto.
Qed.


Lemma beval_expr_eq_int_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 -> P |--  BV (EEq e1 e2) ↦ₗ valeq v1 v2.
Proof.
  unfold aeval_expr, beval_expr, valeq, basicasrt.derivable1;simpl;intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold eqneq_sem_nrm,cmp_compute_nrm, zcmp.
  do 3 eexists. splits;eauto. destruct (v1 =? v2); auto.
Qed.

Lemma beval_expr_eq_ptr_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vptr ↦ₗ v1 -> P |-- EV e2 @ vptr ↦ₗ v2 -> P |--  BV (EEq e1 e2) ↦ₗ valeq v1 v2.
Proof.
  unfold aeval_expr, beval_expr, valeq, basicasrt.derivable1;simpl;intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold eqneq_sem_nrm,cmp_compute_nrm, zcmp.
  do 3 eexists. splits;eauto. destruct (v1 =? v2); auto.
Qed.


Lemma beval_expr_neq_int_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 -> P |--  BV (ENe e1 e2) ↦ₗ valneq v1 v2.
Proof.
  unfold aeval_expr, beval_expr, valneq, basicasrt.derivable1;simpl;intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold eqneq_sem_nrm,cmp_compute_nrm, zcmp.
  do 3 eexists. splits;eauto. destruct (v1 =? v2); auto.
Qed.


Lemma beval_expr_neq_ptr_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vptr ↦ₗ v1 -> P |-- EV e2 @ vptr ↦ₗ v2 -> P |--  BV (ENe e1 e2) ↦ₗ valneq v1 v2.
Proof.
  unfold aeval_expr, beval_expr, valneq, basicasrt.derivable1;simpl;intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold eqneq_sem_nrm,cmp_compute_nrm, zcmp.
  do 3 eexists. splits;eauto. destruct (v1 =? v2); auto.
Qed.


Lemma beval_expr_lt_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 -> P |-- BV (ELt e1 e2) ↦ₗ (valLt v1 v2).
Proof.
  unfold lveq, basicasrt.andp, beval_expr, basicasrt.derivable1; simpl; intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold cmp_sem_nrm.
  exists v1, v2.
  splits;auto.
  unfold cmp_compute_nrm, valLt;simpl;auto. destruct (v1 <? v2);auto.
Qed.

Lemma beval_expr_le_derives : forall e1 e2 v1 v2 P, 
  P |-- EV e1 @ vint ↦ₗ v1 -> P |-- EV e2 @ vint ↦ₗ v2 -> P |-- BV (ELe e1 e2) ↦ₗ (valLe v1 v2).
Proof.
  unfold lveq, basicasrt.andp, beval_expr, basicasrt.derivable1; simpl; intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold cmp_sem_nrm.
  exists v1, v2.
  splits;auto.
  unfold cmp_compute_nrm, valLe;simpl;auto. destruct (v2 <? v1);auto.
Qed.


Lemma beval_expr_Eand_derives : forall e1 e2 v1 v2 P, 
  P |-- BV e1 ↦ₗ v1 -> P |-- BV e2 ↦ₗ v2 -> P |--  BV (EAnd e1 e2) ↦ₗ (valand v1 v2).
Proof.
  unfold beval_expr, valand, basicasrt.derivable1;simpl;intros.
  specialize (H _ H1). specialize (H0 _ H1).
  unfold and_sem_nrm, SC_and_compute_nrm.
  exists v1.
  split;auto.
  assert (v1  = 0 \/ v1 <> 0) as [? | ?] by tauto.
  - left. subst. eexists. split;eauto.
  - right.
    unfold NonSC_and, NonSC_compute_nrm.
    split.
    * unfold not;intros. apply H2. auto.
    * exists v2.
      assert (v2  = 0 \/ v2 <> 0) as [? | ?] by tauto.
      + exists 0.
        splits;auto.
        destruct (v1 =? 0) eqn:?; try lia.
        destruct (v2 =? 0) eqn:?; try lia.
        auto.
      + exists 1. 
        splits;auto.
        destruct (v1 =? 0) eqn:?; try lia.
        destruct (v2 =? 0) eqn:?; try lia.
        auto.
Qed.


Lemma EV_frm : forall P e v PF, P |-- EV e ↦ₗ v -> P ** PF |-- EV e ↦ₗ v.
Proof.
  unfold aeval_expr, basicasrt.coq_prop,  basicasrt.derivable1, basicasrt.andp,  basicasrt.sepcon.
  intros.
  destruct_st st.
  my_destruct H0. destruct_st x. destruct_st x0.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H0. subst.
  simpl in *.
  specialize (H _ H1).
  eapply mem_join_aeval_nrm with (m1 := m0);eauto.
Qed.

Arguments EV_frm [P] [e] [v].


Lemma BV_frm : forall P e v PF, P |-- BV e ↦ₗ v -> P ** PF |-- BV e ↦ₗ v.
Proof.
  unfold beval_expr, basicasrt.coq_prop, basicasrt.derivable1, basicasrt.andp, basicasrt.sepcon.
  intros.
  destruct_st st.
  my_destruct H0. destruct_st x. destruct_st x0.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H0. subst.
  simpl in *.
  specialize (H _ H1).
  eapply mem_join_beval_nrm with (m1 := m0);eauto.
Qed.

Arguments BV_frm [P] [e] [v].

Lemma PV_irrelevant_var : forall P e v pi vi, P |-- EV e ↦ₗ v -> PV pi ↦ₗ vi $ pm ** P |-- EV e ↦ₗ v .
Proof.
  unfold aeval_expr, mstore, isvalidptr, basicasrt.coq_prop, basicasrt.derivable1, basicasrt.andp, basicasrt.sepcon.
  intros.
  destruct_st st.
  my_destruct H0. destruct_st x. destruct_st x0.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H0. subst.
  simpl in *.
  specialize (H _ H2).
  simpl in *.
  eapply mem_join_aeval_nrm with (m1 := m1);eauto.
  apply mem_join_comm;eauto.
Qed.

Arguments PV_irrelevant_var [P] [e] [v].


Lemma PV_irrelevant_bvar : forall P e v pi vi, P |-- BV e ↦ₗ v -> PV pi ↦ₗ vi $ pm ** P |-- BV e ↦ₗ v.
Proof.
  unfold beval_expr, mstore, isvalidptr, basicasrt.coq_prop, basicasrt.derivable1, basicasrt.andp, basicasrt.sepcon.
  intros.
  destruct_st st.
  my_destruct H0. destruct_st x. destruct_st x0.
  cbn in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H0. subst.
  simpl in *.
  specialize (H _ H2).
  simpl in *.
  eapply mem_join_beval_nrm with (m1 := m1);eauto.
  apply mem_join_comm;eauto.
Qed.

Arguments PV_irrelevant_bvar [P] [e] [v].

Lemma vPV_isvalidptr : forall pi vi, vPV pi ↦ₗ vi $ pm |-- !! (pi > 0) && PV pi ↦ₗ vi $ pm.
Proof.
  unfold basicasrt.andp, basicasrt.coq_prop, isvalidptr, basicasrt.derivable1. intros. tauto. Qed.

Definition btrue (bv : Z) := bv <> 0.
Definition bfalse (bv : Z) := bv = 0.

Definition Abtrue (b : bexp) : assertion := fun st => exists bv, (beval b).(nrm) st (bv, vint) /\ bv <> 0.
Definition Abfalse (b : bexp) : assertion := fun st => exists bv, (beval b).(nrm) st (bv, vint) /\ bv = 0.

Lemma btrue_or_bfalse: forall bv, btrue bv \/ bfalse bv. 
Proof. unfold btrue, bfalse. intros. tauto. Qed.

Lemma btrue_valeq_iseq : forall p q, btrue (valeq p q) -> p = q.
Proof.
  intros.
  unfold btrue, valeq in H.
  destruct (p =? q) eqn:?;try lia.
Qed.

Lemma bfalse_valeq_neq : forall p q, bfalse (valeq p q) -> p <> q.
Proof.
  intros.
  unfold bfalse, valeq in H.
  destruct (p =? q) eqn:?;try lia.
Qed.

Lemma btrue_valneq_neq : forall p q, btrue (valneq p q) -> p <> q.
Proof.
  intros.
  unfold btrue, valneq in H.
  destruct (p =? q) eqn:?;try lia.
Qed.

Lemma bfalse_valneq_eq : forall p q, bfalse (valneq p q) -> p = q.
Proof.
  intros.
  unfold bfalse, valneq in H.
  destruct (p =? q) eqn:?;try lia.
Qed.

Lemma btrue_vallt_lt : forall x y, btrue (valLt x y) -> Z.ltb x y = true.
Proof.
  intros.
  unfold btrue, valLt, zcmp  in H.
  destruct ( Z.ltb x y) eqn:?;auto.
Qed.

Lemma bfalse_vallt_lt : forall x y, bfalse (valLt x y) -> Z.ltb x y = false.
Proof.
  intros.
  unfold bfalse, valLt, zcmp  in H.
  destruct ( Z.ltb x y) eqn:?;lia.
Qed.

Lemma btrue_valle_revltfalse : forall x y, btrue (valLe x y) ->  (Z.ltb y x) = false.
Proof.
  intros.
  unfold btrue, valLe, zcmp, negb  in *.
  destruct ( Z.ltb y x) eqn:?;lia.
Qed.

Lemma bfalse_valle_revlttrue : forall x y, bfalse (valLe x y) -> Z.ltb y x = true.
Proof.
  intros.
  unfold bfalse, valLe, zcmp, negb  in H.
  destruct ( Z.ltb y x) eqn:?;lia.
Qed.

Lemma btrue_valand_and : forall x y, btrue (valand x y) -> btrue x /\ btrue  y.
Proof.
  intros.
  unfold btrue, valand in *.
  destruct (x =? 0) eqn:?;auto.
  destruct (y =? 0) eqn:?;lia.
Qed.

Lemma bfalse_valand_or : forall x y, bfalse (valand x y) -> bfalse x \/  bfalse y.
Proof.
  intros.
  unfold bfalse, valand in *.
  destruct (x =? 0) eqn:?.
  left. lia.
  destruct (y =? 0) eqn:?;lia.
Qed.

Lemma Abtrue_derive_btrue :  forall P b bv, P |-- BV b ↦ₗ bv -> (Abtrue b) && P |-- !! (btrue bv) && P.
Proof.
  unfold beval_expr, basicasrt.andp, Abtrue, basicasrt.coq_prop, basicasrt.derivable1, btrue;intros.
  my_destruct H0.
  eapply H in H1 as ?.
  destruct_st st.
  pose proof mem_join_beval_nrm_eq (mem_join_emp2 m) H0 H3.
  inversion H4.
  subst x.
  tauto.
Qed.

Lemma Abfalse_derive_bfalse :  forall P b bv, P |-- BV b ↦ₗ bv -> (Abfalse b) && P |-- !! (bfalse bv) && P.
Proof.
  unfold beval_expr, basicasrt.andp, Abfalse, basicasrt.coq_prop, basicasrt.derivable1, bfalse;intros.
  my_destruct H0.
  eapply H in H1 as ?.
  destruct_st st.
  pose proof mem_join_beval_nrm_eq (mem_join_emp2 m) H0 H3.
  inversion H4.
  subst x.
  tauto.
Qed.

Fixpoint listrep (p : Z) (l : list Z) : ImpRules.expr :=
  match l with
  | nil => !! (p = 0) &&  ImpRules.emp
  | n :: l' => EX q, !! (n <= Int64.max_signed /\ n >= Int64.min_signed) &&  
                    vPV p @ vint ↦ₗ n $ pm  **  vPV (p + 1) @ vptr ↦ₗ q $ pm ** listrep q l'
  end.

Lemma listrep_nil : forall l, listrep 0 l |-- !! (l = nil) && listrep 0 nil.
Proof.
  intros.
  destruct l. 
  - erewrite coq_prop_andp_equiv.
    refine (derivable1_refl _).
    auto.
  - unfold basicasrt.derivable1.
    intros.
    simpl in H.
    destruct H.
    unfold basicasrt.sepcon, basicasrt.andp, basicasrt.coq_prop, isvalidptr in H.
    my_destruct H.
Qed.

Lemma listrep_neqnil : forall p l, p <> 0 -> listrep p l |--  !! (l <> nil) && listrep p l.
Proof.
  intros.
  destruct l. 
  - unfold basicasrt.derivable1.
    intros.
    simpl in H0.
    destruct H0.
    unfold basicasrt.sepcon, basicasrt.andp, basicasrt.coq_prop, isvalidptr in H0.
    subst p.
    contradiction.
  - erewrite coq_prop_andp_equiv.
    refine (derivable1_refl _).
    unfold not;intros hf; inversion hf.
Qed.

Lemma listrep_neqnil' : forall p l, bfalse (valeq p 0) -> listrep p l |--  !! (l <> nil) && listrep p l.
Proof.
  intros.
  destruct l. 
  - unfold basicasrt.derivable1.
    intros.
    simpl in H0.
    destruct H0.
    unfold basicasrt.sepcon, basicasrt.andp, basicasrt.coq_prop, isvalidptr in H0.
    subst p.
    unfold bfalse, valeq in H.
    rewrite Z.eqb_refl in H.
    lia.
  - erewrite coq_prop_andp_equiv.
    refine (derivable1_refl _).
    unfold not;intros hf; inversion hf.
Qed.

Lemma listrep_cons_rev : forall p1 q z l0,  
  !! (z <= Int64.max_signed /\ z >= Int64.min_signed) && 
  vPV p1 @ vint ↦ₗ z $ pm ** vPV (p1+1) @ vptr ↦ₗ q $ pm ** listrep q l0 |-- listrep p1 (z::l0).
Proof.
  intros.
  simpl.
  intros st H.
  exists q.
  auto.
Qed.

Lemma listrep_isvalidptr : forall p l, isvalidptr p -> listrep p l |--  !! (l <> nil) && listrep p l.
Proof.
  intros.
  destruct l. 
  - unfold basicasrt.derivable1.
    intros.
    simpl in H0.
    destruct H0.
    unfold basicasrt.sepcon, basicasrt.andp, basicasrt.coq_prop, isvalidptr in *.
    subst p.
    simpl.
    int auto.
  - erewrite coq_prop_andp_equiv.
    refine (derivable1_refl _).
    unfold not;intros hf; inversion hf.
Qed.

Lemma subst_local_listrep : forall l p x n, subst_local x n (listrep p l ) --||-- listrep p l.
Proof.
  induction l;intros.
  - simpl.
    rewrite subst_local_coqprop.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_local_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    erewrite ! subst_local_coqprop.
    erewrite ! subst_local_sepcon.
    erewrite ! subst_local_coqprop.
    erewrite ! subst_local_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma subst_global_listrep : forall l p x n, subst_global x n (listrep p l) --||-- listrep p l.
Proof.
  induction l;intros.
  - simpl.
    rewrite subst_global_coqprop.
    rewrite subst_global_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_global_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    erewrite ! subst_global_coqprop.
    erewrite ! subst_global_sepcon.
    erewrite ! subst_global_coqprop.
    erewrite ! subst_global_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Fixpoint listrep' (p : Z) (l : list Z) (tail : Z) : ImpRules.expr :=
  match l with
  | nil => !! (p = tail) &&  ImpRules.emp 
  | n :: l' => EX q,  !! (n <= Int64.max_signed /\ n >= Int64.min_signed) && 
                vPV p @ vint ↦ₗ (n) $ pm  **  vPV (p + 1) @ vptr ↦ₗ q $ pm ** listrep' q l' tail
  end.

Lemma listrep'_app_split :forall l1 l2 p1 p2, 
  listrep' p1 (l1 ++ l2) p2 --||-- EX p3, listrep' p1 l1 p3 ** listrep' p3 l2 p2.
Proof.
  induction l1;intros.
  - apply logic_equiv_derivable1;simpl;split.
    + eapply exp_right_exists. exists p1.
      erewrite coq_prop_andp_equiv;auto.
      rewrite sepcon_comm_logic_equiv.
      apply sepcon_emp_right.
    + eapply shallow_exp_left;intros.
      rewrite prop_andp_sepcon1.
      apply coq_prop_andp_left;intros.
      subst.
      rewrite sepcon_comm_logic_equiv.
      apply sepcon_emp_left.
  - simpl.
    apply logic_equiv_derivable1;simpl;split.
    * eapply shallow_exp_left;intros. 
      erewrite IHl1.
      rewrite sepcon_comm_logic_equiv. unfoldimpmodel.
      rewrite ex_logic_euiqv_sepcon.
      apply coq_prop_andp_left.
      intros.
      unfoldimpmodel.
      eapply shallow_exp_left;intros.
      apply exp_right_exists.
      exists x0.
      rewrite ex_logic_euiqv_sepcon.
      apply exp_right_exists.
      exists x.
      rewrite (coq_prop_andp_equiv (a <= Int64.max_signed /\ a >= Int64.min_signed));[ | auto].
      rewrite sepcon_comm_logic_equiv.
      rewrite <- ! sepcon_assoc_logic_equiv.
      refine (derivable1_refl _ ).
    * eapply shallow_exp_left;intros.
      rewrite ex_logic_euiqv_sepcon.
      eapply shallow_exp_left;intros.
      unfoldimpmodel.
      rewrite prop_andp_sepcon1.
      apply coq_prop_andp_left.
      intros.
      unfoldimpmodel.
      apply exp_right_exists.
      exists x0.
      rewrite (coq_prop_andp_equiv (a <= Int64.max_signed /\ a >= Int64.min_signed));[ | auto].
      rewrite (IHl1 l2).
      erewrite (sepcon_comm_logic_equiv _ (EX p3 : Z,
      listrep' x0 l1 p3 ** listrep' p3 l2 p2)). unfoldimpmodel.
      rewrite ex_logic_euiqv_sepcon.
      apply exp_right_exists.
      exists x.
      rewrite sepcon_swap_logic_equiv.
      rewrite (sepcon_comm_logic_equiv  (listrep' x0 l1 x ** listrep' x l2 p2)).
      rewrite sepcon_assoc_logic_equiv.
      rewrite sepcon_assoc_logic_equiv.
      reflexivity.
Qed.


Lemma  listrep_split: forall n p l, listrep p l --||-- EX q, listrep' p (firstn n l) q ** listrep q (skipn n l) .
Proof.
  induction n;intros.
  - apply logic_equiv_derivable1;simpl;split.
    + eapply exp_right_exists.
    exists p.
    erewrite coq_prop_andp_equiv;auto.
    rewrite sepcon_comm_logic_equiv.
    apply sepcon_emp_right.
    + eapply shallow_exp_left;intros.
      rewrite prop_andp_sepcon1.
      apply coq_prop_andp_left;intros.
      subst.
      rewrite sepcon_comm_logic_equiv.
      apply sepcon_emp_left.
  - destruct l.
    + apply logic_equiv_derivable1;simpl;split.
      * eapply exp_right_exists.
        exists 0.
        apply coq_prop_andp_left;intros.
        subst.
        rewrite prop_andp_sepcon1.
        rewrite sepcon_andp_prop_equiv.
        rewrite !coq_prop_andp_equiv;auto.
        apply sepcon_emp_right.
      * eapply shallow_exp_left;intros.
        rewrite prop_andp_sepcon1.
        rewrite sepcon_andp_prop_equiv.
        do 2 (apply coq_prop_andp_left;intros).
        subst.
        rewrite coq_prop_andp_equiv;auto.
        apply sepcon_emp_left.
    + simpl.
      eapply logic_equiv_derivable1;split.
      * eapply shallow_exp_left;intros.
        apply coq_prop_andp_left;intros.  
        erewrite IHn.
        rewrite sepcon_comm_logic_equiv. unfoldimpmodel.
        rewrite ex_logic_euiqv_sepcon.
        eapply shallow_exp_left;intros.
        apply exp_right_exists.
        exists x0.
        rewrite ex_logic_euiqv_sepcon.
        apply exp_right_exists.
        exists x.
        rewrite (coq_prop_andp_equiv (z <= Int64.max_signed /\ z >= Int64.min_signed));[ | auto].
        rewrite sepcon_swap_logic_equiv.
        rewrite (sepcon_comm_logic_equiv  (listrep' x (firstn n l) x0 ** listrep x0 (skipn n l))).
        rewrite sepcon_assoc_logic_equiv.
        rewrite sepcon_assoc_logic_equiv.
        reflexivity.
      * eapply shallow_exp_left;intros.
        rewrite ex_logic_euiqv_sepcon.
        eapply shallow_exp_left;intros.
        unfoldimpmodel.
        rewrite prop_andp_sepcon1.
        apply coq_prop_andp_left;intros.  
        apply exp_right_exists.
        exists x0.
        rewrite (coq_prop_andp_equiv (z <= Int64.max_signed /\ z >= Int64.min_signed));[ | auto].
        rewrite (IHn x0 l).
        rewrite (sepcon_comm_logic_equiv _ (EX q : Z, listrep' x0 (firstn n l) q ** listrep q (skipn n l))).
        unfoldimpmodel.
        rewrite ex_logic_euiqv_sepcon.
        apply exp_right_exists.
        exists x.
        rewrite (sepcon_comm_logic_equiv  (listrep' x0 (firstn n l) x ** listrep x (skipn n l))).
        rewrite sepcon_assoc_logic_equiv.
        reflexivity.
Qed.

Lemma  listrep_app: forall p l1 l2, listrep p (l1 ++ l2) --||-- EX q, listrep' p l1 q ** listrep q l2.
Proof.
  intros.
  eapply logic_equiv_trans.
  eapply listrep_split with (n := length l1).
  rewrite firstn_app.
  assert (length l1 - length l1 = O)%nat by lia.
  rewrite H.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_all.
  rewrite skipn_app.
  rewrite H.
  simpl.
  rewrite skipn_all.
  rewrite app_nil_l.
  apply logic_equiv_refl.
Qed.

Lemma listrep'_zerotail_equiv : forall l p, listrep' p l 0  --||--  listrep p l.
Proof.
  induction l;intros.
  - simpl.
  apply logic_equiv_refl.
  - simpl.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    rewrite IHl.
    apply logic_equiv_refl.
Qed.



Lemma subst_local_listrep' : forall l p q x n, subst_local x n (listrep' p l q) --||-- listrep' p l q.
Proof.
  induction l;intros.
  - simpl.
    rewrite subst_local_coqprop.
    rewrite subst_local_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_local_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    erewrite ! subst_local_coqprop.
    erewrite ! subst_local_sepcon.
    erewrite ! subst_local_coqprop.
    erewrite ! subst_local_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.

Lemma subst_global_listrep' : forall l p q x n, subst_global x n (listrep' p l q) --||-- listrep' p l q.
Proof.
  induction l;intros.
  - simpl.
    rewrite subst_global_coqprop.
    rewrite subst_global_emp.
    apply logic_equiv_refl.
  - simpl.
    rewrite subst_global_exp.
    eapply ex_logic_euiqv_elim_both.
    intro v.
    erewrite ! subst_global_coqprop.
    erewrite ! subst_global_sepcon.
    erewrite ! subst_global_coqprop.
    erewrite ! subst_global_pv.
    erewrite IHl.
    apply logic_equiv_refl.
Qed.


(**********************************************************************************)
(*                     closed modvars rules for imp assertion                     *)
(**********************************************************************************)
Definition closed_wrt_lvars (vs : var -> Prop) (P : assertion) : Prop :=
  forall l1 l2 g m,
  (forall x, vs x -> l1 x = l2 x) ->
  P (mk_lstate l1 g m) = P (mk_lstate l2 g m).

Definition closed_wrt_gvars  (vs : var -> Prop) (P : assertion) : Prop :=
  forall l g1 g2 m,
  (forall x, vs x -> g1 x = g2 x) ->
  P (mk_lstate l g1 m) = P (mk_lstate l g2 m).

Definition closed_wrt_modvars (c : com) (P : assertion) : Prop :=
  closed_wrt_lvars (fun x => modvars_local x c = false) P /\
  closed_wrt_gvars (fun x => modvars_global x c = false) P.

Lemma closedlvars_andp : forall  P Q vs,
  closed_wrt_lvars vs P -> closed_wrt_lvars vs Q ->
  closed_wrt_lvars vs (P && Q).
Proof.
  unfold closed_wrt_lvars, basicasrt.andp;intros.
  erewrite H;eauto. erewrite H0;eauto. 
Qed.

Lemma closedlvars_sepcon : forall  P Q vs,
  closed_wrt_lvars vs P -> closed_wrt_lvars vs Q ->
  closed_wrt_lvars vs (P ** Q).
Proof.
  unfold closed_wrt_lvars, basicasrt.sepcon, substmem; simpl;intros.
  apply propositional_extensionality.
  split;intros.
  - my_destruct H2. destruct_st x. destruct_st x0.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H2. subst.
    exists (mk_lstate l2 g m0), (mk_lstate l2 g m1).
    cbn. splits;eauto.
    erewrite <- H;eauto. erewrite <- H0;eauto.
  - my_destruct H2. destruct_st x. destruct_st x0.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H2. subst.
    exists (mk_lstate l1 g m0), (mk_lstate l1 g m1).
    cbn. splits;eauto.
    erewrite H;eauto. erewrite H0;eauto.
Qed.

Lemma closedlvars_exp : forall {A: Type} (P : A -> assertion) vs,
  (forall v, closed_wrt_lvars vs (P v)) ->
  closed_wrt_lvars vs (EX v, P v).
Proof.
  unfold closed_wrt_lvars, basicasrt.exp; simpl;intros.
  apply propositional_extensionality.
  split;intros.
  - my_destruct H1.
    exists x.
    erewrite <- H;eauto.
  - my_destruct H1.
    exists x.
    erewrite H;eauto.
Qed.

Lemma closedlvars_coqprop : forall (B: Prop) vs,
  closed_wrt_lvars vs (!! B).
Proof.
  unfold closed_wrt_lvars, basicasrt.coq_prop; simpl;intros. reflexivity. Qed.

Lemma closedlvars_GV : forall x v vs,
  closed_wrt_lvars vs (GV x ↦ₗ v).
Proof.
  unfold closed_wrt_lvars, gveq; simpl;intros. reflexivity. Qed.

Lemma closedlvars_emp : forall vs,
  closed_wrt_lvars vs (emp).
Proof.
  unfold closed_wrt_lvars, basicasrt.emp, st_mem;simpl;intros. reflexivity. Qed.

Lemma closedlvars_PV : forall x v vs,
  closed_wrt_lvars vs (PV x ↦ₗ v $ pm).
Proof.
  intros.
  unfold closed_wrt_lvars, mstore, st_mem;intros.
  reflexivity. 
Qed.

Lemma closedlvars_listrep : forall l p vs,
  closed_wrt_lvars vs (listrep p l).
Proof.
  induction l;intros.
  - simpl. apply closedlvars_andp.
    apply closedlvars_coqprop.
    apply closedlvars_emp.
  - simpl.
    apply closedlvars_exp.
    intros.
    apply closedlvars_andp.
    apply closedlvars_coqprop.
    apply closedlvars_sepcon.
    apply closedlvars_sepcon.
    apply closedlvars_andp.
    apply closedlvars_coqprop.
    apply closedlvars_PV.
    apply closedlvars_andp.
    apply closedlvars_coqprop.
    apply closedlvars_PV.
    apply IHl.
Qed.


Lemma closedgvars_andp : forall  P Q vs,
  closed_wrt_gvars vs P -> closed_wrt_gvars vs Q ->
  closed_wrt_gvars vs (P && Q).
Proof.
  unfold closed_wrt_gvars, basicasrt.andp;intros.
  erewrite H;eauto. erewrite H0;eauto. 
Qed.

Lemma closedgvars_sepcon : forall  P Q vs,
  closed_wrt_gvars vs P -> closed_wrt_gvars vs Q ->
  closed_wrt_gvars vs (P ** Q).
Proof.
  unfold closed_wrt_gvars, basicasrt.sepcon; simpl;intros.
  apply propositional_extensionality.
  split;intros.
  - my_destruct H2. destruct_st x. destruct_st x0.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H2. subst.
    exists (mk_lstate l g2 m0), (mk_lstate l g2 m1).
    cbn. splits;eauto.
    erewrite <- H;eauto. erewrite <- H0;eauto.
  - my_destruct H2. destruct_st x. destruct_st x0.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H2. subst.
    exists (mk_lstate l g1 m0), (mk_lstate l g1 m1).
    cbn. splits;eauto.
    erewrite H;eauto. erewrite H0;eauto.
Qed.


Lemma closedgvars_wand : forall  P Q vs,
  closed_wrt_gvars vs P -> closed_wrt_gvars vs Q ->
  closed_wrt_gvars vs (P -* Q).
Proof.
  unfold closed_wrt_gvars, basicasrt.wand; simpl;intros.
  apply propositional_extensionality.
  split;intros.
  - destruct_st st1. destruct_st st2.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H3. subst.
    specialize (H l1 g1 g0 m0  H1).
    specialize (H0 l1 g1 g0 m1 H1).
    rewrite <- H in H4.
    erewrite <- H0.
    eapply H2;eauto.
    cbn.
    split;auto.
  - destruct_st st1. destruct_st st2.
    unfold impmodelrules.join in *. cbn in *. 
    my_destruct H3. subst.
    specialize (H l1 g0 g2 m0  H1).
    specialize (H0 l1 g0 g2 m1 H1).
    rewrite H in H4.
    erewrite H0.
    eapply H2;eauto.
    cbn.
    split;auto.
Qed.


Lemma closedgvars_exp : forall {A: Type} (P : A -> assertion) vs,
  (forall v, closed_wrt_gvars vs (P v)) ->
  closed_wrt_gvars vs (EX v, P v).
Proof.
  unfold closed_wrt_gvars, basicasrt.exp; simpl;intros.
  apply propositional_extensionality.
  split;intros.
  - my_destruct H1.
    exists x.
    erewrite <- H;eauto.
  - my_destruct H1.
    exists x.
    erewrite H;eauto.
Qed.

Lemma closedgvars_coqprop : forall (B: Prop) vs,
  closed_wrt_gvars vs (!! B).
Proof.
  unfold closed_wrt_gvars, basicasrt.coq_prop; simpl;intros. reflexivity. Qed.

Lemma closedgvars_LV : forall x v vs,
  closed_wrt_gvars vs (LV x ↦ₗ v).
Proof.
  unfold closed_wrt_gvars, lveq; simpl;intros. reflexivity. Qed.

Lemma closedgvars_emp : forall vs,
  closed_wrt_gvars vs (emp).
Proof.
  unfold closed_wrt_gvars, basicasrt.emp, st_mem;simpl;intros. reflexivity. Qed.

Lemma closedgvars_PV : forall x v vs,
  closed_wrt_gvars vs (PV x ↦ₗ v $ pm).
Proof.
  intros.
  unfold closed_wrt_gvars, mstore, st_mem;intros.
  reflexivity. 
Qed.

Lemma closedgvars_listrep : forall l p vs,
  closed_wrt_gvars vs (listrep p l).
Proof.
  induction l;intros.
  - simpl. apply closedgvars_andp.
    apply closedgvars_coqprop.
    apply closedgvars_emp.
  - simpl.
    apply closedgvars_exp.
    intros.
    apply closedgvars_andp.
    apply closedgvars_coqprop.
    apply closedgvars_sepcon.
    apply closedgvars_sepcon.
    apply closedgvars_andp.
    apply closedgvars_coqprop.
    apply closedgvars_PV.
    apply closedgvars_andp.
    apply closedgvars_coqprop.
    apply closedgvars_PV.
    apply IHl.
Qed.


(**********************************************************************************)
(*                     permission rules for imp assertion                         *)
(**********************************************************************************)
Lemma  PV_perm_split_equiv: forall pm1 pm2 pm pi vi , 
  Perm.join pm1 pm2 pm ->
  PV pi ↦ₗ vi $ pm1 ** PV pi ↦ₗ vi $ pm2 --||-- PV pi ↦ₗ vi $ pm.
Proof.
  intros. unfold basicasrt.logic_equiv, basicasrt.sepcon, mstore, basicasrt.coq_prop, basicasrt.andp; simpl;split;intros.
  - my_destruct H0. destruct_st x. destruct_st x0.
    unfold impmodelrules.join in *. cbn in *.
    my_destruct H0. subst.
    cbn. splits;eauto. 
    eapply mem_join_eq;eauto.
    eapply mem_join_two_single;eauto.
  - destruct_st st.
    unfold impmodelrules.join in *. cbn in *.
    exists (mk_lstate l g (single_mem pi (vi, pm1))),  (mk_lstate l g (single_mem pi (vi, pm2))).
    cbn.
    splits;eauto. subst m.
    eapply mem_join_two_single;eauto.
Qed.


Definition wand_env (Q1 : assertion) (Q2 : assertion) : assertion :=
  ALL l g, (fun  st' => Q1 (mk_lstate l g (st_mem st'))) -* 
                        (fun  st' => Q2 (mk_lstate l g (st_mem st'))).

Local Notation "x ₑ-* y" := (wand_env x y) (at level 45, right associativity) : asrt_scope.

Lemma derivable1_wandenv_sepcon_modus_ponens1: forall x y,
  (x ₑ-* y) ** x |-- y.
Proof.
  intros.
  unfold wand_env, basicasrt.allp, basicasrt.wand, basicasrt.sepcon, basicasrt.derivable1.
  intros.
  my_destruct H.
  destruct_st x0; destruct_st x1; destruct_st st.
  simpl in *. unfold impmodelrules.join in *. cbn in *.
  my_destruct H.
  subst.
  specialize (H0 l1 g1 (mk_lstate l1 g1 m0)  (mk_lstate l1 g1 m1)).
  simpl in *.
  apply H0;auto.
Qed.

Lemma derivable1_wandenv_sepcon_modus_ponens2:
  forall x y, x ** (x ₑ-* y) |-- y.
Proof.
  intros.
  rewrite (derivable1_sepcon_comm x (x ₑ-* y)).
  apply derivable1_wandenv_sepcon_modus_ponens1.
Qed.


Lemma closed_wrt_gvars_wandenv : forall f x y,
  closed_wrt_gvars f (x ₑ-* y).
Proof.
  intros.
  unfold closed_wrt_gvars, wand_env, basicasrt.allp, basicasrt.wand.
  cbn. unfold impmodelrules.join. simpl.
  intros. clear H.
  apply propositional_extensionality;split;intros.
  - destruct_st st1. destruct_st st2.
    simpl in H0. my_destruct H0;subst.
    specialize (H x0 x1 (mk_lstate l1 g1 m0) (mk_lstate l1 g1 m1)).
    simpl in H.
    apply H;auto.
  - destruct_st st1. destruct_st st2.
    simpl in H0. my_destruct H0;subst.
    specialize (H x0 x1 (mk_lstate l1 g2 m0) (mk_lstate l1 g2 m1)).
    simpl in H.
    apply H;auto.
Qed.    


Lemma env_derivable1: forall (P Q : assertion), 
  P |-- Q ->
  (forall (l : local_env) (g : global_env), 
  (fun  (st': local_cstate) => P (mk_lstate l g (st_mem st'))) |-- (fun  st' => Q (mk_lstate l g (st_mem st')))).
Proof.
  unfold basicasrt.derivable1.
  intros.
  destruct_st st.
  simpl in *.
  apply H.
  auto.
Qed.

End asrtrules.


Arguments PV_irrelevant_var [pm] [P] [e] [v].
Arguments PV_irrelevant_bvar [pm] [P] [e] [v].


Notation "➀" := (Perm.fullperm).

Notation "x ₑ-* y" := (wand_env x y) (at level 45, right associativity) : asrt_scope.


Module NormalImpHoareRules.
Import NormalContextualImp.
Import ImpRules.



Lemma hoare_conseq_pre : forall Delta c P P' Q,
  P |-- P' ->
  Delta ⊢ {{P'}} c {{Q}} -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P' Q Q); auto.
  apply derivable1_refl.
Qed.

Lemma hoare_conseq_post : forall Delta c P Q Q',
  Q' |-- Q ->
  Delta ⊢ {{P}} c {{Q'}} -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P Q Q'); auto.
  apply derivable1_refl.
Qed.

Lemma hoare_conseq_post' : forall Delta c P Q Q',
  Delta ⊢ {{P}} c {{Q'}} ->
  Q' |-- Q -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. eapply hoare_conseq_post;eauto.
Qed.

Lemma hoare_exists_l : forall Delta c (A : Type) (P : A -> assertion) P',
  (forall v : A, Delta ⊢ {{P v}} c {{P'}}) ->
  Delta ⊢ {{EX y, P y}} c {{P'}}.
Proof.
  unfold  valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * HT.
  intros * HDelta * Hm1 HP.
  destruct HP.
  specialize (HT x _ HDelta _ _ _ Hm1 H) as HT.
  auto.
Qed.

Lemma hoare_exists_r : forall Delta c (A : Type) (v : A) P (P' : A -> assertion),
  Delta ⊢ {{P}} c {{P' v}} ->
  Delta ⊢ {{P}} c {{EX y, P' y}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * HT.
  intros * HDelta * Hm1 HP.
  specialize (HT _ HDelta _ _ _ Hm1 HP) as  HT. 
  intros * Hev.
  specialize (HT _ Hev)as [m2 ?]. exists m2. intuition. exists v. auto.
Qed.


Lemma hoare_frame : forall Delta c (A : Type) P (P' : A -> assertion) PF,
  closed_wrt_modvars c PF ->
  Delta ⊢ {{P}} c {{EX v, P' v}} ->
  Delta ⊢ {{P ** PF}} c {{EX v, (P' v ** PF)}}.
Proof.
  unfold  valid_contextualtriple_nrm, valid_triple_nrm. intros * HCP HT.
  intros * HDelta * Hm1 HP. 
  destruct_st st1.
  destruct HP as [st0 [stf  [? [? ?] ] ] ].
  destruct_st st0.
  destruct_st stf.
  cbn in *. unfold impmodelrules.join in H. cbn in H. my_destruct H. subst. 
  
  destruct (mem_join_assoc2 H Hm1) as [mframe' [? ?] ].
  specialize (HT _ HDelta (mk_lstate l g m) m0 mframe' H3 H0) as HT.

  intros * Hev.
  specialize (HT st2 Hev) as [m2' [? ?] ].
  destruct H5 as [v ?].
  destruct (mem_join_assoc1 H2 H4) as [m3 [? ?] ].
  exists m3. split; auto.
  exists v.
  destruct_st st2. cbn in *. 
  exists (mk_lstate l0 g0 m2'), (mk_lstate l0 g0 m2). repeat split; auto.
  destruct HCP as [HCPL HCPG]. destruct (modvars_spec _ _ _ _ Hev) as [HML HMG].
  unfold substmem.
  rewrite <- (HCPL l l0 g0); auto.
  rewrite <- (HCPG l g g0); auto.
Qed.

Lemma hoare_frame' : forall Delta c  P Q PF,
  closed_wrt_modvars c PF ->
  Delta ⊢ {{P}} c {{Q}} ->
  Delta ⊢ {{P ** PF}} c {{Q ** PF}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. intros * HCP HT.
  intros * HDelta * Hm1 HP. 
  destruct HP as [st0 [stf [? [? ?] ] ] ].
  destruct_st st1.
  destruct_st st0.
  destruct_st stf.
  cbn in *. unfold impmodelrules.join in H. cbn in H. my_destruct H. subst. 
  destruct (mem_join_assoc2 H Hm1) as [mframe' [? ?] ].
  specialize (HT _ HDelta (mk_lstate l g m) m0 mframe' H3 H0) as HT.

  intros * Hev.
  specialize (HT st2 Hev) as [m2' [? ?] ].
  destruct (mem_join_assoc1 H2 H4) as [m3 [? ?] ].
  exists m3. split; auto.
  destruct_st st2. cbn in *. 
  exists (mk_lstate l0 g0 m2'), (mk_lstate l0 g0 m2). repeat split; auto.
  destruct HCP as [HCPL HCPG]. destruct (modvars_spec _ _ _ _ Hev) as [HML HMG].
  unfold substmem.
  rewrite <- (HCPL l l0 g0); auto.
  rewrite <- (HCPG l g g0); auto.
Qed.

Lemma hoare_pure : forall Delta c (P0 : Prop) P Q,
  (P0 -> Delta ⊢ {{P}} c {{Q}}) ->
  Delta ⊢ {{!! P0 && P}} c {{Q}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * HT.
  intros * HDelta * Hm1 HP .
  unfold coq_prop in HP. destruct HP as [? HP].
  specialize (HT H _ HDelta _ _ _ Hm1 HP) as ?;auto.
Qed.

Lemma hoare_pure_r : forall Delta c (P0 : Prop) P Q,
  P0 ->
  Delta ⊢ {{P}} c {{Q}} ->
  Delta ⊢ {{P}} c {{!! P0 && Q}}.
Proof.
  intros.
  eapply hoare_conseq_post'.
  eapply H0.
  erewrite  coq_prop_andp_equiv;eauto.
  apply derivable1_refl.
Qed.

Lemma hoare_or : forall Delta c P1 P2 Q,
  Delta ⊢ {{P1}} c {{Q}} ->
  Delta ⊢ {{P2}} c {{Q}} ->
  Delta ⊢ {{orp P1 P2}} c {{Q}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * HT1 HT2.
  intros * HDelta * Hm1 HP.
  unfold orp in *.
  destruct HP .
  - 
    specialize (HT1 _ HDelta _ _ _  Hm1 H) as ?;auto.
  - specialize (HT2 _ HDelta _ _ _  Hm1 H) as ?;auto.
Qed.

Lemma hoare_Skip : forall Delta P,
  Delta ⊢ {{P}} CSkip {{P}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl.
  intros * HDelta * Hm1 HP. 

  intros * Hev.
  sets_unfold in Hev. subst.
  exists m1; split; auto.
Qed.

Lemma hoare_AsgnLocal : forall Δ (x : var) e (v : value) (P : assertion),
  P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ P }} 
      CAsgnLocal x e
      {{EX v', LV x ↦ₗ v && (subst_local x v' P)}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros * H callees HDelta * Hm1 HP.
  specialize (H _ HP).
  destruct_st st1.
  unfold aeval_expr in H.
  simpl in *.

  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H.
  subst v.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H3.
  apply fun_ext1 in H2.
  subst m0 g0.
  exists m1;splits;auto.
  exists (l x).
  unfold subst_local;unfold lveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_AsgnLocal' : forall Δ (x : var) e (v v' : value) (P : assertion),
  LV x ↦ₗ v' && P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ LV x ↦ₗ v' && P }} 
      CAsgnLocal x e
      {{ LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  intros * He.
  eapply hoare_conseq_post.
  2:{ apply hoare_AsgnLocal with (v := v).
      auto. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_local_and |  ].
  assert ((subst_local x v'' (LV x ↦ₗ v') && subst_local x v'' P) |-- subst_local x v' P).
  { pose proof subst_local_lveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.
 
Lemma hoare_AsgnGlobal : forall Δ (x : var) e (v : value) (P : assertion),
  P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ P }} 
      CAsgnGlobal x e
      {{EX v', GV x ↦ₗ v && (subst_global x v' P)}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros * H callees HDelta * Hm1 HP.
  specialize (H _ HP).
  destruct_st st1.
  unfold aeval_expr in H.
  simpl in *.
  
  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H.
  subst v.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H3.
  apply fun_ext1 in H2.
  subst m0 l0.
  exists m1;splits;auto.
  exists (g x).
  unfold subst_global;unfold gveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_AsgnGlobal' : forall Δ (x : var) e (v v' : value) (P : assertion),
  GV x ↦ₗ v' && P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ GV x ↦ₗ v' && P }} 
      CAsgnGlobal x e
      {{ GV x ↦ₗ v && (subst_global x v' P)}} .
Proof.
  intros * He.
  eapply hoare_conseq_post.
  2:{ apply hoare_AsgnGlobal with (v := v).
      auto. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_global_and |  ].
  assert ((subst_global x v'' (GV x ↦ₗ v') && subst_global x v'' P) |-- subst_global x v' P).
  { pose proof subst_global_gveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.

(* load sem is loading a value into a local var  *)
Lemma hoare_LoadFull : forall Δ x e ve v pm P,
  P |--  EV e @ vptr ↦ₗ ve ->
  P |--  !! isvalidptr ve && PV ve ↦ₗ v $ pm ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x e
      {{EX v', LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros * H0 H1 callees HDelta * Hm1 HP.
  specialize (H0 _ HP).
  destruct_st st1.
  unfold aeval_expr in H0.
  simpl in *.
  
  unfold load_sem_nrm;sets_unfold;  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H0.
  inversion H7.
  subst x0.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H5, H6.
  subst m0 g0.
  specialize (H1 _ HP) as [? ?].
  unfold mstore, isvalidptr, basicasrt.coq_prop, basicasrt.andp,  basicasrt.sepcon,  basicasrt.truep in *;simpl in *.
  my_destruct H5. destruct_st x0. destruct_st x1. cbn in *. unfold impmodelrules.join in H5. cbn in *.
  my_destruct H5. subst.
  simpl in *.
  clear H7.
  pose proof mem_join_Some1 _ _ _ _ _ _ H5  (single_mem_get_eq ve (v, pm)) as [? [? ?]].
  pose proof mem_join_Some_eq_l Hm1 H6 H2.
  destruct b. simpl in H9.
  subst v.
  exists m1;splits;auto.
  exists (l x).
  unfold subst_local;unfold lveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_LoadFull' : forall Δ x e ve v v' pm P ,
  LV x ↦ₗ v' && P |--  EV e @ vptr ↦ₗ ve ->
  P |--  !! isvalidptr ve && PV ve ↦ₗ v $ pm ** TT  ->
  Δ ⊢ {{ LV x ↦ₗ v' && P }} 
      CLoad x e
      {{LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  intros *  He Hp.
  eapply hoare_conseq_post.
  2:{ eapply hoare_LoadFull with (v := v);
      eauto.
      eapply derivable1_trans.
      apply derivable1_andp_elim2.
      exact Hp. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_local_and |  ].
  assert ((subst_local x v'' (LV x ↦ₗ v') && subst_local x v'' P) |-- subst_local x v' P).
  { pose proof subst_local_lveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.

Lemma hoare_Store : forall Δ e1 e2 v0 v1 v2 P ,
  isvalidptr v1 ->
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P |-- EV e2 ↦ₗ v2 ->
  Δ ⊢ {{ PV v1 ↦ₗ v0 $ ➀ ** P }} 
      CStore e1 e2
      {{ PV v1 ↦ₗ v2 $ ➀ ** P }} .
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros * Hvalidp He1 He2.
  intros callees HDelta * Hm1 HP.
  pose proof (PV_irrelevant_var v1 v0 He1) _ HP.
  pose proof (PV_irrelevant_var v1 v0 He2) _ HP.
  unfold aeval_expr in H, H0; destruct_st st1;simpl in *.

  intros * Hev.
  simpl in Hev.
  unfold asgn_deref_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H5, H6.
  subst l0 g0.
  exists (mem_update m1 x v).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H. inversion H5. clear H5. subst v1. 
  pose proof mem_join_aeval_nrm_eq Hm1 H1 H0. inversion H5. clear H5. subst v2. 
  unfold mstore, basicasrt.andp, isvalidptr, coq_prop in HP.
  destruct HP.
  my_destruct H5.
  destruct_st x0. destruct_st x1. cbn in *. unfold impmodelrules.join in H5. cbn in *.
  my_destruct H5. subst l1 l0 g1 g0.
  split.
  + assert (m2 x = Some  (v0, ➀)).
    { subst. apply single_mem_get_eq. }
    pose proof mem_join_Some1 m2 m3 m1 x v0 ➀ H5 H9 as [? [? ?]].
    apply Perm_full_leb_eq in H11. subst x0.
    pose proof mem_join_Some1 _ _ _  _ v0 ➀ Hm1 H10 as [? [? ?]].
    apply Perm_full_leb_eq in H12. subst x0.
    erewrite (mem_update_unfold m m0 x (v0, ➀));eauto.
    2:{ unfold writable_m. rewrite H4. apply writable_perm_eq_full. reflexivity.   }
    subst. simpl.
    apply mem_join_mem_update_l;auto.
    unfold writable_m.
    rewrite H10.
    apply writable_perm_eq_full. reflexivity. 
  + exists (mk_lstate l g (mem_update m2 x v)), (mk_lstate l g m3).
    simpl. unfold impmodelrules.join. simpl.
    splits;auto. 
    ++ subst.
       apply mem_join_mem_update_l;auto.
       unfold writable_m.
       rewrite single_mem_get_eq.
       apply writable_perm_eq_full. reflexivity. 
    ++ unfold substmem, mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop;simpl.
       splits;auto.
       subst m2.
       apply mem_update_single_eq.
       simpl.
       apply writable_perm_eq_full. reflexivity. 
Qed.


Lemma hoare_Store' : forall Δ e1 e2 v0 v1 v2 P p,
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P |-- EV e2 ↦ₗ v2 ->
  P |-- !! isvalidptr v1 ->
  P --||-- PV v1 ↦ₗ v0 $ ➀ ** p ->
  Δ ⊢ {{ P }} 
      CStore e1 e2
      {{ PV v1 ↦ₗ v2 $ ➀** p }} .
Proof.
  intros * He1 He2 Hvalidp H.
  eapply hoare_conseq_pre.
  rewrite H.
  apply derivable1_refl.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros callees HDelta * Hm1 HP.
  rewrite H in Hvalidp, He1, He2.
  specialize (Hvalidp _ HP). unfold basicasrt.coq_prop in Hvalidp.
  specialize (He1 _ HP).
  specialize (He2 _ HP).
  unfold aeval_expr in He1, He2; destruct_st st1;simpl in *.
  
  intros * Hev.
  simpl in Hev.
  unfold asgn_deref_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H4, H5.
  subst l0 g0.
  exists (mem_update m1 x v).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1. inversion H4. clear H4. subst v1. 
  pose proof mem_join_aeval_nrm_eq Hm1 H0 He2. subst v2.
  unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
  destruct HP.
  my_destruct H4. destruct_st x0. destruct_st x1. simpl in H4. unfold impmodelrules.join in H4.
  cbn in H4. my_destruct H4. subst g1 g0 l1 l0.
  cbn in *.
  split.
  + assert (m2 x = Some  (v0, ➀)).
    { subst. apply single_mem_get_eq. }
    pose proof mem_join_Some1 _ _ _  x v0 ➀ H4 H8 as [? [? ?]].
    apply Perm_full_leb_eq in H10. subst x0.
    pose proof mem_join_Some1 _ _ _  x v0 ➀ Hm1 H9 as [? [? ?]].
    apply Perm_full_leb_eq in H11. subst x0.
    erewrite (mem_update_unfold m m0 x (v0, ➀));eauto.
    2:{ unfold writable_m. rewrite H3. apply writable_perm_eq_full. reflexivity.   }
    subst. simpl.
    apply mem_join_mem_update_l;auto.
    unfold writable_m.
    rewrite H9.
    apply writable_perm_eq_full. reflexivity. 
  + exists (mk_lstate l g (mem_update m2 x v)), (mk_lstate l g m3).
    simpl. unfold impmodelrules.join. simpl.
    splits;auto. 
    ++ subst.
       apply mem_join_mem_update_l;auto.
       unfold writable_m.
       rewrite single_mem_get_eq.
       apply writable_perm_eq_full. reflexivity. 
    ++ unfold substmem, mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop;simpl.
       splits;auto.
       subst m2.
       apply mem_update_single_eq.
       simpl.
       apply writable_perm_eq_full. reflexivity. 
Qed.


(* Lemma hoare_Store'' : forall Δ e1 e2 v0 v1 v2 PL P ,
  Alvars PL |-- EV e1 ↦ₗ v1 ->
  Alvars PL |-- EV e2 ↦ₗ v2 ->
  Δ ⊢ {{ Alvars PL && PV v1 ↦ₗ v0 ** P }} 
      CStore e1 e2
      {{ Alvars PL && PV v1 ↦ₗ v2 ** P }} .
Proof.
  intros * He1 He2.
  eapply hoare_conseq with (P' := PV v1 ↦ₗ v0 ** (Alvars PL && P) ).
  3:{ apply hoare_Store with (v0 := v0) (v1 := v1) (v2 := v2).
      - eapply derivable1_trans.
        apply derivable1_andp_elim1.
        auto.
      - eapply derivable1_trans.
        apply derivable1_andp_elim1.
        auto. }
  - erewrite sepcon_andp_Alvars2.
    apply derivable1_refl.
  - erewrite sepcon_andp_Alvars1.
    apply derivable1_refl.
Qed. *)

Lemma hoare_Call : forall Delta f fspec (w : fspec.(FS_With)),
  In (f, fspec) Delta ->
  Delta ⊢ {{FS_Pre fspec w}} 
          CCall f 
          {{FS_Post fspec w}}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * Hf.
  intros * HDelta * Hm1 HP.
  specialize (HDelta _ _ Hf st1 _ _ w Hm1 HP) as  Hnrm.

  intros * Hev.
  destruct Hev.
  destruct_st st1. destruct_st st2.
  cbn in *.
  subst l0.
  specialize (Hnrm (mk_gstate g0 m0) H).
  eapply Hnrm.
Qed.


Lemma hoare_Call_frm : forall Delta f fspec (w : fspec.(FS_With)) PF,
  closed_wrt_modvars (CCall f) PF ->
  In (f, fspec) Delta ->
  Delta ⊢ {{(FS_Pre fspec w) ** PF}}  
          CCall f 
          {{(FS_Post fspec w)** PF}}. 
Proof.
  intros.
  eapply hoare_frame';eauto.
  eapply hoare_Call;eauto.
Qed.

Lemma funcall_closedlvars  : forall f P, 
closed_wrt_lvars (fun x => modvars_local x (CCall f) = false) P.
Proof.
  unfold closed_wrt_lvars;simpl;intros.
  assert (l1 = l2). { apply fun_ext1. intros. eapply H. auto. }
  rewrite H0.
  reflexivity.
Qed.


Lemma hoare_Call_frm' : forall Delta f fspec P Q (w : fspec.(FS_With)) PF,
  In (f, fspec) Delta ->
  P |-- (FS_Pre fspec w) ** PF ->
  (FS_Post fspec w)** PF |-- Q ->
  closed_wrt_gvars (fun x => modvars_global x (CCall f)  = false) PF ->
  Delta ⊢ {{P}} CCall f {{Q}}. 
Proof.
  intros.
  eapply hoare_conseq;eauto.
  eapply hoare_Call_frm;eauto.
  split;auto.
  apply funcall_closedlvars.
Qed.

Lemma hoare_Call_specderive : forall Delta f fspec fspec0,
  In (f, fspec) Delta ->
  (forall (w0 : fspec0.(FS_With)),
  FS_Pre fspec0 w0 |-- EX w, FS_Pre fspec w ** (FS_Post fspec w  ₑ-* FS_Post fspec0 w0)) ->
  forall w0, 
  Delta ⊢ {{FS_Pre fspec0 w0}} 
          CCall f 
          {{FS_Post fspec0 w0}}.
Proof.
  intros.
  specialize (H0 w0).
  eapply hoare_conseq_pre.
  exact H0.
  eapply hoare_exists_l.
  intros w.
  eapply hoare_conseq_post'.
  eapply hoare_Call_frm;auto.
  unfold closed_wrt_modvars.
  split. apply funcall_closedlvars.
  cbn.
  apply closed_wrt_gvars_wandenv.
  apply derivable1_wandenv_sepcon_modus_ponens2.
Qed.

Lemma hoare_Call_specderive_frm : forall Delta f fspec fspec0,
  In (f, fspec) Delta ->
  (forall (w0 : fspec0.(FS_With)),
  FS_Pre fspec0 w0 |-- EX w, FS_Pre fspec w ** (FS_Post fspec w  ₑ-* FS_Post fspec0 w0)) ->
  forall P Q w0 PF, 
  P |-- FS_Pre fspec0 w0  ** PF ->
  FS_Post fspec0 w0 ** PF |-- Q ->
  closed_wrt_gvars (fun x => modvars_global x (CCall f)  = false) PF ->
  Delta ⊢ {{P}} CCall f {{Q}}.
Proof.
  intros.
  eapply hoare_conseq;eauto.
  eapply hoare_frame'.
  split;auto.
  apply funcall_closedlvars.
  eapply hoare_Call_specderive;eauto.
Qed.

Definition IterSepcon (xs : list assertion) : assertion := fold_right sepcon emp xs.
Fixpoint consec_mem p n (tl: list vtype) : list assertion := 
  match n, tl with 
  | S n' , t :: tl' => (vPV p ↦ₗ (0, t) $ ➀ ) :: (consec_mem (p + 1) n' tl')
  | _ , _  => nil
  end.
  
Lemma IterSepcon_consec_mem_add_N : forall n p0 l g tl,
  (p0 > 0) -> (length tl >= n)%nat ->
  IterSepcon
  (consec_mem p0 n tl) (mk_lstate l g (mem_add_N empty_mem p0 0 tl n )).
Proof.
  unfold mem_add_N. 
  intros *.  revert p0 l g tl.
  induction n; intros * H Hlen; simpl in *.
  - unfold emp;simpl;auto. unfold impmodelrules.is_unit. cbn.  solve_empmem.
  - destruct tl;simpl in Hlen;[lia | ].
    cbn; unfold mstore, basicasrt.sepcon, substmem;simpl.
    exists (mk_lstate l g (single_mem p0 ((0, v), ➀) )), (mk_lstate l g (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl))).
    cbn. unfold impmodelrules.join. cbn. splits;auto.
    + pose proof (mem_join_emp1 (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl))).
      pose proof (single_mem_single p0 ((0,v), ➀)).
      unfold mem_single in H1. destruct H1.
      assert (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl) p0 = None).
      { apply mem_add_N_notin. lia. }
      apply (mem_join_update_None1 _ _ _ _ _ _ H0 H3).
      * intros. unfold empty_mem, single_mem.
        apply addr_eqb_neq in H4. rewrite H4. auto.
      * unfold mem_add. rewrite addr_eqb_refl. auto.
      * intros. unfold mem_add.
        apply addr_eqb_neq in H4. rewrite H4. auto.
    + unfold basicasrt.andp, basicasrt.coq_prop, isvalidptr.
        simpl.
        split;auto.
    + apply IHn. lia. lia.
Qed.


Lemma hoare_Alloc : forall Δ x e tl v P ,
  P |-- EV e @ vint ↦ₗ v -> 
  (length tl >= (Z.to_nat v))%nat -> 
  Δ ⊢ {{ P }} 
      CAlloc x tl e
      {{EX p0 v',  !! ( (p0 > 0)) &&
      IterSepcon (consec_mem p0 (Z.to_nat v) tl) **
      (LV x @ vptr ↦ₗ p0 && (subst_local x v' P)) }} .
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl.
  intros * He1 Hlen * HDelta * Hm1 HP.
  specialize (He1 _  HP).
  unfold aeval_expr in He1.
  intros * Hev.
  unfold alloc_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st1.
  destruct_st st2.
  unfold st_mem in *; simpl in *.
  apply fun_ext1 in H6.
  subst g0.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1.
  inversion H6. subst v. clear H6.
  exists (mem_add_N m1 x1 0 tl (Z.to_nat x0)).
  split.
  + eapply (mem_join_add_range m1 ) with (m' := m0);eauto.
    ++ intros. rewrite mem_add_N_in; auto. erewrite H2;auto. lia.  
    ++ intros. rewrite mem_add_N_notin;auto. lia.  
  + exists x1, (l x).
    unfold substmem, mstore, basicasrt.andp, basicasrt.sepcon, isvalidptr, basicasrt.coq_prop, lveq;simpl.
    split ; auto.
    exists (mk_lstate l0 g (mem_add_N empty_mem x1 0 tl (Z.to_nat x0))), (mk_lstate l0 g m1).
    unfold impmodelrules.join. cbn.
    splits;auto.
    -- eapply (mem_join_add_range _ _ _ _ _ x1 (x1 + x0) (mem_join_emp1 m1));eauto.
       * intros. pose proof mem_join_None3 p Hm1 as [? _];auto.
       * intros. rewrite ! mem_add_N_in; auto. lia.  lia.
       * intros. rewrite ! mem_add_N_notin; auto. lia.
       * intros. rewrite ! mem_add_N_notin; auto. lia.
    -- unfold substmem;simpl.
       eapply IterSepcon_consec_mem_add_N;auto.
    -- unfold subst_local,substmem; simpl.
       rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_Free : forall Δ e1 v1 v0  P p ,
  isvalidptr v1 ->
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P --||-- PV v1 ↦ₗ v0  $ ➀ ** p ->
  Δ ⊢ {{ P }} 
      CFree e1
      {{ p }} .
Proof.
  intros * Hvalidp He1 H.
  eapply hoare_conseq_pre.
  rewrite H.
  apply derivable1_refl.
  unfold valid_contextualtriple_nrm, valid_triple_nrm.
  intros callees HDelta * Hm1 HP.
  rewrite H in He1.
  specialize (He1 _ HP).
  unfold aeval_expr in He1; destruct_st st1;simpl in *.

  intros * Hev.
  simpl in Hev.
  unfold free_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H3, H4.
  subst l0 g0.
  exists (mem_remove m1 x).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1. inversion H3. clear H3. subst v1.  
  unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
  destruct HP.
  my_destruct H3. destruct_st x0. destruct_st x1. simpl in H3. unfold impmodelrules.join in H3.
  cbn in H3. my_destruct H3. subst g1 g0 l1 l0.
  cbn in *.
  subst m2.
  split.
  + erewrite (mem_remove_unfold m m0);eauto.
    apply mem_join_mem_remove_l;auto.
    pose proof mem_join_Some1 _ _ _  _ _ _ H3 (single_mem_get_eq x (v0, ➀)) as [? [? ?]].
    apply Perm_full_leb_eq in H6.
    subst.
    unfold writable_m.
    rewrite H4.
    apply writable_perm_eq_full.
    reflexivity.
  + apply mem_join_comm in H3.
    erewrite <- (mem_join_single_mem_remove_l _ H3).
    auto.
    Unshelve.
    simpl.
    apply writable_perm_eq_full.
    reflexivity.
Qed.

Lemma hoare_Seq : forall Delta c1 c2 P1 P2 P3,
  Delta ⊢ {{P1}} c1 {{P2}} ->
  Delta ⊢ {{P2}} c2 {{P3}} -> 
  Delta ⊢ {{P1}} CSeq c1 c2 {{P3}} .
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * HT1 HT2.
  intros * HDelta * Hm1 HP.
  specialize (HT1 _ HDelta st1 m1 mf Hm1 HP) as HT1.
  sets_unfold.
  intros * Hev.
  destruct Hev as [st3 [? ?] ].
  specialize (HT1 _ H).
  destruct HT1 as [m2 [? ?] ].
  specialize (HT2 _ HDelta st3 m2 mf H1 H2) as HT2.
  specialize (HT2 _ H0).
  auto.
Qed.

Lemma hoare_If : forall Delta b bv c1 c2 P P',
  P |-- BV b ↦ₗ bv -> 
  Delta ⊢ {{ !! (btrue bv) && P }} c1 {{ P' }} ->
  Delta ⊢ {{ !! (bfalse bv) && P }} c2 {{ P' }} ->
  Delta ⊢ {{ P }} CIf b c1 c2 {{ P' }}.
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * H HT1 HT2.
  intros * HDelta * Hm1 HP.
  specialize (HT1 _ HDelta st1 m1 mf Hm1).
  specialize (HT2 _ HDelta st1 m1 mf Hm1).
  specialize (H _ HP).
  unfold beval_expr in H.
  
  sets_unfold; unfold test_true, test_false ; intros * Hev.
  my_destruct Hev.
  + subst x.
    destruct_st st1.
    simpl in *.
    pose proof mem_join_beval_nrm_eq Hm1 Hev H. inversion H2. clear H2. subst x0 x1.
    assert ((!! btrue bv && P)
    {| lenv := l; genv := g; st_mem := m1 |}).
    { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (btrue bv) P H1)).
      apply H2.
      auto.
    }
    specialize (HT1 H2) as ?.
    apply H3;auto.
  + subst x.
    destruct_st st1.
    simpl in *.
    pose proof mem_join_beval_nrm_eq Hm1 Hev H. inversion H1. clear H1. subst x0 bv.
    assert ((!! bfalse 0 && P)
    {| lenv := l; genv := g; st_mem := m1 |}).
    { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (bfalse 0) P (ltac:(reflexivity)))).
      apply H1.
      auto.
    }
    specialize (HT2 H1) as ?.
    apply H2;auto.
Qed.

Lemma hoare_While : forall Delta b c I bv,
  I |-- BV b ↦ₗ bv -> 
  valid_contextualtriple_nrm Delta
    (!! (btrue bv) &&  I) c I ->
  valid_contextualtriple_nrm Delta
    I (CWhile b c) (!! (bfalse bv) &&  I).
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * Hbv HT.
  intros * HDelta * Hm1 HP.
    unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;simpl;intros;[ contradiction | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    my_destruct H;subst.
    + assert ((!! btrue bv && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, btrue in *;
       destruct_st st1;
       simpl in *.
       my_destruct H;subst.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.  inversion H1. clear H1. subst x0 x1.
       tauto. }
     specialize (HT H3) as ?;clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + eexists.
      splits;eauto.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp,  bfalse in *;
      destruct_st st2;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.   inversion H1. clear H1. subst bv x.
      split;[int auto | auto ].
Qed.

Lemma hoare_While' : forall Delta b c I,
  I |-- EX bv, BV b ↦ₗ bv -> 
  valid_contextualtriple_nrm Delta
    (Abtrue b &&  I) c I ->
  valid_contextualtriple_nrm Delta
    I (CWhile b c) (Abfalse b &&  I).
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * Hbv HT.
  intros * HDelta * Hm1 HP.
    unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;simpl;intros;[ contradiction | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    destruct H0 as [bv H0].
    my_destruct H;subst.
    + assert ((Abtrue b && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, Abtrue in *;
       destruct_st st1;
       simpl in *.
       split;auto.
       exists bv.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.   inversion H1. clear H1. subst x0 x1.
       tauto. }
     specialize (HT H3) as ?;clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + eexists.
      splits;eauto.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp,  Abfalse in *;
      destruct_st st2;
      simpl in *.
      split;auto.
      exists bv.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.   inversion H1. clear H1. subst bv x.
      split;[int auto | auto ].
Qed.

Lemma hoare_While_false : forall Delta b c I bv,
  I |-- BV b ↦ₗ bv -> bfalse bv ->
  valid_contextualtriple_nrm Delta
    I (CWhile b c) ( I).
Proof.
  unfold valid_contextualtriple_nrm, valid_triple_nrm. simpl. intros * Hbv Hbfalse.
  intros * HDelta * Hm1 HP.
    unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    apply Hbv in HP as ?.
    unfold beval_expr in H0.
    destruct n. simpl in H. contradiction.
    simpl in H. destruct H.
    - my_destruct H.
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H5. subst x0 x1.
      unfold bfalse in Hbfalse.
      lia. 
    - my_destruct H. subst st2.
      eexists.
      eauto.
Qed.

End  NormalImpHoareRules.


(**********************************************************************************)
(*                     imp err language's hoare rules                             *)
(*                                                                                *)
(**********************************************************************************)
Module PracticalImpHoareRules.
Import ContextualJoinStateGlobalEnv.
Import ImpRules.


Lemma hoare_conseq_pre : forall Delta c P P' Q,
  P |-- P' ->
  Delta ⊢ {{P'}} c {{Q}} -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P' Q Q); auto.
  apply derivable1_refl.
Qed.

Lemma hoare_conseq_post : forall Delta c P Q Q',
  Q' |-- Q ->
  Delta ⊢ {{P}} c {{Q'}} -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. apply (hoare_conseq _ _ P P Q Q'); auto.
  apply derivable1_refl.
Qed.

Lemma hoare_conseq_post' : forall Delta c P Q Q',
  Delta ⊢ {{P}} c {{Q'}} ->
  Q' |-- Q -> 
  Delta ⊢ {{P}} c {{Q}}.
Proof.
  intros. eapply hoare_conseq_post;eauto.
Qed.

Lemma hoare_exists_l : forall Delta c (A : Type) (P : A -> assertion) P',
  (forall v : A, Delta ⊢ {{P v}} c {{P'}}) ->
  Delta ⊢ {{EX y, P y}} c {{P'}}.
Proof.
  unfold  valid_contextualtriple, valid_triple. simpl. intros * HT.
  intros * HDelta * Hm1 HP.
  destruct HP.
  specialize (HT x _ HDelta _ _ _ Hm1 H) as [HTerr HT].
  split;auto.
Qed.

Lemma hoare_exists_r : forall Delta c (A : Type) (v : A) P (P' : A -> assertion),
  Delta ⊢ {{P}} c {{P' v}} ->
  Delta ⊢ {{P}} c {{EX y, P' y}}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * HT.
  intros * HDelta * Hm1 HP.
  specialize (HT _ HDelta _ _ _ Hm1 HP) as [HTerr HT].
  splits;auto. 
  intros * Hev.
  specialize (HT _ Hev)as [m2 ?]. exists m2. intuition. exists v. auto.
Qed.


Lemma hoare_frame : forall Delta c (A : Type) P (P' : A -> assertion) PF,
  closed_wrt_modvars c PF ->
  Delta ⊢ {{P}} c {{EX v, P' v}} ->
  Delta ⊢ {{P ** PF}} c {{EX v, (P' v ** PF)}}.
Proof.
  unfold  valid_contextualtriple, valid_triple. intros * HCP HT.
  intros * HDelta * Hm1 HP. 
  destruct_st st1.
  destruct HP as [st0 [stf  [? [? ?] ] ] ].
  destruct_st st0.
  destruct_st stf.
  cbn in *. unfold impmodelrules.join in H. cbn in H. my_destruct H. subst. 
  
  destruct (mem_join_assoc2 H Hm1) as [mframe' [? ?] ].
  specialize (HT _ HDelta (mk_lstate l g m) m0 mframe' H3 H0) as [HTerr HT].
  splits;auto.
  
  intros * Hev.
  specialize (HT st2 Hev) as [m2' [? ?] ].
  destruct H5 as [v ?].
  destruct (mem_join_assoc1 H2 H4) as [m3 [? ?] ].
  exists m3. split; auto.
  exists v.
  destruct_st st2. cbn in *. 
  exists (mk_lstate l0 g0 m2'), (mk_lstate l0 g0 m2). repeat split; auto.
  destruct HCP as [HCPL HCPG]. destruct (modvars_spec _ _ _ _ Hev) as [HML HMG].
  unfold substmem.
  rewrite <- (HCPL l l0 g0); auto.
  rewrite <- (HCPG l g g0); auto.
Qed.

Lemma hoare_frame' : forall Delta c  P Q PF,
  closed_wrt_modvars c PF ->
  Delta ⊢ {{P}} c {{Q}} ->
  Delta ⊢ {{P ** PF}} c {{Q ** PF}}.
Proof.
  unfold valid_contextualtriple, valid_triple. intros * HCP HT.
  intros * HDelta * Hm1 HP. 
  destruct HP as [st0 [stf [? [? ?] ] ] ].
  destruct_st st1.
  destruct_st st0.
  destruct_st stf.
  cbn in *. unfold impmodelrules.join in H. cbn in H. my_destruct H. subst. 
  destruct (mem_join_assoc2 H Hm1) as [mframe' [? ?] ].
  specialize (HT _ HDelta (mk_lstate l g m) m0 mframe' H3 H0) as [HTerr HT].
  splits;auto.
  intros * Hev.
  specialize (HT st2 Hev) as [m2' [? ?] ].
  destruct (mem_join_assoc1 H2 H4) as [m3 [? ?] ].
  exists m3. split; auto.
  destruct_st st2. cbn in *. 
  exists (mk_lstate l0 g0 m2'), (mk_lstate l0 g0 m2). repeat split; auto.
  destruct HCP as [HCPL HCPG]. destruct (modvars_spec _ _ _ _ Hev) as [HML HMG].
  unfold substmem.
  rewrite <- (HCPL l l0 g0); auto.
  rewrite <- (HCPG l g g0); auto.
Qed.

Lemma hoare_pure : forall Delta c (P0 : Prop) P Q,
  (P0 -> Delta ⊢ {{P}} c {{Q}}) ->
  Delta ⊢ {{!! P0 && P}} c {{Q}}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * HT.
  intros * HDelta * Hm1 HP .
  unfold coq_prop in HP. destruct HP as [? HP].
  specialize (HT H _ HDelta _ _ _ Hm1 HP) as [? ?].
  split;auto.
Qed.

Lemma hoare_pure_r : forall Delta c (P0 : Prop) P Q,
  P0 ->
  Delta ⊢ {{P}} c {{Q}} ->
  Delta ⊢ {{P}} c {{!! P0 && Q}}.
Proof.
  intros.
  eapply hoare_conseq_post'.
  eapply H0.
  erewrite  coq_prop_andp_equiv;eauto.
  apply derivable1_refl.
Qed.

Lemma hoare_or : forall Delta c P1 P2 Q,
  Delta ⊢ {{P1}} c {{Q}} ->
  Delta ⊢ {{P2}} c {{Q}} ->
  Delta ⊢ {{orp P1 P2}} c {{Q}}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * HT1 HT2.
  intros * HDelta * Hm1 HP.
  unfold orp in *.
  destruct HP .
  - 
    specialize (HT1 _ HDelta _ _ _  Hm1 H) as [? ?].
    split;
    auto.
  - specialize (HT2 _ HDelta _ _ _  Hm1 H) as [? ?].
    split;
    auto.
Qed.

Lemma hoare_Skip : forall Delta P,
  Delta ⊢ {{P}} CSkip {{P}}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl.
  intros * HDelta * Hm1 HP. 
  splits;auto.
  intros * Hev.
  sets_unfold in Hev. subst.
  exists m1; split; auto.
Qed.

Lemma hoare_AsgnLocal : forall Δ (x : var) e (v : value) (P : assertion),
  P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ P }} 
      CAsgnLocal x e
      {{EX v', LV x ↦ₗ v && (subst_local x v' P)}}.
Proof.
  unfold valid_contextualtriple, valid_triple.
  intros * H callees HDelta * Hm1 HP.
  specialize (H _ HP).
  destruct_st st1.
  unfold aeval_expr in H.
  simpl in *.
  splits.
  - eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto. 
  -
  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H.
  subst v.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H3.
  apply fun_ext1 in H2.
  subst m0 g0.
  exists m1;splits;auto.
  exists (l x).
  unfold subst_local;unfold lveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_AsgnLocal' : forall Δ (x : var) e (v v' : value) (P : assertion),
  LV x ↦ₗ v' && P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ LV x ↦ₗ v' && P }} 
      CAsgnLocal x e
      {{ LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  intros * He.
  eapply hoare_conseq_post.
  2:{ apply hoare_AsgnLocal with (v := v).
      auto. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_local_and |  ].
  assert ((subst_local x v'' (LV x ↦ₗ v') && subst_local x v'' P) |-- subst_local x v' P).
  { pose proof subst_local_lveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.
 
Lemma hoare_AsgnGlobal : forall Δ (x : var) e (v : value) (P : assertion),
  P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ P }} 
      CAsgnGlobal x e
      {{EX v', GV x ↦ₗ v && (subst_global x v' P)}}.
Proof.
  unfold valid_contextualtriple, valid_triple.
  intros * H callees HDelta * Hm1 HP.
  specialize (H _ HP).
  destruct_st st1.
  unfold aeval_expr in H.
  simpl in *.
  splits.
  - eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto. 
  -
  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H.
  subst v.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H3.
  apply fun_ext1 in H2.
  subst m0 l0.
  exists m1;splits;auto.
  exists (g x).
  unfold subst_global;unfold gveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_AsgnGlobal' : forall Δ (x : var) e (v v' : value) (P : assertion),
  GV x ↦ₗ v' && P |--  EV e ↦ₗ v ->
  Δ ⊢ {{ GV x ↦ₗ v' && P }} 
      CAsgnGlobal x e
      {{ GV x ↦ₗ v && (subst_global x v' P)}} .
Proof.
  intros * He.
  eapply hoare_conseq_post.
  2:{ apply hoare_AsgnGlobal with (v := v).
      auto. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_global_and |  ].
  assert ((subst_global x v'' (GV x ↦ₗ v') && subst_global x v'' P) |-- subst_global x v' P).
  { pose proof subst_global_gveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.

(* load sem is loading a value into a local var  *)
Lemma hoare_LoadFull : forall Δ x e ve v pm P,
  P |--  EV e @ vptr ↦ₗ ve ->
  P |--  !! isvalidptr ve && PV ve ↦ₗ v $ pm ** TT ->
  Δ ⊢ {{ P }} 
      CLoad x e
      {{EX v', LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  unfold valid_contextualtriple, valid_triple.
  intros * H0 H1 callees HDelta * Hm1 HP.
  specialize (H0 _ HP).
  destruct_st st1.
  unfold aeval_expr in H0.
  simpl in *.
  splits.
  - sets_unfold.
    cut (~
    (aeval e).(err) {| lenv := l; genv := g; st_mem := m |} /\ ~
     load_sem_err x (aeval e).(nrm) {| lenv := l; genv := g; st_mem := m |});[tauto | ].
    split.
    { eapply aeval_nrm_nerr;eauto.
    eapply mem_join_aeval_nrm;eauto. }
    unfold load_sem_err; sets_unfold.
    unfold not;intros H2; my_destruct H2.
    { pose proof mem_join_aeval_nrm_eq Hm1 H2 H0. inversion H3. subst x0 x1. clear H3.
    specialize (H1 _ HP).
    unfold mstore, isvalidptr, basicasrt.coq_prop, basicasrt.andp, basicasrt.sepcon, basicasrt.truep in H1.
    destruct H1.
    my_destruct H1. }
    { pose proof mem_join_aeval_nrm_eq Hm1 H2 H0. inversion H4. subst x0 x1. clear H4.
    specialize (H1 _ HP).
    unfold mstore, isvalidptr, basicasrt.coq_prop, basicasrt.andp, basicasrt.sepcon, basicasrt.truep in H1.
    destruct H1.
    my_destruct H1. }
    pose proof mem_join_aeval_nrm_eq Hm1 H2 H0. inversion H4. subst x0 x1. clear H4.
    specialize (H1 _ HP).
    unfold mstore, isvalidptr, basicasrt.coq_prop, basicasrt.andp,  basicasrt.sepcon, basicasrt.truep in H1.
    destruct H1.
    my_destruct H1. destruct_st x0. destruct_st x1. cbn in *. unfold impmodelrules.join in H1. cbn in *.
    my_destruct H1. subst.
    simpl in *.
    pose proof mem_join_Some1 _ _ _ _ _ _ H1 (single_mem_get_eq ve (v,pm)) as [? [? ?]].
    pose proof mem_join_Some1 _ _ _ _ _ _ Hm1 H4 as [? [? ?]].
    congruence. 
  -
  unfold load_sem_nrm;sets_unfold;  intros * Hev.
  my_destruct Hev.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H0.
  inversion H7.
  subst x0.
  destruct_st st2;simpl in *.
  apply fun_ext1 in H5, H6.
  subst m0 g0.
  specialize (H1 _ HP) as [? ?].
  unfold mstore, isvalidptr, basicasrt.coq_prop, basicasrt.andp,  basicasrt.sepcon,  basicasrt.truep in *;simpl in *.
  my_destruct H5. destruct_st x0. destruct_st x1. cbn in *. unfold impmodelrules.join in H5. cbn in *.
  my_destruct H5. subst.
  simpl in *.
  clear H7.
  pose proof mem_join_Some1 _ _ _ _ _ _ H5  (single_mem_get_eq ve (v, pm)) as [? [? ?]].
  pose proof mem_join_Some_eq_l Hm1 H6 H2.
  destruct b. simpl in H9.
  subst v.
  exists m1;splits;auto.
  exists (l x).
  unfold subst_local;unfold lveq, basicasrt.andp in *; simpl in *.
  split;auto.
  rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_LoadFull' : forall Δ x e ve v v' pm P ,
  LV x ↦ₗ v' && P |--  EV e @ vptr ↦ₗ ve ->
  P |--  !! isvalidptr ve && PV ve ↦ₗ v $ pm ** TT  ->
  Δ ⊢ {{ LV x ↦ₗ v' && P }} 
      CLoad x e
      {{LV x ↦ₗ v && (subst_local x v' P)}} .
Proof.
  intros *  He Hp.
  eapply hoare_conseq_post.
  2:{ eapply hoare_LoadFull with (v := v);
      eauto.
      eapply derivable1_trans.
      apply derivable1_andp_elim2.
      exact Hp. }
  eapply shallow_exp_left;intro v''.
  eapply logic_equiv_derivable1_andp;[ apply logic_equiv_refl | eapply subst_local_and |  ].
  assert ((subst_local x v'' (LV x ↦ₗ v') && subst_local x v'' P) |-- subst_local x v' P).
  { pose proof subst_local_lveq x v'' v'.
    apply logic_equiv_derivable1 in H as [? _].
    rewrite H.
    intros st.
    unfold basicasrt.andp, basicasrt.coq_prop.
    intros [? ?];subst;auto.
  }
  rewrite H.
  apply derivable1_refl.
Qed.

Lemma hoare_Store : forall Δ e1 e2 v0 v1 v2 P ,
  isvalidptr v1 ->
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P |-- EV e2 ↦ₗ v2 ->
  Δ ⊢ {{ PV v1 ↦ₗ v0 $ ➀ ** P }} 
      CStore e1 e2
      {{ PV v1 ↦ₗ v2 $ ➀ ** P }} .
Proof.
  unfold valid_contextualtriple, valid_triple.
  intros * Hvalidp He1 He2.
  intros callees HDelta * Hm1 HP.
  pose proof (PV_irrelevant_var v1 v0 He1) _ HP.
  pose proof (PV_irrelevant_var v1 v0 He2) _ HP.
  unfold aeval_expr in H, H0; destruct_st st1;simpl in *.
  splits.
  - 
    sets_unfold.
    repeat match goal with 
    | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
    | |- _ => splits
    end.
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto. 
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto.

    unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
    unfold isvalidptr in Hvalidp.
    destruct HP.
    my_destruct H1.
    destruct_st x. destruct_st x0. cbn in *. unfold impmodelrules.join in H1. cbn in *.
    my_destruct H1. subst.
    unfold asgn_deref_sem_err;intros Herr; my_destruct Herr.
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr H. inversion H4. subst x x0. clear H4. discriminate. }
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr H. inversion H5. subst x x0. clear H5. subst v1. lia. }
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr H. inversion H5. subst x x0. clear H5.
      simpl in *.
      pose proof mem_join_Some1 _ _ _  _ _  _ H1  (single_mem_get_eq v1 (v0, ➀)) as [? [? ?]].
      apply Perm_full_leb_eq in H5. subst x.
      pose proof mem_join_Some1 _ _ _  _ _  _ Hm1 H2 as [? [? ?]].
      apply Perm_full_leb_eq in H6. subst x.
      apply H4.
      unfold writable_m.
      rewrite H5.
      rewrite writable_perm_eq_full.
      reflexivity. }
  -
  intros * Hev.
  simpl in Hev.
  unfold asgn_deref_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H5, H6.
  subst l0 g0.
  exists (mem_update m1 x v).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev H. inversion H5. clear H5. subst v1. 
  pose proof mem_join_aeval_nrm_eq Hm1 H1 H0. inversion H5. clear H5. subst v2. 
  unfold mstore, basicasrt.andp, isvalidptr, coq_prop in HP.
  destruct HP.
  my_destruct H5.
  destruct_st x0. destruct_st x1. cbn in *. unfold impmodelrules.join in H5. cbn in *.
  my_destruct H5. subst l1 l0 g1 g0.
  split.
  + assert (m2 x = Some  (v0, ➀)).
    { subst. apply single_mem_get_eq. }
    pose proof mem_join_Some1 m2 m3 m1 x v0 ➀ H5 H9 as [? [? ?]].
    apply Perm_full_leb_eq in H11. subst x0.
    pose proof mem_join_Some1 _ _ _  _ v0 ➀ Hm1 H10 as [? [? ?]].
    apply Perm_full_leb_eq in H12. subst x0.
    erewrite (mem_update_unfold m m0 x (v0, ➀));eauto.
    2:{ unfold writable_m. rewrite H4. apply writable_perm_eq_full. reflexivity.   }
    subst. simpl.
    apply mem_join_mem_update_l;auto.
    unfold writable_m.
    rewrite H10.
    apply writable_perm_eq_full. reflexivity. 
  + exists (mk_lstate l g (mem_update m2 x v)), (mk_lstate l g m3).
    simpl. unfold impmodelrules.join. simpl.
    splits;auto. 
    ++ subst.
       apply mem_join_mem_update_l;auto.
       unfold writable_m.
       rewrite single_mem_get_eq.
       apply writable_perm_eq_full. reflexivity. 
    ++ unfold substmem, mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop;simpl.
       splits;auto.
       subst m2.
       apply mem_update_single_eq.
       simpl.
       apply writable_perm_eq_full. reflexivity. 
Qed.


Lemma hoare_Store' : forall Δ e1 e2 v0 v1 v2 P p,
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P |-- EV e2 ↦ₗ v2 ->
  P |-- !! isvalidptr v1 ->
  P --||-- PV v1 ↦ₗ v0 $ ➀ ** p ->
  Δ ⊢ {{ P }} 
      CStore e1 e2
      {{ PV v1 ↦ₗ v2 $ ➀** p }} .
Proof.
  intros * He1 He2 Hvalidp H.
  eapply hoare_conseq_pre.
  rewrite H.
  apply derivable1_refl.
  unfold valid_contextualtriple, valid_triple.
  intros callees HDelta * Hm1 HP.
  rewrite H in Hvalidp, He1, He2.
  specialize (Hvalidp _ HP). unfold basicasrt.coq_prop in Hvalidp.
  specialize (He1 _ HP).
  specialize (He2 _ HP).
  unfold aeval_expr in He1, He2; destruct_st st1;simpl in *.
  splits.
  - 
    sets_unfold.
    repeat match goal with 
    | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
    | |- _ => splits
    end.
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto. 
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto.

    unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
    unfold isvalidptr in Hvalidp.
    destruct HP.
    my_destruct H0. destruct_st x. destruct_st x0. simpl in H0. unfold impmodelrules.join in H0.
    cbn in H0. my_destruct H0. subst g1 g0 l1 l0.
    cbn in *.
    unfold asgn_deref_sem_err;intros Herr; my_destruct Herr.
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr He1. inversion H4. subst x x0. clear H4. discriminate. }
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr He1. inversion H5. subst x x0. clear H5.  lia. }
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr He1. inversion H5. subst x x0. clear H5. 
      simpl in *.
      subst m0.
      pose proof mem_join_Some1 _ _ _  _ _  _ H0  (single_mem_get_eq v1 (v0, ➀)) as [? [? ?]].
      apply Perm_full_leb_eq in H3. subst x.
      pose proof mem_join_Some1 _ _ _  _ _  _ Hm1 H1 as [? [? ?]].
      apply Perm_full_leb_eq in H5. subst x.
      apply H4.
      unfold writable_m.
      rewrite H3.
      rewrite writable_perm_eq_full.
      reflexivity. }
  -
  intros * Hev.
  simpl in Hev.
  unfold asgn_deref_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H4, H5.
  subst l0 g0.
  exists (mem_update m1 x v).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1. inversion H4. clear H4. subst v1. 
  pose proof mem_join_aeval_nrm_eq Hm1 H0 He2. subst v2.
  unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
  destruct HP.
  my_destruct H4. destruct_st x0. destruct_st x1. simpl in H4. unfold impmodelrules.join in H4.
  cbn in H4. my_destruct H4. subst g1 g0 l1 l0.
  cbn in *.
  split.
  + assert (m2 x = Some  (v0, ➀)).
    { subst. apply single_mem_get_eq. }
    pose proof mem_join_Some1 _ _ _  x v0 ➀ H4 H8 as [? [? ?]].
    apply Perm_full_leb_eq in H10. subst x0.
    pose proof mem_join_Some1 _ _ _  x v0 ➀ Hm1 H9 as [? [? ?]].
    apply Perm_full_leb_eq in H11. subst x0.
    erewrite (mem_update_unfold m m0 x (v0, ➀));eauto.
    2:{ unfold writable_m. rewrite H3. apply writable_perm_eq_full. reflexivity.   }
    subst. simpl.
    apply mem_join_mem_update_l;auto.
    unfold writable_m.
    rewrite H9.
    apply writable_perm_eq_full. reflexivity. 
  + exists (mk_lstate l g (mem_update m2 x v)), (mk_lstate l g m3).
    simpl. unfold impmodelrules.join. simpl.
    splits;auto. 
    ++ subst.
       apply mem_join_mem_update_l;auto.
       unfold writable_m.
       rewrite single_mem_get_eq.
       apply writable_perm_eq_full. reflexivity. 
    ++ unfold substmem, mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop;simpl.
       splits;auto.
       subst m2.
       apply mem_update_single_eq.
       simpl.
       apply writable_perm_eq_full. reflexivity. 
Qed.

(* Lemma hoare_Store'' : forall Δ e1 e2 v0 v1 v2 PL P ,
  Alvars PL |-- EV e1 ↦ₗ v1 ->
  Alvars PL |-- EV e2 ↦ₗ v2 ->
  Δ ⊢ {{ Alvars PL && PV v1 ↦ₗ v0 ** P }} 
      CStore e1 e2
      {{ Alvars PL && PV v1 ↦ₗ v2 ** P }} .
Proof.
  intros * He1 He2.
  eapply hoare_conseq with (P' := PV v1 ↦ₗ v0 ** (Alvars PL && P) ).
  3:{ apply hoare_Store with (v0 := v0) (v1 := v1) (v2 := v2).
      - eapply derivable1_trans.
        apply derivable1_andp_elim1.
        auto.
      - eapply derivable1_trans.
        apply derivable1_andp_elim1.
        auto. }
  - erewrite sepcon_andp_Alvars2.
    apply derivable1_refl.
  - erewrite sepcon_andp_Alvars1.
    apply derivable1_refl.
Qed. *)

Lemma hoare_Call : forall Delta f fspec (w : fspec.(FS_With)),
  In (f, fspec) Delta ->
  Delta ⊢ {{FS_Pre fspec w}} 
          CCall f 
          {{FS_Post fspec w}}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * Hf.
  intros * HDelta * Hm1 HP.
  specialize (HDelta _ _ Hf st1 _ _ w Hm1 HP) as [Hnerr Hnrm].
  splits;auto.
  intros * Hev.
  destruct Hev.
  destruct_st st1. destruct_st st2.
  cbn in *.
  subst l0.
  specialize (Hnrm (mk_gstate g0 m0) H).
  eapply Hnrm.
Qed.


Lemma hoare_Call_frm : forall Delta f fspec (w : fspec.(FS_With)) PF,
  closed_wrt_modvars (CCall f) PF ->
  In (f, fspec) Delta ->
  Delta ⊢ {{(FS_Pre fspec w) ** PF}}  
          CCall f 
          {{(FS_Post fspec w)** PF}}. 
Proof.
  intros.
  eapply hoare_frame';eauto.
  eapply hoare_Call;eauto.
Qed.

Lemma funcall_closedlvars  : forall f P, 
closed_wrt_lvars (fun x => modvars_local x (CCall f) = false) P.
Proof.
  unfold closed_wrt_lvars;simpl;intros.
  assert (l1 = l2). { apply fun_ext1. intros. eapply H. auto. }
  rewrite H0.
  reflexivity.
Qed.

Lemma hoare_Call_frm' : forall Delta f fspec P Q (w : fspec.(FS_With)) PF,
  In (f, fspec) Delta ->
  P |-- (FS_Pre fspec w) ** PF ->
  (FS_Post fspec w)** PF |-- Q ->
  closed_wrt_gvars (fun x => modvars_global x (CCall f)  = false) PF ->
  Delta ⊢ {{P}} CCall f {{Q}}. 
Proof.
  intros.
  eapply hoare_conseq;eauto.
  eapply hoare_Call_frm;eauto.
  split;auto.
  apply funcall_closedlvars.
Qed.

Lemma hoare_Call_specderive : forall Delta f fspec fspec0,
  In (f, fspec) Delta ->
  (forall (w0 : fspec0.(FS_With)),
  FS_Pre fspec0 w0 |-- EX w, FS_Pre fspec w ** (FS_Post fspec w  ₑ-* FS_Post fspec0 w0)) ->
  forall w0, 
  Delta ⊢ {{FS_Pre fspec0 w0}} 
          CCall f 
          {{FS_Post fspec0 w0}}.
Proof.
  intros.
  specialize (H0 w0).
  eapply hoare_conseq_pre.
  exact H0.
  eapply hoare_exists_l.
  intros w.
  eapply hoare_conseq_post'.
  eapply hoare_Call_frm;auto.
  unfold closed_wrt_modvars.
  split. apply funcall_closedlvars.
  cbn.
  apply closed_wrt_gvars_wandenv.
  apply derivable1_wandenv_sepcon_modus_ponens2.
Qed.

Lemma hoare_Call_specderive_frm : forall Delta f fspec fspec0,
  In (f, fspec) Delta ->
  (forall (w0 : fspec0.(FS_With)),
  FS_Pre fspec0 w0 |-- EX w, FS_Pre fspec w ** (FS_Post fspec w  ₑ-* FS_Post fspec0 w0)) ->
  forall P Q w0 PF, 
  P |-- FS_Pre fspec0 w0  ** PF ->
  FS_Post fspec0 w0 ** PF |-- Q ->
  closed_wrt_gvars (fun x => modvars_global x (CCall f)  = false) PF ->
  Delta ⊢ {{P}} CCall f {{Q}}.
Proof.
  intros.
  eapply hoare_conseq;eauto.
  eapply hoare_frame'.
  split;auto.
  apply funcall_closedlvars.
  eapply hoare_Call_specderive;eauto.
Qed.

Definition IterSepcon (xs : list assertion) : assertion := fold_right sepcon emp xs.
Fixpoint consec_mem p n (tl: list vtype) : list assertion := 
  match n, tl with 
  | S n' , t :: tl' => (vPV p ↦ₗ (0, t) $ ➀ ) :: (consec_mem (p + 1) n' tl')
  | _ , _  => nil
  end.
  
Lemma IterSepcon_consec_mem_add_N : forall n p0 l g tl,
  (p0 > 0) -> (length tl >= n)%nat  ->
  IterSepcon
  (consec_mem p0 n tl) (mk_lstate l g (mem_add_N empty_mem p0 0 tl n )).
Proof.
  unfold mem_add_N. 
  intros *.  revert p0 l g tl.
  induction n; intros * H Hlen; simpl in *.
  - unfold emp;simpl;auto. unfold impmodelrules.is_unit. cbn.  solve_empmem.
  - destruct tl;simpl in Hlen;[lia | ].
    cbn; unfold mstore, basicasrt.sepcon, substmem;simpl.
    exists (mk_lstate l g (single_mem p0 ((0, v), ➀) )), (mk_lstate l g (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl))).
    cbn. unfold impmodelrules.join. cbn. splits;auto.
    + pose proof (mem_join_emp1 (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl))).
      pose proof (single_mem_single p0 ((0,v), ➀)).
      unfold mem_single in H1. destruct H1.
      assert (mem_add_list empty_mem (Zseq (p0 + 1) n) (map (fun t : vtype => (0, t)) tl) p0 = None).
      { apply mem_add_N_notin. lia. }
      apply (mem_join_update_None1 _ _ _ _ _ _ H0 H3).
      * intros. unfold empty_mem, single_mem.
        apply addr_eqb_neq in H4. rewrite H4. auto.
      * unfold mem_add. rewrite addr_eqb_refl. auto.
      * intros. unfold mem_add.
        apply addr_eqb_neq in H4. rewrite H4. auto.
    + unfold basicasrt.andp, basicasrt.coq_prop, isvalidptr.
        simpl.
        split;auto.
    + apply IHn. lia. lia.
Qed.

Lemma hoare_Alloc : forall Δ x e tl v P ,
  P |-- EV e @ vint  ↦ₗ v -> 
  (length tl >= (Z.to_nat v))%nat -> 
  Δ ⊢ {{ P }} 
      CAlloc x tl e
      {{EX p0 v',  !! ( (p0 > 0)) &&
      IterSepcon (consec_mem p0 (Z.to_nat v) tl) **
      (LV x @ vptr ↦ₗ p0 && (subst_local x v' P)) }} .
Proof.
  unfold valid_contextualtriple, valid_triple. simpl.
  intros * He1 Hlen * HDelta * Hm1 HP.
  specialize (He1 _  HP).
  unfold aeval_expr in He1.
  splits.
  - sets_unfold.
    destruct_st st1.
    simpl in *.
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto.
  - intros * Hev.
  unfold alloc_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st1.
  destruct_st st2.
  unfold st_mem in *; simpl in *.
  apply fun_ext1 in H6.
  subst g0.
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1.
  inversion H6. subst v. clear H6.
  exists (mem_add_N m1 x1 0 tl (Z.to_nat x0)).
  split.
  + eapply (mem_join_add_range m1 ) with (m' := m0);eauto.
    ++ intros. rewrite mem_add_N_in; auto. erewrite H2;auto. lia.
    ++ intros. rewrite mem_add_N_notin;auto. lia.  
  + exists x1, (l x).
    unfold substmem, mstore, basicasrt.andp, basicasrt.sepcon, isvalidptr, basicasrt.coq_prop, lveq;simpl.
    split ; auto.
    exists (mk_lstate l0 g (mem_add_N empty_mem x1 0 tl (Z.to_nat x0))), (mk_lstate l0 g m1).
    unfold impmodelrules.join. cbn.
    splits;auto.
    -- eapply (mem_join_add_range _ _ _ _ _ x1 (x1 + x0) (mem_join_emp1 m1));eauto.
       * intros. pose proof mem_join_None3 p Hm1 as [? _];auto.
       * intros. rewrite ! mem_add_N_in; auto. lia. lia.
       * intros. rewrite ! mem_add_N_notin; auto. lia.
       * intros. rewrite ! mem_add_N_notin; auto. lia.
    -- unfold substmem;simpl.
       eapply IterSepcon_consec_mem_add_N;auto.
    -- unfold subst_local,substmem; simpl.
       rewrite vmap_repair_eq';eauto.
Qed.

Lemma hoare_Free : forall Δ e1 v1 v0  P p ,
  isvalidptr v1 ->
  P |-- EV e1 @ vptr ↦ₗ v1 ->
  P --||-- PV v1 ↦ₗ v0  $ ➀ ** p ->
  Δ ⊢ {{ P }} 
      CFree e1
      {{ p }} .
Proof.
  intros * Hvalidp He1 H.
  eapply hoare_conseq_pre.
  rewrite H.
  apply derivable1_refl.
  unfold valid_contextualtriple, valid_triple.
  intros callees HDelta * Hm1 HP.
  rewrite H in He1.
  specialize (He1 _ HP).
  unfold aeval_expr in He1; destruct_st st1;simpl in *.
  splits.
  - 
    sets_unfold.
    repeat match goal with 
    | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
    | |- _ => splits
    end.
    eapply aeval_nrm_nerr.
    eapply mem_join_aeval_nrm;eauto. 
    unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
    unfold isvalidptr in Hvalidp.
    destruct HP.
    my_destruct H0. destruct_st x. destruct_st x0. simpl in H0. unfold impmodelrules.join in H0.
    cbn in H0. my_destruct H0. subst g1 g0 l1 l0. cbn in *.
    unfold free_sem_err;intros Herr; my_destruct Herr.
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr He1.  inversion H4. subst x x0. clear H4. discriminate. }
    { pose proof mem_join_aeval_nrm_eq Hm1 Herr He1.  inversion H6. subst x x0. clear H6. lia. }
  -
  intros * Hev.
  simpl in Hev.
  unfold free_sem_nrm in Hev.
  my_destruct Hev.
  destruct_st st2.
  simpl in *.
  apply fun_ext1 in H3, H4.
  subst l0 g0.
  exists (mem_remove m1 x).
  pose proof mem_join_aeval_nrm_eq Hm1 Hev He1. inversion H3. clear H3. subst v1.  
  unfold mstore, basicasrt.andp, isvalidptr, basicasrt.coq_prop in HP.
  destruct HP.
  my_destruct H3. destruct_st x0. destruct_st x1. simpl in H3. unfold impmodelrules.join in H3.
  cbn in H3. my_destruct H3. subst g1 g0 l1 l0.
  cbn in *.
  subst m2.
  split.
  + erewrite (mem_remove_unfold m m0);eauto.
    apply mem_join_mem_remove_l;auto.
    pose proof mem_join_Some1 _ _ _  _ _ _ H3 (single_mem_get_eq x (v0, ➀)) as [? [? ?]].
    apply Perm_full_leb_eq in H6.
    subst.
    unfold writable_m.
    rewrite H4.
    apply writable_perm_eq_full.
    reflexivity.
  + apply mem_join_comm in H3.
    erewrite <- (mem_join_single_mem_remove_l _ H3).
    auto.
    Unshelve.
    simpl.
    apply writable_perm_eq_full.
    reflexivity.
Qed.

Lemma hoare_Seq : forall Delta c1 c2 P1 P2 P3,
  Delta ⊢ {{P1}} c1 {{P2}} ->
  Delta ⊢ {{P2}} c2 {{P3}} -> 
  Delta ⊢ {{P1}} CSeq c1 c2 {{P3}} .
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * HT1 HT2.
  intros * HDelta * Hm1 HP.
  specialize (HT1 _ HDelta st1 m1 mf Hm1 HP) as [? HT1].
  splits.
  - sets_unfold.
    repeat match goal with 
    | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
    | |- _ => splits
    end.
    auto.
    unfold not;intros [? [? ?]].
    specialize (HT1 _ H0).
    my_destruct HT1.
    specialize (HT2 _ HDelta x m mf HT1 H2) as [? ?].
    tauto.
  - intros * Hev.
  destruct Hev as [st3 [? ?] ].
  specialize (HT1 _ H0).
  destruct HT1 as [m2 [? ?] ].
  specialize (HT2 _ HDelta st3 m2 mf H2 H3) as [?  HT2].
  specialize (HT2 _ H1).
  auto.
Qed.

Lemma hoare_If : forall Delta b bv c1 c2 P P',
  P |-- BV b ↦ₗ bv -> 
  Delta ⊢ {{ !! (btrue bv) && P }} c1 {{ P' }} ->
  Delta ⊢ {{ !! (bfalse bv) && P }} c2 {{ P' }} ->
  Delta ⊢ {{ P }} CIf b c1 c2 {{ P' }}.
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * H HT1 HT2.
  intros * HDelta * Hm1 HP.
  specialize (HT1 _ HDelta st1 m1 mf Hm1).
  specialize (HT2 _ HDelta st1 m1 mf Hm1).
  specialize (H _ HP).
  unfold beval_expr in H.
  splits.
  - sets_unfold.
    repeat match goal with 
    | |- ~ (?P \/ ?Q)  => cut (~ P /\ ~ Q);[tauto | ]
    | |- _ => splits
    end.
    { unfold test_true, not; intros.
      my_destruct H0.
      subst x.
      destruct_st st1.
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H0 H. inversion H3. subst x0 x1. clear H3.
      assert ((!! btrue bv && P)
      {| lenv := l; genv := g; st_mem := m1 |}).
      { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (btrue bv) P H2)).
        apply H3.
        auto.
      }
      specialize (HT1 H3) as [? _]. contradiction. }
    { unfold test_false, not; intros.
      my_destruct H0.
      subst x.
      destruct_st st1.
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H0 H. inversion H2.
      subst bv x0. clear H2.
      assert ((!! bfalse 0 && P)
      {| lenv := l; genv := g; st_mem := m1 |}).
      { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (bfalse 0) P (ltac:(reflexivity)))).
        apply H2.
        auto.
      }
      specialize (HT2 H2) as [? _].
      congruence. }
  -
  sets_unfold; unfold test_true, test_false ; intros * Hev.
  my_destruct Hev.
  + subst x.
    destruct_st st1.
    simpl in *.
    pose proof mem_join_beval_nrm_eq Hm1 Hev H. inversion H2. 
    subst  x0 x1. clear H2.
    assert ((!! btrue bv && P)
    {| lenv := l; genv := g; st_mem := m1 |}).
    { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (btrue bv) P H1)).
      apply H2.
      auto.
    }
    specialize (HT1 H2) as [_ ?].
    apply H3;auto.
  + subst x.
    destruct_st st1.
    simpl in *.
    pose proof mem_join_beval_nrm_eq Hm1 Hev H. inversion H1.
    subst bv x0. clear H1.
    assert ((!! bfalse 0 && P)
    {| lenv := l; genv := g; st_mem := m1 |}).
    { pose proof (logic_equiv_derivable1_2 (coq_prop_andp_equiv (bfalse 0) P (ltac:(reflexivity)))).
      apply H1.
      auto.
    }
    specialize (HT2 H1) as [_ ?].
    apply H2;auto.
Qed.

Lemma hoare_While : forall Delta b c I bv,
  I |-- BV b ↦ₗ bv -> 
  valid_contextualtriple Delta
    (!! (btrue bv) &&  I) c I ->
  valid_contextualtriple Delta
    I (CWhile b c) (!! (bfalse bv) &&  I).
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * Hbv HT.
  intros * HDelta * Hm1 HP.
  splits.
  - unfold Lfix, test_true, test_false;
    sets_unfold.
    unfold not;intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;intros;simpl in *;[auto | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    my_destruct H;subst.
    + assert ((!! btrue bv && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, btrue in *;
       destruct_st st1;
       simpl in *.
       my_destruct H;subst.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.
       inversion H1. subst x0 x1. clear H1.
       tauto. }
     specialize (HT H3) as [_ ?];clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + 
    assert ((!! btrue bv && I)
   {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
    { clear - Hm1 H2 H H0 HP.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, btrue in *;
      destruct_st st1;
      simpl in *.
      my_destruct H;subst.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H1. subst x0 x1. clear H1.
      tauto. }
    specialize (HT H3) as [? _];clear H3.
    auto.
    + unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, btrue in *;
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm Hm1 H0.
      eapply (beval_nrm_nerr H1 H);eauto.
  - unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;simpl;intros;[ contradiction | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    my_destruct H;subst.
    + assert ((!! btrue bv && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, btrue in *;
       destruct_st st1;
       simpl in *.
       my_destruct H;subst.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.
       inversion H1. subst x0 x1. clear H1.
       tauto. }
     specialize (HT H3) as [_ ?];clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + eexists.
      splits;eauto.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp,  bfalse in *;
      destruct_st st2;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H1. subst bv x. clear H1.
      split;[int auto | auto ].
Qed.

Lemma hoare_While' : forall Delta b c I,
  I |-- EX bv, BV b ↦ₗ bv -> 
  valid_contextualtriple Delta
    (Abtrue b &&  I) c I ->
  valid_contextualtriple Delta
    I (CWhile b c) (Abfalse b &&  I).
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * Hbv HT.
  intros * HDelta * Hm1 HP.
  splits.
  - unfold Lfix, test_true, test_false;
    sets_unfold.
    unfold not;intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;intros;simpl in *;[auto | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    destruct H0 as [bv H0].
    my_destruct H;subst.
    + assert ((Abtrue b && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, Abtrue in *;
       destruct_st st1;
       simpl in *.
       split;auto.
       exists bv.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.
       inversion H1. subst x0 x1. clear H1.
       tauto. }
     specialize (HT H3) as [_ ?];clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + 
    assert ((Abtrue b && I)
   {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
    { clear - Hm1 H2 H H0 HP.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, Abtrue in *;
      destruct_st st1;
      simpl in *.
      split;auto.
      exists bv.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H1. subst x0 x1. clear H1.
      tauto. }
    specialize (HT H3) as [? _];clear H3.
    auto.
    + unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, Abtrue in *;
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm Hm1 H0.
      eapply (beval_nrm_nerr H1 H);eauto.
  - unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    generalize dependent st1. revert m1 mf.
    induction n;simpl;intros;[ contradiction | ].
    specialize (HT _ HDelta _ _ _ Hm1).
    apply Hbv in HP as ?.
    destruct H0 as [bv H0].
    my_destruct H;subst.
    + assert ((Abtrue b && I)
    {| lenv := lenv st1; genv := genv st1; st_mem := m1 |}).
     { clear - Hm1 H2 H H0 HP.
       unfold beval_expr, basicasrt.coq_prop, basicasrt.andp, test_true, Abtrue in *;
       destruct_st st1;
       simpl in *.
       split;auto.
       exists bv.
       pose proof mem_join_beval_nrm_eq Hm1 H H0.
       inversion H1. subst x0 x1. clear H1.
       tauto. }
     specialize (HT H3) as [_ ?];clear H3.
     specialize (H5 _ H1).
     my_destruct H5.
     eapply IHn;eauto.
    + eexists.
      splits;eauto.
      unfold beval_expr, basicasrt.coq_prop, basicasrt.andp,  Abfalse in *;
      destruct_st st2;
      simpl in *.
      split;auto.
      exists bv.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H1. subst bv x. clear H1.
      split;[int auto | auto ].
Qed.

Lemma hoare_While_false : forall Delta b c I bv,
  I |-- BV b ↦ₗ bv -> bfalse bv ->
  valid_contextualtriple Delta
    I (CWhile b c) ( I).
Proof.
  unfold valid_contextualtriple, valid_triple. simpl. intros * Hbv Hbfalse.
  intros * HDelta * Hm1 HP.
  splits.
  - unfold Lfix, test_true, test_false;
    sets_unfold.
    unfold not;intros.
    destruct H as [n H].
    apply Hbv in HP as ?.
    unfold beval_expr in H0.
    destruct n. simpl in H. contradiction.
    simpl in H. destruct H.
    + my_destruct H.
      subst.
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H3. subst x0 x1.
      unfold bfalse in *.
      lia.
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H4. subst x0 x1.
      unfold bfalse in *.
      lia.
    + eapply beval_nrm_nerr;eauto.
      destruct_st st1;
      simpl in *.
      eapply mem_join_beval_err_rev;eauto.
  - 
    unfold Lfix, test_true, test_false;
    sets_unfold.
    intros.
    destruct H as [n H].
    apply Hbv in HP as ?.
    unfold beval_expr in H0.
    destruct n. simpl in H. contradiction.
    simpl in H. destruct H.
    + my_destruct H.
      destruct_st st1;
      simpl in *.
      pose proof mem_join_beval_nrm_eq Hm1 H H0.
      inversion H5. subst x0 x1.
      unfold bfalse in Hbfalse.
      lia. 
    + my_destruct H. subst st2.
      eexists.
      eauto.
Qed.

End  PracticalImpHoareRules.
