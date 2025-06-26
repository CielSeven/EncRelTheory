Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics.



Section sllrules.

Import ImpRules.
Context (pm : Perm.t).

Local Open Scope asrt_scope.

Fixpoint sllbseg (x y: addr) (l: list Z) :=
  match l with
    | nil     => !! (x = y)  && emp
    | a :: l0 => EX p, !! (a <= Int64.max_signed /\ a >= Int64.min_signed) &&  
                   vPV x @ vptr ↦ₗ p $ pm  **
                   vPV p @ vint ↦ₗ a $ pm  **
                   sllbseg (p + 1) y l0
  end.


Lemma sllbseg_2_listrep': forall x y z l,
  isvalidptr y ->
  sllbseg x y l ** PV y @ vptr ↦ₗ z $ pm |--
  EX y', vPV x @ vptr ↦ₗ y' $ pm  ** listrep' pm  y' l z.
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + Intros.
    subst x.
    Exists z; quick_entailer!.
  + erewrite (ex_logic_euiqv_sepcon ). 
    eapply shallow_exp_left; unfoldimpmodel.
    intro x_v.
    rexists x_v.
    rewrite prop_andp_sepcon1.
    apply coq_prop_andp_left;intros.
    rewrite <- sepcon_assoc_logic_equiv; unfoldimpmodel.
    rewrite IHl.
    rewrite sepcon_comm_logic_equiv;unfoldimpmodel.
    erewrite (ex_logic_euiqv_sepcon ). 
    eapply shallow_exp_left; unfoldimpmodel.
    intro y'.
    erewrite (sepcon_comm_logic_equiv (vPV x @ vptr ↦ₗ x_v $ pm)  ((EX q ,
    !! (a <= Int64.max_signed /\ a >= Int64.min_signed) &&
    vPV x_v @ vint ↦ₗ a $ pm **
    vPV (x_v + 1) @ vptr ↦ₗ q $ pm ** 
    listrep' pm q l z))).
    unfoldimpmodel.
    erewrite (ex_logic_euiqv_sepcon ). 
    rexists y'.
    quick_entailer!.
Qed.

Lemma sllbseg_len1: forall (x y: addr) (a: Z),
  isvalidptr x -> isvalidptr y ->
  (a <= Int64.max_signed /\ a >= Int64.min_signed) ->
  PV x @ vptr ↦ₗ y $ pm ** PV y @ vint ↦ₗ a $ pm |--  
  sllbseg x (y + 1) (a::nil).
Proof.
  intros.
  simpl.
  Exists y.
  quick_entailer!.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + Intros.
    subst x.
    quick_entailer!.
  + erewrite (ex_logic_euiqv_sepcon ). 
    eapply shallow_exp_left; unfoldimpmodel.
    intro u.
    rexists u.
    quick_entailer!.
Qed.

Lemma subst_local_sllbseg : forall l p q x n, subst_local x n (sllbseg p q l) --||-- sllbseg p q l.
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

Lemma subst_global_sllbseg: forall l p q x n, subst_global x n (sllbseg p q l) --||-- (sllbseg p q l).
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



End  sllrules.

Ltac sll_asrt_simpl := 
    repeat progress ( match goal with 
    | |- context [subst_local ?x ?xv (sllbseg ?pm ?p ?q ?l) ] => erewrite (subst_local_sllbseg pm l p q x xv)
    | |- context [subst_global ?x ?xv (sllbseg ?pm ?p ?q ?l) ] => erewrite (subst_global_sllbseg pm l p q x xv)
    end).