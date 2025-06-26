Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics.

Import ImpRules.
Local Open Scope asrt_scope.


Module NormalImpHoareTac.
Import NormalContextualImp.
Import NormalImpHoareRules.
Ltac imp_rule := 
  match goal with 
  | |- ?delta ⊢ {{ ?P }} CSkip {{ ?Q }}  => apply hoare_Skip
  | |- ?delta ⊢ {{ ?P }} CAsgnLocal ?x ?e {{ ?Q }} =>
      eapply hoare_AsgnLocal; 
      asrt_simpl;symbolic_execution
  | |- ?delta ⊢ {{ ?P }} CAsgnGlobal ?x ?e {{ ?Q }} =>
      eapply hoare_AsgnGlobal ;
      asrt_simpl;symbolic_execution
  | |- ?delta ⊢ {{ ?P }} CLoad ?x ?e {{ ?Q }} =>
      eapply hoare_LoadFull;[ symbolic_execution | entailer!; symbolic_execution]

  | |- ?delta ⊢ {{ ?P }} CStore ?x ?e {{ ?Q }} =>
      eapply hoare_Store';[  symbolic_execution | symbolic_execution | idtac | 
    eapply logic_equiv_derivable1;unfoldimpmodel; split;[
    match goal with 
    | |- ?P |--PV ?l ↦ₗ ?v0 $ _ ** ?p => match P with 
                        | context [PV l ↦ₗ ?v $ ?pm ] => 
            eapply derivable1_trans; [ unfoldimpmodel; strongseplift  (PV l ↦ₗ v $ pm);refine (derivable1_refl _) |  refine (derivable1_refl _) ]  end 
    end | 
    asrt_simpl;
    andp_cancel1;
    sepcon_cancel] ];auto
  | |- ?delta ⊢ {{ ?P  }} CIf ?B ?c1 ?c2  {{ ?Q }} 
     => eapply hoare_If;[ asrt_simpl;symbolic_execution | |  ]
  | |- ?delta ⊢ {{ ?P }} CAlloc ?x ?t ?e {{ ?Q }} =>
      eapply hoare_Alloc;[ symbolic_execution | cbn;try lia ]
  | |- ?delta ⊢ {{ ?P }} CFree ?e {{ ?Q }} =>
      eapply hoare_Free;[ idtac  | symbolic_execution | 
      eapply logic_equiv_derivable1; unfoldimpmodel;split;[
      match goal with 
      | |- ?P |--PV ?l ↦ₗ ?v0 $ _ ** ?p => match P with 
                          | context [PV l ↦ₗ ?v $ ?pm ] => 
              eapply derivable1_trans; [ unfoldimpmodel; strongseplift  (PV l ↦ₗ v $ pm);refine (derivable1_refl _) |  refine (derivable1_refl _) ]  end 
      end | 
      asrt_simpl;
      andp_cancel1;
      sepcon_cancel ] ];auto
  end.
  
Ltac pure_intro :=  
  match goal with 
  | |- ?Δ ⊢ {{ (@basicasrt.coq_prop _ ?B) && ?P }} ?c {{ ?Q }} => eapply hoare_pure;intros; pure_intro
  | |- ?Δ ⊢ {{ (@basicasrt.exp ?s ?A _ )}} ?c {{ ?Q }} => eapply hoare_exists_l;
          match A with 
          | int64 => let v:= fresh "v" in intros v 
          | list ?B => let l := fresh "l" in intros l
          | _ => intros 
          end ; pure_intro
  | |- _ => idtac
  end.

Ltac forward := 
  match goal with 
  | |- ?delta ⊢ {{ ?P  }} CSeq ?c1 ?c2  {{ ?Q }} 
      => ( eapply hoare_Seq; [ imp_rule | pure_intro ]) ||  ( eapply hoare_Seq )
  | |- ?delta ⊢ {{ ?P  }} CIf ?B ?c1 ?c2  {{ ?Q }} 
      => eapply hoare_If;[ asrt_simpl;symbolic_execution | pure_intro | pure_intro ]
  | |- _ => eapply hoare_conseq_post';[imp_rule | idtac ]
  end.

Ltac simpl_pre := 
  repeat progress 
  ( eapply hoare_conseq_pre;[
    substlgvars;
    Rename asrt_simpl;
    try (match goal with 
    | |- ?P |-- ?Q => match P with 
                      | context [(@basicasrt.coq_prop ?s ?B)] =>  (* pure_simpl B; *)try andp_lift ((@basicasrt.coq_prop s B))
                      end    
    end);
    refine (derivable1_refl _);unfoldimpmodel | ];pure_intro).

Ltac clear_LV_pre := eapply hoare_conseq_pre;[ 
    repeat progress 
    (match goal with 
    | |- context [LV ?x ↦ₗ ?v] => match goal with 
                                | |- (LV x ↦ₗ v) && _ |-- _ => rewrite derivable1_andp_elim2
                                | |- _ => andp_lift (LV x ↦ₗ v); rewrite derivable1_andp_elim2
                                end
    end);refine (derivable1_refl _);unfoldimpmodel
  | ].

Ltac clear_LV_GV :=
    repeat progress 
    (match goal with 
    | |- LV ?x ↦ₗ ?v && _  |-- _ => rewrite derivable1_andp_elim2
    | |- GV ?x ↦ₗ ?v && _  |-- _ => rewrite derivable1_andp_elim2
    | |- context [LV ?x ↦ₗ ?v] => andp_lift (LV x ↦ₗ v)
    | |- context [GV ?x ↦ₗ ?v] => andp_lift (GV x ↦ₗ v)
    end).

Ltac clear_var_pre x :=
  eapply hoare_conseq_pre;[ 
    (match goal with 
    | |- context [LV x ↦ₗ ?v] => match goal with 
                                | |- (LV x ↦ₗ v) && _ |-- _ => rewrite derivable1_andp_elim2
                                | |- _ => andp_lift (LV x ↦ₗ v); rewrite derivable1_andp_elim2
                                end
    | |- context [GV x ↦ₗ ?v] => match goal with 
                            | |- (GV x ↦ₗ v) && _ |-- _ => rewrite derivable1_andp_elim2
                            | |- _ => andp_lift (GV x ↦ₗ v); rewrite derivable1_andp_elim2
                            end
    end);refine (derivable1_refl _);unfoldimpmodel
  | ].   

Ltac hoareasrt_simpl := asrt_simpl_aux idtac.
Ltac hoare_simpl_pre := 
  repeat progress 
  ( eapply hoare_conseq_pre;[
    hoareasrt_simpl;
    try (match goal with 
    | |- ?P |-- ?Q => match P with 
                      | context [(@basicasrt.coq_prop ?s ?B)] => 
                      let ret := isptrcoqprop B P in 
                        match ret with 
                        | false =>   (* pure_simpl B; *)try andp_lift ((@basicasrt.coq_prop s B))
                        | true => fail
                        end 
                      end   
    end);
    refine (derivable1_refl _);unfoldimpmodel | ];pure_intro).

Ltac hoare_simpl_pre_clearv :=
  match goal with 
  | |- context [subst_local ?x ?xv ?P ] => hoare_simpl_pre;try clear xv; try subst xv
  | |- context [subst_global ?x ?xv ?P ] => hoare_simpl_pre;try clear xv; try subst xv
  | |- _ => hoare_simpl_pre
  end.

Ltac forward_simpl := 
  match goal with 
  | |- ?delta ⊢ {{ ?P  }} CSeq ?c1 ?c2  {{ ?Q }} 
      => ( eapply hoare_Seq; [ imp_rule | pure_intro;hoare_simpl_pre_clearv ]) ||  ( eapply hoare_Seq )
  | |- ?delta ⊢ {{ ?P  }} CIf ?B ?c1 ?c2  {{ ?Q }} 
      => eapply hoare_If;[ asrt_simpl;symbolic_execution | pure_intro;hoare_simpl_pre_clearv | pure_intro;hoare_simpl_pre_clearv ]
  | |- ?delta ⊢ {{ ?P }} CSkip {{ ?Q }}  => apply hoare_Skip
  | |- _ => eapply hoare_conseq_post';[imp_rule | idtac ]
  end.

Ltac funcproof_init := 
  unfold triple_body_nrm;simpl;
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre;
  match goal with 
  | |- ?delta ⊢ {{ ?P }} ?f {{ ?Q }}   => try unfold f 
  end. 
End NormalImpHoareTac.
