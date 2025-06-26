Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

From SetsClass Require Import SetsClass.
From AUXLib Require Import Axioms Feq Idents  List_lemma int_auto VMap.
From compcert.lib Require Import Integers.

From EncRelSeq Require Import  callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion.


Import ImpRules.
Local Open Scope asrt_scope.

Ltac refl := refine (derivable1_refl _ ).

Inductive all_list : Type :=
  | norm_asrt : expr -> all_list
  | dependent_asrt : forall (A : Type), (A -> expr) -> all_list.

Ltac All_listasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in 
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A && ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A -* ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?A || ?B => let L1  :=  (All_listasrts_rec A (@nil all_list)) in
                let L2 :=  (All_listasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | subst_local ?x ?v ?P => constr:(L)
  | subst_global ?x ?v ?P => constr:(L)
  | @basicasrt.exp ?s ?t ?A  => constr:(cons (dependent_asrt t A) L)
  | TT => constr:(L)
  | emp => constr:(L)
  | LV ?x ↦ₗ ?v => constr:(L)
  | GV ?x ↦ₗ ?v => constr:(L)
  | ?x => constr:(cons (norm_asrt x) L)
  end.

Ltac All_listasrts P :=
  let l:= (All_listasrts_rec P (@nil all_list)) in 
  constr:(l).

Ltac Rename_rec l Tac :=
  match l with 
  | nil => Tac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt ((@basicasrt.coq_prop _ ?B) ) => set (a := B) in *
      | norm_asrt ?v => set (a := v) in *
      | dependent_asrt _ ?B => set (a := B) in *
    end; Rename_rec l' Tac ; subst a
  end. 

Ltac Rename Tac:= 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | |- ?P --||-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      Rename_rec l Tac
  | _ => idtac 
  end.

Ltac pure_Rename_rec l :=
  match l with 
  | nil => idtac 
  | ?x :: ?l' => 
    let a := fresh "v" in
    match x with 
      | norm_asrt ((@basicasrt.coq_prop _ ?B) ) => set (a := B) in *
      | norm_asrt ?v => set (a := v) in *
      | dependent_asrt _ ?B => set (a := B) in *
    end; pure_Rename_rec l'
  end. 

Ltac pure_Rename := 
  match goal with 
  | |- ?P |-- ?Q => 
    let L1 := All_listasrts P in 
    let L2 := All_listasrts Q in
    let l := eval cbn [List.app] in (List.app L1 L2) in
      pure_Rename_rec l
  end.


Ltac find_one x Hp :=
  match Hp with 
  | ?A && ?B => find_one x A
  | ?A && ?B => find_one x B
  | ?A ** ?B => find_one x A
  | ?A ** ?B => find_one x B
  | x => idtac
  end. 

Ltac sepcon_lift''' p :=
  ( (rewrite (sepcon_comm_logic_equiv) with (y:= p) ; unfoldimpmodel) ||
    (rewrite (sepcon_swap_logic_equiv) with (y:= p) ; unfoldimpmodel  ) ).

Ltac PV_lift p :=  
  match p with 
  | (PV ?a @ vptr ↦ₗ ?v $ ?pm) => 
        match goal with 
        | |- ?P |-- ?Q  => match P with 
              | context [?x ** (PV a @ vptr ↦ₗ v $ pm)] =>
              eapply derivable1_trans;[
              erewrite (sepcon_comm_logic_equiv x (PV a @ vptr ↦ₗ v $ pm));refl| ];unfoldimpmodel 
              | context [?x ** ((PV a @ vptr ↦ₗ v $ pm) ** ?y) ] => 
              eapply derivable1_trans;[
              erewrite (sepcon_swap_logic_equiv x (PV a @ vptr ↦ₗ v $ pm) y);refl| ];unfoldimpmodel 
              end
        | |- ?P |-- ?Q  => match Q with 
              | context [?x ** (PV a @ vptr ↦ₗ v $ pm)] => 
              eapply derivable1_trans;[ |
              erewrite (sepcon_comm_logic_equiv x (PV a @ vptr ↦ₗ v $ pm));refl];unfoldimpmodel 
              | context [?x ** ((PV a @ vptr ↦ₗ v $ pm) ** ?y) ] => 
              eapply derivable1_trans;[ | 
              erewrite (sepcon_swap_logic_equiv x (PV a @ vptr ↦ₗ v $ pm) y);refl ];unfoldimpmodel 
              end
        end
  | (PV ?a @ vint ↦ₗ ?v $ ?pm) => 
        match goal with 
        | |- ?P |-- ?Q  => match P with 
                          | context [?x ** (PV a @ vint ↦ₗ v $ pm)] =>
                          eapply derivable1_trans;[
                          erewrite (sepcon_comm_logic_equiv x (PV a @ vint ↦ₗ v $ pm));refl| ];unfoldimpmodel 
                          | context [?x ** ((PV a @ vint ↦ₗ v $ pm)** ?y) ] => 
                          eapply derivable1_trans;[
                          erewrite (sepcon_swap_logic_equiv x (PV a @ vint ↦ₗ v $ pm) y);refl| ];unfoldimpmodel 
                          end
        | |- ?P |-- ?Q  => match Q with 
                          | context [?x ** (PV a @ vint ↦ₗ v $ pm)] => 
                          eapply derivable1_trans;[ |
                          erewrite (sepcon_comm_logic_equiv x (PV a @ vint ↦ₗ v $ pm));refl];unfoldimpmodel 
                          | context [?x ** ((PV a @ vint ↦ₗ v $ pm) ** ?y) ] => 
                          eapply derivable1_trans;[ | 
                          erewrite (sepcon_swap_logic_equiv x (PV a @ vint ↦ₗ v $ pm) y);refl ];unfoldimpmodel 
                          end
        end
  end.


Ltac sepcon_lift'' p :=
  (PV_lift p || 
  match goal with 
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] =>
                    eapply derivable1_trans;[
                    erewrite (sepcon_comm_logic_equiv x p);refl| ];unfoldimpmodel 
                    | context [?x ** (p ** ?y) ] => 
                    eapply derivable1_trans;[
                    erewrite (sepcon_swap_logic_equiv x p y);refl| ];unfoldimpmodel 
                    end
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x ** p] => 
                    eapply derivable1_trans;[ |
                    erewrite (sepcon_comm_logic_equiv x p);refl];unfoldimpmodel 
                    | context [?x ** (p ** ?y) ] => 
                    eapply derivable1_trans;[ | 
                    erewrite (sepcon_swap_logic_equiv x p y);refl ];unfoldimpmodel 
                    end
  end). 


Ltac sepcon_lift' p := sepcon_lift'' p ;
  repeat progress (sepcon_lift'' p).

Ltac find_lift x Hp :=
  match Hp with 
  | ?A && ?B => find_lift x A
  | ?A && ?B => find_lift x B
  | ?A ** ?B => find_lift x A
  | ?A ** ?B => find_lift x B
  | x => sepcon_lift' x
  end. 

Ltac pure_find_lift x Hp :=
  match Hp with 
  | ?A ** ?B => pure_find_lift x A
  | ?A ** ?B => pure_find_lift x B
  | x => idtac
  end.   

Ltac sepcon_lift p :=
  match goal with 
  | |- ?P |-- ?Q => find_lift p P
  | |- _ => idtac end;
  match goal with 
  | |- ?P |-- ?Q => find_lift p Q 
  | |- _ => idtac 
  end.
                   
Ltac sepcon_cancel' P := 
   match P with 
  | ?x ** ?P' => match goal with 
                 | |- ?x ** _ |-- ?x ** _ => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl x ) | ]; unfoldimpmodel; sepcon_cancel' P'
                 | |- _  |-- ?Q =>  pure_find_lift x Q;
                sepcon_lift' x; eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; 
                sepcon_cancel' P'
                end
  | ?x ** ?P' => sepcon_cancel' P'
  | ?x => sepcon_lift x;
          match goal with
            | |- x |-- x => refine ( derivable1_refl _ )
            | |- x ** ?P |-- x ** _  => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            | |- x |-- x ** _ => eapply sepcon_cancel_res_emp 
          end 
  | _ => refl ||  idtac
   end.

Ltac sepcon_cancel := 
  match goal with 
  | |- ?x |-- ?x => refine ( derivable1_refl _ )
  | |- ?x ** _ |-- ?x ** _ => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl x ) | ]; unfoldimpmodel;  sepcon_cancel 
  | |- ?P |-- _ => sepcon_cancel' P 
  end.


Ltac TT_simpl :=
  repeat rewrite truep_andp_left_equiv; repeat rewrite truep_andp_right_equiv.

Ltac isptrcoqprop B Q := 
  match B with 
  | (isvalidptr _) => match Q with 
                    | context [(andp (coq_prop B) (mstore ?x ?v ?p))] => constr:(true)
                    | _ => constr:(false)
                  end
  | _ => constr:(false)
  end.  


Ltac asrt_easysimpl := (* TT_simpl; *)
  repeat progress match goal with 
  | |- context [ (?x && ?y) && ?z] => erewrite (logic_equiv_andp_assoc x y z); unfoldimpmodel
  | |- context [ (?P ** ?Q) ** ?R ] => erewrite <- (sepcon_assoc_logic_equiv P Q R); unfoldimpmodel
  | |- context [ ((@basicasrt.coq_prop _ ?P)  && ?Q) ** ?R ] => erewrite (prop_andp_sepcon1 P Q R)
  | |- context [ ?P ** ((@basicasrt.coq_prop _ ?Q)  && ?R) ] => erewrite (sepcon_andp_prop_equiv P Q R)
  | |- context [ ?P ** (@basicasrt.coq_prop _ ?Q)  ] => erewrite (sepcon_prop_equiv P Q)
  end.

Ltac andp_lift_foo p :=
  ( (rewrite (logic_equiv_andp_comm) with (y:= p) ; unfoldimpmodel) ||
            (rewrite (logic_equiv_andp_swap) with (y:= p) ) ).


Ltac andp_lift'' p :=
  ( andp_lift_foo p ||
  match goal with 
  | |- ?P |-- ?Q  => match Q with 
                    | context [?x && p ** ?q ] => erewrite (logic_equiv_andp_comm x (p ** q)) ; unfoldimpmodel
                    | context [?x && (p ** ?q  && ?y) ] => erewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  | |- ?P |-- ?Q  => match P with 
                    | context [?x && p ** ?q ] => erewrite (logic_equiv_andp_comm x (p ** q)) ; unfoldimpmodel
                    | context [?x && (p ** ?q  && ?y) ] => erewrite (logic_equiv_andp_swap x (p ** q) y) 
                    end
  end).

Ltac andp_lift' p := 
  andp_lift'' p ;
  repeat progress (andp_lift'' p).

Ltac andp_lift p := asrt_easysimpl; try (sepcon_lift p);
match goal with 
  | |- ?P |-- ?Q =>  andp_lift' p
  | |- ?P ?st => eapply (derivable1_imp _ _ st);[ andp_lift' p; refine (derivable1_refl _) | ]
end.



Ltac asrt_simpl := 
    repeat progress (match goal with 
    | |- context [ (?x && ?y) && ?z] => erewrite (logic_equiv_andp_assoc x y z); unfoldimpmodel
    | |- context [ (?P ** ?Q) ** ?R ] => erewrite <- (sepcon_assoc_logic_equiv P Q R); unfoldimpmodel
    | |- context [ ((@basicasrt.coq_prop _ ?P)  && ?Q) ** ?R ] => erewrite (prop_andp_sepcon1 P Q R)
    | |- context [ ?P ** ((@basicasrt.coq_prop _ ?Q)  && ?R) ] => erewrite (sepcon_andp_prop_equiv P Q R)
    | |- context [ ?P ** (@basicasrt.coq_prop _ ?Q)  ] => erewrite (sepcon_prop_equiv P Q)
    | |- context [ (_ ** _ ) && ?P ] => andp_lift P
    | |- context [ ?P ** emp ] => rewrite (sepcon_emp_equiv P)
    | |- context [ emp ** ?P ] => rewrite (sepcon_comm_logic_equiv emp P); unfoldimpmodel; rewrite (sepcon_emp_equiv P)
    | |- context [ ?P ** basicasrt.emp ] => rewrite (sepcon_emp_equiv P)
    | |- context [ basicasrt.emp ** ?P ] => rewrite (sepcon_comm_logic_equiv emp P); unfoldimpmodel; rewrite (sepcon_emp_equiv P)
    | |- context [?P ** (GV ?x ↦ₗ ?v && ?R)] => erewrite (sepcon_andp_gveq x v P R)
    | |- context [?P ** (LV ?x ↦ₗ ?v && ?R)] => erewrite (sepcon_andp_lveq x v P R)
    | |- context [(GV ?x ↦ₗ ?v && ?R) ** ?P ] => rewrite (sepcon_comm_logic_equiv (GV x ↦ₗ v && R) P); unfoldimpmodel;
                                                  erewrite (sepcon_andp_gveq x v P R)
    | |- context [(LV ?x ↦ₗ ?v && ?R) ** ?P ] => rewrite (sepcon_comm_logic_equiv (LV x ↦ₗ v && R) P); unfoldimpmodel;
                                                  erewrite (sepcon_andp_lveq x v P R)
    | |- context [((@basicasrt.coq_prop _ ?B) && ?Q) ** ?R] => rewrite (prop_andp_sepcon1 B Q R )
    | |- context [?P ** ((@basicasrt.coq_prop _ ?B) && ?R)] => rewrite (sepcon_andp_prop_equiv P B R)
    | |- context [?P ** ((@basicasrt.coq_prop _ ?B)) ] => rewrite (sepcon_prop_equiv P B)
    | |- context [((@basicasrt.coq_prop ?s ?B)) ** ?P ] => rewrite (sepcon_comm_logic_equiv ((@basicasrt.coq_prop s B)) P); unfoldimpmodel
    | |- context [ (@exp ?t ?P) && ?Q ] => erewrite (ex_logic_euiqv_andp _ Q)
    | |- context [ (@exp ?t ?P) ** ?Q ] => erewrite (ex_logic_euiqv_sepcon _ Q)
    | |- context [ @exp ?t ?P ] => try andp_lift (@exp t P); try sepcon_lift (@exp t P)
    | |- context [ (@basicasrt.exp ?s ?t ?P) && ?Q ] => erewrite (ex_logic_euiqv_andp _ Q)
    | |- context [ (@basicasrt.exp ?s ?t ?P) ** ?Q ] => erewrite (ex_logic_euiqv_sepcon _ Q)
    | |- context [ @basicasrt.exp ?s ?t ?P ] => try andp_lift (@basicasrt.exp s t P); try sepcon_lift (@basicasrt.exp s t P)
    | |- context [(@basicasrt.coq_prop ?s ?B)] => try andp_lift ((@basicasrt.coq_prop s B))
    end).

Ltac substlgvars := 
    repeat (progress match goal with
    | |- context [subst_local ?x ?xv (GV ?y ↦ₗ ?yv) ] => erewrite (subst_local_gv x y xv yv)
    | |- context [subst_local ?x ?xv (LV ?y ↦ₗ ?yv) ] => ( erewrite (subst_local_lvneq x y xv yv) by (cbv;congruence) ) ||
                                                          erewrite (subst_local_lveq x xv yv) 
    | |- context [subst_local ?x ?n (PV ?y ↦ₗ ?yv $ ?p )] => erewrite (subst_local_pv p x n y yv)
    | |- context [subst_local ?x ?n (listrep ?pm ?p ?l)] => erewrite (subst_local_listrep pm l p x n)
    | |- context [subst_local ?x ?n (listrep' ?pm ?p ?l ?q)] => erewrite (subst_local_listrep' pm l p q x n)
    | |- context [subst_local ?x ?n ((@basicasrt.coq_prop _ ?P) )] => erewrite (subst_local_pure P x n)
    | |- context [subst_local ?x ?n (@exp ?t ?P)] => erewrite (subst_local_exp x n P)
    | |- context [subst_local ?x ?n (?p && ?q )] => erewrite (subst_local_and p q x n)
    | |- context [subst_local ?x ?n (?p ** ?q )] => erewrite (subst_local_sepcon p q x n)
    | |- context [subst_global ?x ?xv (LV ?y ↦ₗ ?yv) ] => erewrite (subst_global_lv x y xv yv)
    | |- context [subst_global ?x ?xv (GV ?y ↦ₗ ?yv) ] => ( erewrite (subst_global_gvneq x y xv yv) by (cbv;congruence) ) ||
                                                          erewrite (subst_global_gveq x xv yv) 
    | |- context [subst_global ?x ?n (PV ?y ↦ₗ ?yv $ ?p)] => erewrite (subst_global_pv p x n y yv)
    | |- context [subst_global ?x ?n (listrep ?pm ?p ?l)] => erewrite (subst_global_listrep pm l p x n)
    | |- context [subst_global ?x ?n (listrep' ?pm ?p ?l ?q)] => erewrite (subst_global_listrep' pm l p q x n)
    | |- context [subst_global ?x ?n ((@basicasrt.coq_prop _ ?P) )] => erewrite (subst_global_pure P x n)
    | |- context [subst_global ?x ?n (@exp ?t ?P)] => erewrite (subst_global_exp x n P)
    | |- context [subst_global ?x ?n (?p && ?q )] => erewrite (subst_global_and p q x n)
    | |- context [subst_global ?x ?n (?p ** ?q )] => erewrite (subst_global_sepcon p q x n)
    end).

Ltac strongseplift P := try (sepcon_lift' P);
repeat progress match goal with 
| |- context [GV ?x ↦ₗ ?v && P ** ?R] => erewrite <- (sepcon_andp_gveq x v P R)
| |- context [LV ?x ↦ₗ ?v && P ** ?R] => erewrite <- (sepcon_andp_lveq x v P R)
| |- context [LV ?x ↦ₗ ?v && P] => erewrite (logic_equiv_andp_comm (LV x ↦ₗ v) P) ; unfoldimpmodel
| |- context [GV ?x ↦ₗ ?v && P] => erewrite (logic_equiv_andp_comm (GV x ↦ₗ v) P) ; unfoldimpmodel
end; try (sepcon_lift' P).


Ltac strongseplift_left P := 
  eapply derivable1_trans; 
  [ unfoldimpmodel; strongseplift P; refl | refl ].

Ltac strongsepcon_cancel' P := 
   match P with 
  | (PV ?x @ vptr ↦ₗ ?v $ ?pm) ** ?P' => match goal with 
                 | |- (PV x @ vptr ↦ₗ v $ pm) ** _ |-- (PV x @ vptr ↦ₗ v $ pm) ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; strongsepcon_cancel' P'
                 | |- _ =>
                strongseplift (PV x @ vptr ↦ₗ v $ pm); eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; 
                strongsepcon_cancel' P'
                end
  | (PV ?x @ vint ↦ₗ ?v $ ?pm) ** ?P' => match goal with 
                 | |- (PV x @ vint ↦ₗ v $ pm) ** _ |-- (PV x @ vint ↦ₗ v $ pm) ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; strongsepcon_cancel' P'
                 | |- _ =>
                strongseplift (PV x @ vint ↦ₗ v $ pm); eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; 
                strongsepcon_cancel' P'
                end
  | ?x ** ?P' => match goal with 
                 | |- x ** _ |-- x ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; strongsepcon_cancel' P'
                 | |- _ =>
                strongseplift x; eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; 
                strongsepcon_cancel' P'
                end
  | ?x ** ?P' => strongsepcon_cancel' P'
  | (PV ?a @ vptr ↦ₗ ?v $ ?pm) => strongseplift (PV a @ vptr ↦ₗ v $ pm);
          match goal with
            | |- ?x |-- ?x => refine ( derivable1_refl _ )
            | |- ?x ** _ |-- ?x ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            | |- ?x |-- ?x ** _ => eapply sepcon_cancel_res_emp 
            | |- ?x ** _ |-- ?x  => eapply sepcon_cancel_res_emp_right 
            | |- ?x && LV ?y ↦ₗ ?v |-- ?x ** _ => rewrite <- (sepcon_andp_lveqemp y v x);
                                                eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            | |- ?x && GV ?y ↦ₗ ?v |-- ?x ** _ => rewrite <- (sepcon_andp_gveqemp y v x);
                                                eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
          end 
  | (PV ?a @ vint ↦ₗ ?v $ ?pm) => strongseplift (PV a @ vint ↦ₗ v $ pm);
            match goal with
              | |- ?x |-- ?x => refine ( derivable1_refl _ )
              | |- ?x ** _ |-- ?x ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
              | |- ?x |-- ?x ** _ => eapply sepcon_cancel_res_emp 
              | |- ?x ** _ |-- ?x  => eapply sepcon_cancel_res_emp_right 
              | |- ?x && LV ?y ↦ₗ ?v |-- ?x ** _ => rewrite <- (sepcon_andp_lveqemp y v x);
                                                  eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
              | |- ?x && GV ?y ↦ₗ ?v |-- ?x ** _ => rewrite <- (sepcon_andp_gveqemp y v x);
                                                  eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            end 
  | ?x => strongseplift x;
          match goal with
            | |- x |-- x => refine ( derivable1_refl _ )
            | |- x ** _ |-- x ** ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            | |- x |-- x ** _ => eapply sepcon_cancel_res_emp 
            | |- x ** _ |-- x  => eapply sepcon_cancel_res_emp_right 
            | |- x && LV ?y ↦ₗ ?v |-- x ** _ => rewrite <- (sepcon_andp_lveqemp y v x);
                                                eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
            | |- x && GV ?y ↦ₗ ?v |-- x ** _ => rewrite <- (sepcon_andp_gveqemp y v x);
                                                eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel
          end 
  | (PV ?x @ vint ↦ₗ ?v $ ?pm) => try andp_lift (PV x @ vint ↦ₗ v $ pm); simple apply derivable1_andp_elim1 
  | (PV ?x @ vptr ↦ₗ ?v $ ?pm) => try andp_lift (PV x @ vptr ↦ₗ v $ pm); simple apply derivable1_andp_elim1 
  | ?x => try andp_lift x; simple apply derivable1_andp_elim1 
  | _ => idtac
  end.


Ltac andp_cancel' P := 
  match P with 
  | ?x && ?P' => match goal with 
                | |- x && _ |-- x && ?P' => eapply derivable1_sepcon_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel; andp_cancel' P'
                | |- _ =>
                andp_lift x;eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];
                andp_cancel' P'
                end
  | _ => idtac
  end.


Ltac cancel_LVGV :=
  match goal with 
  | |- _ |-- (LV ?x @ vptr ↦ₗ ?v) && _  => 
          match goal with 
          | |- (LV x @ vptr ↦ₗ v) && _ |-- (LV x @ vptr ↦ₗ v) && _ => eapply derivable1_andp_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel;  cancel_LVGV
          | |- _ =>
          andp_lift (LV x @ vptr ↦ₗ v);eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];
          unfoldimpmodel;  cancel_LVGV
          end
  | |- _ |-- (LV ?x @ vint ↦ₗ ?v) && _  => 
          match goal with 
          | |- (LV x @ vint ↦ₗ v) && _ |-- (LV x @ vint ↦ₗ v) && _ => eapply derivable1_andp_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel;  cancel_LVGV
          | |- _ =>
          andp_lift (LV x @ vint ↦ₗ v);eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];
          unfoldimpmodel;  cancel_LVGV
          end
  | |- _ |-- (GV ?x @ vptr ↦ₗ ?v) && _  => 
          match goal with 
          | |- (GV x @ vptr ↦ₗ v) && _ |-- (GV x @ vptr ↦ₗ v) && _ => eapply derivable1_andp_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel;  cancel_LVGV
          | |- _ =>
          andp_lift (GV x @ vptr ↦ₗ v);eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];
          unfoldimpmodel;  cancel_LVGV
          end
  | |- _ |-- (GV ?x @ vint ↦ₗ ?v) && _  => 
          match goal with 
          | |- (GV x @ vint ↦ₗ v) && _ |-- (GV x @ vint ↦ₗ v) && _ => eapply derivable1_andp_mono ; [refine ( derivable1_refl _ ) | ]; unfoldimpmodel;  cancel_LVGV
          | |- _ =>
          andp_lift (GV x @ vint ↦ₗ v);eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];
          unfoldimpmodel;  cancel_LVGV
          end
  (* | |- (LV ?x ↦ₗ ?v) && _ |-- _ => rewrite (derivable1_andp_elim2 (LV x ↦ₗ v)); cancel_LVGV
  | |- (GV ?x ↦ₗ ?v) && _ |-- _ => rewrite (derivable1_andp_elim2 (GV x ↦ₗ v)); cancel_LVGV *)
  | |- _ => idtac
  end.

Ltac andp_cancel'' :=
  match goal with 
  | |- ?x |-- ?x => refine (derivable1_refl _) 
  | |- ?x && _ |-- ?x && _ => eapply derivable1_andp_mono ; [refine (derivable1_refl _) | ];andp_cancel''
  | |- _ |-- ?x && ?P => andp_cancel' (x && P); andp_cancel''
  | |- _ &&  _ |-- ?P => strongsepcon_cancel' P  
  | |- _ => sepcon_cancel || idtac
  end.

(* 
Ltac pure_simpl B:= 
  repeat progress (match goal with 
  | |- context [((@basicasrt.coq_prop _ B) && ?Q) ** ?R] => rewrite (prop_andp_sepcon1 B Q R )
  | |- context [?P ** ((@basicasrt.coq_prop _ B) && ?R)] => rewrite (sepcon_andp_prop_equiv P B R)
  | |- context [?P ** ((@basicasrt.coq_prop _ B)) ] => rewrite (sepcon_prop_equiv P B)
  | |- context [((@basicasrt.coq_prop ?s B)) ** ?P ] => rewrite (sepcon_comm_logic_equiv ((@basicasrt.coq_prop s B)) P); unfoldimpmodel
  end;asrt_simpl). *)
Ltac andp_cancel1:= asrt_simpl;andp_cancel''.

Ltac pure_cancel :=
  match goal with 
  | |- ?P |--?Q  => match Q with 
                    | context [(@basicasrt.coq_prop ?s ?B)] =>  (* pure_simpl B; *)try andp_lift ((@basicasrt.coq_prop s B)); 
                        match goal with 
                        | |- _ |-- (@basicasrt.coq_prop s B) && _  => erewrite (coq_prop_andp_equiv B); unfoldimpmodel;[  pure_cancel | auto]
                        end
                    end
  | |- _ => idtac
  end.

Ltac andp_cancel := 
    match goal with 
   | |- ?P |-- ?Q || ?R => idtac 
   | |- ?P || ?Q |-- ?R => idtac
   | |- ?P |-- ?Q => match P with 
                    | context [ (@basicasrt.coq_prop ?s ?B) ] => try andp_lift ( (@basicasrt.coq_prop s B) ); apply (coq_prop_andp_left B); unfoldimpmodel; intros;andp_cancel
                    end
   | |- ?P |--?Q  => match Q with 
                    | context [(@basicasrt.coq_prop ?s ?B)] =>  (* pure_simpl B; *)try andp_lift ((@basicasrt.coq_prop s B)); 
                        match goal with 
                        | |- _ |-- (@basicasrt.coq_prop s B) && _  => erewrite (coq_prop_andp_equiv B); unfoldimpmodel;[  andp_cancel | auto]
                        end
                    end
   | |- (@basicasrt.coq_prop _ ?P)  |-- (@basicasrt.coq_prop _ ?Q)  => apply coq_prop_imply ; auto
   | |- _ |-- (@basicasrt.coq_prop _ ?Q)  => apply (coq_prop_right Q);auto
   | |- (@basicasrt.coq_prop _ ?P) |-- ?Q => eapply coq_prop_left; intros; andp_cancel
   | |- _ |-- TT => apply derivable1_truep_intros ; auto
   | |- _ => andp_cancel''
    end.

Ltac andp_cancel3 := 
  match goal with
  | |- (@basicasrt.coq_prop _ ?P)  |-- (@basicasrt.coq_prop _ ?Q)  => apply coq_prop_imply ; auto
  | |- _ |-- (@basicasrt.coq_prop _ ?Q)  => apply (coq_prop_right Q);auto
  | |- (@basicasrt.coq_prop _ ?P) |-- ?Q => eapply coq_prop_left; intros; andp_cancel3
  | |- _ |-- TT => apply derivable1_truep_intros ; auto
  | |- _ |-- _  => cancel_LVGV; andp_cancel''
  | |- _ => idtac
    end.

Ltac pureIntros := asrt_easysimpl;
repeat progress (match goal with 
| |- ?P |-- ?Q => (match P with 
                    | context [ ?P ** emp ] => rewrite (sepcon_emp_equiv P)
                    | context [ emp ** ?P ] => rewrite (sepcon_comm_logic_equiv emp P); unfoldimpmodel; rewrite (sepcon_emp_equiv P)
                    | context [ (@basicasrt.coq_prop ?s ?B) ] =>  (* pure_simpl B; *)try andp_lift ( (@basicasrt.coq_prop s B) ); apply (coq_prop_andp_left B); unfoldimpmodel; intros
                  end)
end).


Ltac pureIntros' := 
  repeat progress (match goal with 
  | |- ?P |--?Q =>  match P with 
                    | context [ ?P ** emp ] => rewrite (sepcon_emp_equiv P)
                    | context [ emp ** ?P ] => rewrite (sepcon_comm_logic_equiv emp P); unfoldimpmodel; rewrite (sepcon_emp_equiv P)
                    | context [(@basicasrt.coq_prop ?s ?B)] =>  (* pure_simpl B; *)try andp_lift ((@basicasrt.coq_prop s B)); eapply (coq_prop_andp_left B); unfoldimpmodel; intros
                    end 
  end).

Ltac symbolic_execution :=
  match goal with 
  | |- ?P |--aeval_expr (EVarGlobal ?x) ?v'  => 
      match P with 
      | context [GV x @ vptr ↦ₗ ?v ] => (andp_lift (GV x @ vptr ↦ₗ v) || idtac );
                                  eapply derivable1_trans; unfoldimpmodel;
                                  [ apply derivable1_andp_elim1; unfoldimpmodel | 
                                    apply aeval_expr_gvar_derives ]
      | context [GV x @ vint ↦ₗ ?v ] => (andp_lift (GV x @ vint ↦ₗ v) || idtac );
                                  eapply derivable1_trans; unfoldimpmodel;
                                  [ apply derivable1_andp_elim1; unfoldimpmodel | 
                                    apply aeval_expr_gvar_derives ]
      end 
  | |- ?P |--aeval_expr (EVarLocal ?x) ?v'  => 
      match P with 
      | context [LV x @ vptr ↦ₗ ?v ] => (andp_lift (LV x @ vptr ↦ₗ v) || idtac );
                                  eapply derivable1_trans; unfoldimpmodel;
                                  [ apply derivable1_andp_elim1; unfoldimpmodel | 
                                    apply aeval_expr_lvar_derives ]
      | context [LV x @ vint ↦ₗ ?v ] => (andp_lift (LV x @ vint ↦ₗ v) || idtac );
                                  eapply derivable1_trans; unfoldimpmodel;
                                  [ apply derivable1_andp_elim1; unfoldimpmodel | 
                                    apply aeval_expr_lvar_derives ]
      end 
  | |- ?P |--aeval_expr (ENum ?x) ?v'  => eapply aeval_expr_const_derives;clear; int auto
  | |- ?P |--aeval_expr (ENull) ?v'  => eapply aeval_expr_null_derives
  | |- ?P |--EV (EAdd ?e1 ?e2) @ vptr ↦ₗ ?v => eapply aeval_expr_EAdd_ptr_derive;[ 
                                        symbolic_execution |
                                        symbolic_execution  ]
  | |- ?P |--EV (EAdd ?e1 ?e2) @ vint ↦ₗ ?v => eapply aeval_expr_EAdd_int_derive;[ 
                                        symbolic_execution |
                                        symbolic_execution  ]
  | |- ?P |--EV (EAdd ?e1 ?e2) ↦ₗ ?v => 
      (eapply aeval_expr_EAdd_ptr_derive;[ symbolic_execution | symbolic_execution  ]) || 
      (eapply aeval_expr_EAdd_int_derive;[ symbolic_execution | symbolic_execution  ])
  | |- ?P |--EV (ESub ?e1 ?e2) @ vptr ↦ₗ ?v => eapply aeval_expr_ESub_ptr_derive;[ 
                                        symbolic_execution |
                                        symbolic_execution  ]
  | |- ?P |--EV (ESub ?e1 ?e2) @ vint ↦ₗ ?v => eapply aeval_expr_ESub_derive;[ 
                                        symbolic_execution |
                                        symbolic_execution  ]
  | |- ?P |--EV (ESub ?e1 ?e2) ↦ₗ ?v => 
      (eapply aeval_expr_ESub_ptr_derive;[ symbolic_execution | symbolic_execution  ]) || 
      (eapply aeval_expr_ESub_derive;[ symbolic_execution | symbolic_execution  ])
  | |- ?P |--BV (EEq ?e1 ?e2) ↦ₗ _ =>
      ( eapply beval_expr_eq_int_derives;symbolic_execution) ||
      ( eapply beval_expr_eq_ptr_derives;symbolic_execution) 
  | |- ?P |--BV (ENe ?e1 ?e2) ↦ₗ _ =>
      ( eapply beval_expr_neq_int_derives;symbolic_execution) ||
      ( eapply beval_expr_neq_ptr_derives;symbolic_execution) 
  | |- ?P |--BV (ELt ?e1 ?e2) ↦ₗ _ =>
      eapply beval_expr_lt_derives;symbolic_execution
  | |- ?P |--BV (ELe ?e1 ?e2) ↦ₗ _ =>
      eapply beval_expr_le_derives;symbolic_execution
  | |- ?P |--BV (EAnd ?e1 ?e2) ↦ₗ _ =>
      eapply beval_expr_Eand_derives;symbolic_execution
  | |- ?P |--PV ?p2 ↦ₗ _ $ _ ** TT => substlgvars; asrt_simpl; repeat match P with 
                                  | ?P && ?Q => rewrite derivable1_andp_elim2; unfoldimpmodel
                                  | context [PV p2 ↦ₗ ?v $ ?pm] => try (sepcon_lift (PV p2 ↦ₗ v $ pm)); 
                                                              ( apply (truep_sepcon_frm_r  (PV p2 ↦ₗ v $ pm ))  || 
                                                                apply truep_sepcon_elim2)
                                  end 
  | |- EX _, _ |--_ => eapply shallow_exp_left; unfoldimpmodel;intros;symbolic_execution
  | |- _ |--EX _, _ => eapply exp_right_exists;eexists;symbolic_execution
  end.





Ltac left_intro v:=
  asrt_simpl;
  eapply shallow_exp_left; unfoldimpmodel; 
  intro v.

Ltac left_intro' :=
  match goal with
  | |- ?P |--_ => match P with | context [EX _, _ ]  =>
                                  asrt_simpl;
                                  eapply shallow_exp_left; unfoldimpmodel; 
                                  intro;left_intro'
                                | _ => idtac end 
  | |- _ => idtac
  end.



Ltac right_intro v:=
  asrt_simpl;
  eapply shallow_allp_right; unfoldimpmodel;
  intro v.

Ltac rexists v:=
  eapply exp_right_exists;
  exists v.

Ltac simpl_auto := 
  try unfold isvalidptr in *;
  try unfold isptr in *;
  cbn in *; solve [auto | lia | int_auto].

Ltac simpl_entail := match goal with
  | |- _ |-- TT => apply derivable1_truep_intros
  | |- ?Q /\ ?R => split;[simpl_entail| simpl_entail]
  | |-  _ =>  simpl_auto || idtac  end.

Ltac asrt_simpl_aux tac := let tac0 := (substlgvars;tac;asrt_simpl) in Rename tac0.
Ltac normal_asrt := asrt_simpl_aux idtac.
Tactic Notation "normalize"  := normal_asrt.
Ltac simpl_entailer :=
  substlgvars;asrt_simpl;andp_cancel.
Tactic Notation "cancel" := Rename sepcon_cancel.
Tactic Notation "entailer!" := substlgvars;asrt_simpl;pureIntros; pure_cancel; andp_cancel3;simpl_entail.
(* use rename to speed up entailer, 
   However do not use it when 
   1. there are unkown assertins ?P
   2. there are wand_env
   3. there are unfoded fixpoint definition *)
Tactic Notation "quick_entailer!"  := unfoldimpmodel; Rename simpl_entailer;simpl_entail.
Tactic Notation "Intros" := pureIntros.
Tactic Notation "Intros" simple_intropattern(x0):= left_intro x0;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) := left_intro x0; left_intro x1;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) := left_intro x0; left_intro x1; left_intro x2;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) := left_intro x0; left_intro x1; left_intro x2; left_intro x3;pureIntros.
Tactic Notation "Intros" simple_intropattern(x0) simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) := left_intro x0; left_intro x1; left_intro x2; left_intro x3; left_intro x4;pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0):= right_intro x0;pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0) simple_intropattern(x1) := right_intro x0; right_intro x1;pureIntros.
Tactic Notation "Intros_r" simple_intropattern(x0) simple_intropattern(x1)
                          simple_intropattern(x2) simple_intropattern(x3)
                          simple_intropattern(x4) simple_intropattern(x5)
                          simple_intropattern(x6) simple_intropattern(x7)
                          simple_intropattern(x8) := 
  right_intro x0; right_intro x1;right_intro x2; right_intro x3;right_intro x4; right_intro x5;
  right_intro x6; right_intro x7;right_intro x8; pureIntros.



Tactic Notation "Exists" uconstr(x0) := asrt_simpl;rexists x0.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) := asrt_simpl;rexists x0;asrt_simpl;rexists x1.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2;asrt_simpl;rexists x3.
Tactic Notation "Exists" uconstr(x0) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) := asrt_simpl;rexists x0;asrt_simpl;rexists x1;asrt_simpl;rexists x2;asrt_simpl;rexists x3;asrt_simpl;rexists x4.


Tactic Notation "Left" := rewrite <- derivable1_orp_intros1.
Tactic Notation "Right" := rewrite <- derivable1_orp_intros2.


Ltac sepcon_liftIters P :=  
  match P with 
  | ?x ** ?y => sepcon_liftIters y;sepcon_liftIters x
  | ?x => sepcon_lift x
  end.
  
Ltac sep_apply_pre H := match type of H with | ?P |--?Q => sepcon_liftIters P end.


Ltac asrt_get_after_n p n :=
    match n with
      | 0%nat => constr:(Some p)
      | S ?n' =>
        match p with
          | ?p' ** ?q' => asrt_get_after_n q' n'
          | _ => constr:(@None)
        end
    end.
Ltac sep_remember y p a:=
      match asrt_get_after_n p y with
        | @None => fail 1
        | Some ?p' => remember p' as a
      end.

Ltac L_sepcon_lift'' p :=
  match goal with 
  | |- ?P |-- ?Q  => match P with 
                    | context [?x ** p] => erewrite (sepcon_comm_logic_equiv x p) ; unfoldimpmodel
                    | context [?x ** (p ** ?y) ] => erewrite (sepcon_swap_logic_equiv x p y) 
                    end
  end.

Ltac L_sepcon_lift' p := L_sepcon_lift'' p ;
  repeat progress (L_sepcon_lift'' p).

Ltac sep_lift_L_aux L :=
  match L with 
  | nil => idtac 
  | cons (PV ?x @ vptr ↦ₗ ?v $ ?pm) ?l' => strongseplift (PV x @ vptr ↦ₗ v $ pm); sep_lift_L_aux l'
  | cons (PV ?x @ vint ↦ₗ ?v $ ?pm) ?l' => strongseplift (PV x @ vint ↦ₗ v $ pm); sep_lift_L_aux l'
  | cons ?p ?l' => strongseplift p; sep_lift_L_aux l'
  end.

Ltac sep_lift_L L :=
  let revl := eval cbn [List.rev List.app] in (List.rev L) in sep_lift_L_aux revl.

Ltac sep_remember_L  L :=
  let n := eval compute in (length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; 
        let a:= fresh "P" in 
        match goal with 
        | |- ?P |--_ =>  sep_remember n P a end;
        strongseplift a
  end.

Ltac sep_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; unfoldimpmodel; (rewrite h ||
        let a:= fresh "P" in 
        match goal with 
        | |- ?P |-- _ =>  sep_remember n P a end;
        try (strongseplift a);rewrite h; subst a)
  end.

Ltac prop_rewrite h:= rewrite (prop_add_left _ _ h) at 1.

Ltac prop_apply_L L h:=
  let n := eval compute in (List.length L) in 
  match n with 
  | O => fail "nil list"
  | _ => asrt_simpl; sep_lift_L L; try rewrite !derivable1_sepcon_assoc1; unfoldimpmodel;  ( prop_rewrite h ||
        let a:= fresh "P" in 
        match goal with 
        | |- ?P |-- _ =>  sep_remember n P a end;
        try (L_sepcon_lift' a); prop_rewrite h; subst a)
  end.

Ltac exact_last Q :=
  match Q with 
  | ?A && ?B => exact_last B 
  | ?p => constr:(p)
  end.

Ltac unify_asrt x Q :=
  match Q with 
  | ?A ** ?B => (unify_asrt x A)
  | ?A ** ?B => unify_asrt x B
  | ?y => unify x y
  end.

Ltac unify_asrts P Q :=
  match P with 
  | ?A ** ?B => (unify_asrts A Q); (unify_asrts B Q)
  | ?x => unify_asrt x Q 
  end.


Ltac unify_prewithgoal  P :=
  match goal with 
  | |- ?Q  |-- _ => let Q' := (exact_last Q) in unify_asrts P Q' 
  end.

Ltac  sepconlistasrts_rec P L :=
  match P with 
  | ?A ** ?B => let L1  :=  (sepconlistasrts_rec A (@nil expr)) in 
                let L2 :=  (sepconlistasrts_rec B L) in
                let l:= eval cbn [List.app] in (List.app L1  L2) in
                  constr:(l)
  | ?x => constr:(cons x L)
  end.

Ltac sepconlistasrts P :=
  let l:= (sepconlistasrts_rec P (@nil expr)) in 
  constr:(l).

Ltac sep_apply H :=
  let h:= fresh "Hlemma" in pose proof H as h;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- ?Q => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in sep_apply_L L h;clear  h
                  end
  | ?P --||-- ?Q => find_lemmapre_rec (P |-- Q)
  end) in find_lemmapre_rec h.

Ltac prop_apply H :=
  let h:= fresh "Hlemma" in pose proof H as h;
  let rec find_lemmapre_rec h :=
   (lazymatch type of h with
  | forall x:?T, _ => lazymatch type of T with
                      | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                      | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                              find_lemmapre_rec h
                      end
  | ?T -> _ => lazymatch type of T with
                | Prop => let H' := fresh "H" in cut (T);[ intro H'; specialize (h H'); find_lemmapre_rec h | ]
                | _ => let _x := fresh "_x"  in evar (_x : T); specialize(h _x);subst _x;
                      find_lemmapre_rec h
                end
  | ?P |-- (@basicasrt.coq_prop _ ?Q)  => unify_prewithgoal P;
                  match type of h with 
                  | ?P |-- _ =>  let L:= (sepconlistasrts P) in prop_apply_L L h;clear  h
                  end
  end) in find_lemmapre_rec h.


(* closed tacs *)
Ltac solve_closedlvars tac := 
  repeat progress match goal with 
  | |- closed_wrt_lvars ?vs (GV ?x ↦ₗ ?v) => apply (closedlvars_GV x v vs)
  | |- closed_wrt_lvars ?vs (PV ?x ↦ₗ ?v $ ?pm) => apply (closedlvars_PV pm x v vs)
  | |- closed_wrt_lvars ?vs emp => apply closedlvars_emp
  | |- closed_wrt_lvars ?vs ((@basicasrt.coq_prop _ ?B)) => apply (closedlvars_coqprop B vs)
  | |- closed_wrt_lvars ?vs (listrep ?pm ?p ?l) => apply (closedlvars_listrep pm l p vs)
  | |- closed_wrt_lvars ?vs (?P && ?Q) => apply (closedlvars_andp P Q vs)
  | |- closed_wrt_lvars ?vs (?P ** ?Q) => apply (closedlvars_sepcon P Q vs)
  | |- closed_wrt_lvars ?vs ( @basicasrt.exp ?s ?t ?P ) => apply (closedlvars_exp P vs);intro
  | |- _ => tac
  end.

Ltac solve_closedgvars tac := 
  repeat progress match goal with 
  | |- closed_wrt_gvars ?vs (LV ?x ↦ₗ ?v) => apply (closedgvars_LV x v vs)
  | |- closed_wrt_gvars ?vs (PV ?x ↦ₗ ?v $ ?pm) => apply (closedgvars_PV pm x v vs)
  | |- closed_wrt_gvars ?vs emp => apply closedgvars_emp
  | |- closed_wrt_gvars ?vs ((@basicasrt.coq_prop _ ?B)) => apply (closedgvars_coqprop B vs)
  | |- closed_wrt_gvars ?vs (listrep ?pm ?p ?l) => apply (closedgvars_listrep pm l p vs)
  | |- closed_wrt_gvars ?vs (?P && ?Q) => apply (closedgvars_andp P Q vs)
  | |- closed_wrt_gvars ?vs (?P ** ?Q) => apply (closedgvars_sepcon P Q vs)
  | |- closed_wrt_gvars ?vs ( @basicasrt.exp ?s ?t ?P ) => apply (closedgvars_exp P vs);intro
  | |- _ => tac
  end. 



Ltac destruct_arrow_aux w B :=
  match B with 
  | Prop => let X := fresh "X" in destruct w as [w B]
  | _ -> ?C =>  destruct_arrow_aux w C 
  end.

Ltac destruct_prodtype_aux w B :=
  match B with 
  | value => let v := fresh "v" in destruct w as [w v]
  | list ?A => let l := fresh "l" in destruct w as [w l]
  | Z => let z := fresh "z" in destruct w as [w z]
  | Perm.t => let c := fresh "t" in destruct w as [w v]
  | ?C -> ?D => destruct_arrow_aux w B 
  | _ => let v := fresh "v" in destruct w as [w v]
  end.


Ltac renmae_arrow_type w A :=
  match A with 
  | Prop => let X := fresh "X" in rename w into X
  | _ -> ?C =>  renmae_arrow_type w C
  end.

Ltac rename_type w A :=
  match A with 
  | value => let v := fresh "v" in rename w into v
  | list ?B => let l := fresh "l" in rename w into l
  | Z => let z := fresh "z" in rename w into z
  | Perm.t => let c := fresh "t" in  rename w into v
  | ?C -> ?D => renmae_arrow_type w D
  | _ => let v := fresh "v" in rename w into v
  end.

Ltac destruct_prodtype w :=
  lazymatch type of w with 
  | (?A * ?B)%type  => destruct_prodtype_aux w B;destruct_prodtype w
  | (?A)%type  => rename_type w A 
  end.
 

