Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list.
Local Open Scope Z_scope.
Require Import Lia.
Require Import Coq.Logic.Classical_Prop.
Require Import type_infer_lib.

(*
Lemma refine_origin_impl_revised: forall sc scf
	(C_sc: sol_compressed sc)
	(C_scf: sol_compressed scf)
	(Rf1: sol_refine sc scf),
	sol_refine_revised sc scf.
Proof.
	intros.
	red in Rf1.
	red.
	induction t.
	3, 4: simpl; f_equal; auto.
	2: simpl; auto.
	specialize (Rf1 n).
	unfold type_subst at 3.
	destruct (sc n) eqn: Hn.
	- unfold type_subst at 1.
		rewrite Rf1. reflexivity.
	- reflexivity.
Qed.

Lemma refine_revised_no_var_impl_origin: forall sc scf
	(C_sc: sol_compressed sc)
	(C_scf: sol_compressed scf)
	(NoVar: sol_no_var scf)
	(Rf1: sol_refine_revised sc scf),
	sol_refine sc scf.
Proof.
	intros.
	red in Rf1.
	intros n.
  destruct (sc n) eqn: Hscn; [ | tauto ].
	specialize (Rf1 (TVar n)).
	unfold type_subst in Rf1 at 1 3.
	rewrite Hscn in Rf1.

	destruct (scf n) eqn: Hscfn.
	1: f_equal; assumption.
	exfalso.
	destruct t eqn: Ht; inversion Rf1.
	subst t.
	destruct (scf n0) eqn: Hscfn0.
	- subst t.
		specialize (NoVar n0).
		rewrite Hscfn0 in NoVar.
		contradiction.
	- inversion H0.
	  subst n0.
		clear H0 Hscfn0.
		specialize (C_sc n n).
		rewrite Hscn in C_sc.
		congruence.
Qed.

Lemma correct_revise1_impl_revise2: forall (t1 t2: TypeTree) (sc scp: sol)
	(C_sc: sol_compressed sc)
	(C_scp: sol_compressed scp)
	(Correct: sol_correct_iter_revise1 t1 t2 sc scp),
	sol_correct_iter_revise2 t1 t2 sc scp.
Proof.
	intros.
	red in Correct.
	intros sf C_sf NoVar_sf.
	specialize (Correct sf C_sf).
	destruct Correct as [Correct1 Correct2].
	split.
	+ intros [V R].
		eapply refine_revised_no_var_impl_origin; auto.
		apply Correct1.
		intuition.
		eapply refine_origin_impl_revised; auto.
	+ intros R.
		pose proof (refine_origin_impl_revised _ _ C_scp C_sf R).
		specialize (Correct2 H).
	  intuition.
		eapply refine_revised_no_var_impl_origin; auto.
Qed.

Lemma unify_sound_revised1_impl_revised2:
	unify_sound_revised1 -> unify_sound_revised2.
Proof.
	red.
	intros.
	specialize (H t1 t2 s_pre s_post s_cpre H0 H1 H2 H3).
	destruct H as [ s_cpost  H ].
	exists s_cpost.
	intuition.
	apply correct_revise1_impl_revise2; auto.
	apply (proj1 H0).
	apply (proj1 H4).
Qed. *)
