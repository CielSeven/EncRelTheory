From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
From SimpleC.SL Require Import Mem Assertion.

Local Open Scope sac_scope.
Import CRules.

Inductive Werror : Type :=
| Werr : Werror
.

Inductive Wtype : Type :=
| TyZ
| TyError
.

Definition wtype_eq : Wtype -> Wtype -> bool :=
    fun a b =>
        match a, b with
        | TyZ, TyZ => true
        | TyError, TyError => true
        | _, _ => false
        end.

Definition wtype_eq_dec : forall (a b : Wtype), {a = b} + {a <> b}.
    refine (fun a b =>
              match a, b with
              | TyZ, TyZ => left eq_refl
              | TyError, TyError => left eq_refl
              | _, _ => right _
              end); abstract discriminate.
Defined.

Definition wtype_denote (ty : Wtype) : Type :=
    match ty with
    | TyZ => Z
    | TyError => Werror
    end.

Definition TypeMapping : Type := Z -> Wtype.

Definition empty_type_mapping : TypeMapping := fun (x : Z) => TyError.

Definition type_mapping_lookup (ty_env : TypeMapping) (x : Z) : Wtype :=
    ty_env x.

Definition type_mapping_update (ty_env : TypeMapping) (x : Z) (ty : Wtype) : TypeMapping :=
    fun y => if Z.eq_dec x y then ty else type_mapping_lookup ty_env y.

Lemma type_mapping_update_eq : forall (ty_env : TypeMapping) (x : Z) (ty : Wtype),
    ty = type_mapping_lookup (type_mapping_update ty_env x ty) x.
Proof.
    intros.
    unfold type_mapping_lookup, type_mapping_update.
    destruct (Z.eq_dec x x); [ reflexivity | contradiction ].
Qed.

Lemma type_mapping_update_neq : forall (ty_env : TypeMapping) (x y : Z) (ty : Wtype),
    x <> y -> type_mapping_lookup ty_env y = type_mapping_lookup (type_mapping_update ty_env x ty) y.
Proof.
    intros.
    unfold type_mapping_lookup, type_mapping_update.
    destruct (Z.eq_dec x y); [ contradiction | reflexivity ].
Qed.
(* 
Definition fmap_type {A : Type} (f : A -> Type) (x : option A) : Type :=
    match x with
    | None => option unit
    | Some y => option (f y)
    end. *)

Definition TermMapping (ty_env : TypeMapping) : Type :=
    forall (n : Z), wtype_denote (type_mapping_lookup ty_env n).

Definition empty_term_mapping : (TermMapping empty_type_mapping).
    refine (fun (x : Z) => Werr).
Defined.

Definition term_mapping_lookup (ty_env : TypeMapping)
                               (tm_env : TermMapping ty_env)
                               (x : Z) :
                               wtype_denote (type_mapping_lookup ty_env x) :=
    tm_env x.

Definition term_mapping_update (ty_env : TypeMapping)
                               (tm_env : TermMapping ty_env)
                               (x : Z)
                               (ty : Wtype)
                               (v : wtype_denote ty) :
                               TermMapping (type_mapping_update ty_env x ty).
    refine (fun y =>
              match (Z.eq_dec x y) with
              | left _ => _
              | right _ => _
              end).
    - rewrite <- e.
      erewrite type_mapping_update_eq in v.
      apply v.
    - pose (ans := (term_mapping_lookup ty_env tm_env y)).
      erewrite type_mapping_update_neq in ans.
      apply ans.
      assumption.
Defined.

Lemma term_mapping_update_eq :
    forall (ty_env : TypeMapping) (tm_env : TermMapping ty_env) (x : Z) (ty : Wtype) (v : wtype_denote ty),
        term_mapping_lookup (type_mapping_update ty_env x ty) (term_mapping_update ty_env tm_env x ty v) x =
        eq_rect ty wtype_denote v (type_mapping_lookup (type_mapping_update ty_env x ty) x)
            (type_mapping_update_eq ty_env x ty).
    intros.
    unfold term_mapping_lookup, term_mapping_update.
    destruct (Z.eq_dec x x); try contradiction.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.Eq_rect_eq.eq_rect_eq.
    reflexivity.
Qed.

Definition def_term_mapping_update_neq : Prop.
    refine (forall (ty_env : TypeMapping) (tm_env : TermMapping ty_env) (x y : Z) (ty : Wtype) (v : wtype_denote ty) (H : x <> y),
              term_mapping_lookup (type_mapping_update ty_env x ty) (term_mapping_update ty_env tm_env x ty v) y = _).
    rewrite <- type_mapping_update_neq.
    apply (term_mapping_lookup ty_env tm_env y).
    apply H.
Defined.

Lemma term_mapping_update_neq :
    forall (ty_env : TypeMapping) (tm_env : TermMapping ty_env) (x y : Z) (ty : Wtype) (v : wtype_denote ty)
           (H : x <> y),
        term_mapping_lookup (type_mapping_update ty_env x ty) (term_mapping_update ty_env tm_env x ty v) y =
        eq_rect (type_mapping_lookup ty_env y) (fun w : Wtype => wtype_denote w) (term_mapping_lookup ty_env tm_env y)
            (type_mapping_lookup (type_mapping_update ty_env x ty) y) (type_mapping_update_neq ty_env x y ty H).
    unfold def_term_mapping_update_neq.
    intros.
    unfold term_mapping_lookup, term_mapping_update.
    destruct (Z.eq_dec x y).
    - contradiction.
    - unfold term_mapping_lookup.
      assert (n = H) by apply proof_irrelevance.
      rewrite H0; reflexivity.
Qed.

(* Definition consistent_mapping_ (ty_env : TypeMapping) (tm_env : TermMapping ty_env) :
    forall (x : Z) (ty : Wtype),
        ty = (type_mapping_lookup ty_env x) ->
        exists (a : wtype_denote ty), term_mapping_lookup ty_env tm_env x = a.
    refine ((forall (x : Z),
               match type_mapping_lookup ty_env x with
               | inleft (@existT _ _ a _) => exists (a' : wtype_denote a), term_mapping_lookup ty_env tm_env x = _
               | inright _ => term_mapping_lookup ty_env tm_env x = _
               end)).
    - rewrite e; simpl; apply (Some a').
    - rewrite e; simpl; apply None.
Defined. *)
(* 
Lemma empty_mapping_consistent: consistent_mapping empty_type_mapping empty_term_mapping.
Proof.
    unfold consistent_mapping.
    reflexivity.
Qed.

Lemma update_mapping_consistent:
  forall (ty_env : TypeMapping) (tm_env : TermMapping ty_env) (x : Z) (ty : Wtype) (v : wtype_denote ty),
    consistent_mapping ty_env tm_env ->
    consistent_mapping (type_mapping_update ty_env x ty) (term_mapping_update ty_env tm_env x ty v).
Proof.
    unfold consistent_mapping; intros.
    destruct (Z.eq_dec x x0).
    - subst x0.
      destruct (option_dec (type_mapping_lookup (type_mapping_update ty_env x ty) x)).
      + destruct s.
        assert (H1 : x0 = ty). {
            clear - e.
            rewrite type_mapping_update_eq in e.
            injection e; intros.
            symmetry; assumption.
        }
        subst x0.
        exists v.

        eq_rect_r
      rewrite type_mapping_update_eq in e. *)

Inductive Ctype : Type :=
| Cint
.

forall 1 2, (1 |-> 2) |-- (1 |-> 2)

Inductive Wexpr : Wtype -> Type :=
| EVar (x : Z) (ty : Wtype) : Wexpr ty
| EConstZ (val : Z) : Wexpr TyZ
.

Inductive SepAtomTerm : Type :=
| TSepDataAt (addr : Wexpr TyZ) (ty : Ctype) (val : Wexpr TyZ)
.

Inductive SepTerm : Type :=
| TSepCon (t : SepAtomTerm) (t1 : SepTerm)
| TSepLeaf (t : SepAtomTerm)
.

Inductive ExistsTerm : Type :=
| TExists (x : Z) (ty : Wtype) (t : ExistsTerm)
| TSep (t : SepTerm)
.

Inductive ForallTerm : Type :=
| TForall (x : Z) (ty : Wtype) (t : ForallTerm)
| TEntail (pre : ExistsTerm) (post : ExistsTerm)
.

Definition check_valid_expr {A : Wtype} (t : Wexpr A) (env : TypeMapping) : Prop :=
    match t with
    | EVar x ty => type_mapping_lookup env x = ty
    | EConstZ _ => True
    end.

Definition check_valid_sep_atom (t : SepAtomTerm) (env : TypeMapping) : Prop :=
    match t with
    | TSepDataAt addr ty val => check_valid_expr addr env /\ check_valid_expr val env
    end.

Fixpoint check_valid_sep (t : SepTerm) (env : TypeMapping) : Prop :=
    match t with
    | TSepCon t1 t2 => check_valid_sep_atom t1 env /\ check_valid_sep t2 env
    | TSepLeaf t' => check_valid_sep_atom t' env
    end.

Lemma check_valid_sep_unfold :
    forall t env,
        check_valid_sep t env = match t with
                                | TSepCon t1 t2 => check_valid_sep_atom t1 env /\ check_valid_sep t2 env
                                | TSepLeaf t' => check_valid_sep_atom t' env
                                end.
    intros.
    unfold check_valid_sep at 1.
    destruct t; reflexivity.
Qed.

Fixpoint check_valid_exists (t : ExistsTerm) (env : TypeMapping) : Prop :=
    match t with
    | TExists x ty t' => check_valid_exists t' (type_mapping_update env x ty)
    | TSep t' => check_valid_sep t' env
    end.

Lemma check_valid_exists_unfold :
    forall t env,
        check_valid_exists t env = match t with
                                   | TExists x ty t' => check_valid_exists t' (type_mapping_update env x ty)
                                   | TSep t' => check_valid_sep t' env
                                   end.
    intros.
    unfold check_valid_exists at 1.
    destruct t; reflexivity.
Qed.

Fixpoint check_valid_forall (t : ForallTerm) (env : TypeMapping) : Prop :=
    match t with
    | TForall x ty t' => check_valid_forall t' (type_mapping_update env x ty)
    | TEntail pre post => check_valid_exists pre env /\ check_valid_exists post env
    end.

Lemma check_valid_forall_unfold :
    forall t env,
        check_valid_forall t env = match t with
                                   | TForall x ty t' => check_valid_forall t' (type_mapping_update env x ty)
                                   | TEntail pre post => check_valid_exists pre env /\ check_valid_exists post env
                                   end.
    intros.
    unfold check_valid_forall at 1.
    destruct t; reflexivity.
Qed.

Definition wexpr_denote : forall (ty : Wtype) (e : Wexpr ty)
                                 (ty_env : TypeMapping)
                                 (H : check_valid_expr e ty_env)
                                 (tm_env : TermMapping ty_env), wtype_denote ty.
    refine (fix f (ty : Wtype) (e : Wexpr ty)
                  (ty_env : TypeMapping)
                  (H : check_valid_expr e ty_env)
                  (tm_env : TermMapping ty_env) : wtype_denote ty := _).
    destruct e.
    - simpl in H.
      subst ty.
      apply (term_mapping_lookup ty_env tm_env x).
    - simpl in H.
      apply val.
Defined.

Definition sep_atom_term_denote : forall (t : SepAtomTerm)
                                         (ty_env : TypeMapping)
                                         (H : check_valid_sep_atom t ty_env)
                                         (tm_env : TermMapping ty_env), model -> Prop.
    refine (fix f (t : SepAtomTerm)
                  (ty_env : TypeMapping)
                  (H : check_valid_sep_atom t ty_env)
                  (tm_env : TermMapping ty_env) : model -> Prop := _).
    destruct t.
    simpl in H; destruct H as [ H1 H2 ].
    apply (wexpr_denote _ addr ty_env H1 tm_env # Int |-> wexpr_denote _ val ty_env H2 tm_env).
Defined.

Definition sep_term_denote : forall (t : SepTerm)
                                    (ty_env : TypeMapping)
                                    (H : check_valid_sep t ty_env)
                                    (tm_env : TermMapping ty_env), model -> Prop.
    refine (fix f (t : SepTerm)
                  (ty_env : TypeMapping)
                  (H : check_valid_sep t ty_env)
                  (tm_env : TermMapping ty_env) : model -> Prop := _).
    destruct t; rewrite check_valid_sep_unfold in H.
    - destruct H as [ H0 H1 ].
      apply ((sep_atom_term_denote t ty_env H0 tm_env) ** (f t0 ty_env H1 tm_env)).
    - apply (sep_atom_term_denote t ty_env H tm_env).
Defined.

Definition exists_term_denote : forall (t : ExistsTerm)
                                       (ty_env : TypeMapping)
                                       (H : check_valid_exists t ty_env)
                                       (tm_env : TermMapping ty_env), model -> Prop.
    refine (fix f (t : ExistsTerm)
                  (ty_env : TypeMapping)
                  (H : check_valid_exists t ty_env)
                  (tm_env : TermMapping ty_env) : model -> Prop := _).
            (* match t with
            | TExists x ty t' => EX (v : wtype_denote ty),
                                  f t' (type_mapping_update ty_env x ty) _ (term_mapping_update ty_env tm_env x ty v)
            | TSep t' => sep_term_denote t' ty_env _ tm_env
            end). *)
    destruct t; rewrite check_valid_exists_unfold in H;
    [ apply (EX (v : wtype_denote ty),
               f t (type_mapping_update ty_env x ty) H (term_mapping_update ty_env tm_env x ty v)) |
      apply (sep_term_denote t ty_env H tm_env) ].
Defined.

Definition forall_term_denote : forall (t : ForallTerm)
                                       (ty_env : TypeMapping)
                                       (H : check_valid_forall t ty_env)
                                       (tm_env : TermMapping ty_env), Prop.
    refine (fix f (t : ForallTerm)
                  (ty_env : TypeMapping)
                  (H : check_valid_forall t ty_env)
                  (tm_env : TermMapping ty_env) : Prop := _).
            (* match t with
            | TForall x ty t' => forall (v : wtype_denote ty),
                                     f t' (type_mapping_update ty_env x ty) _ (term_mapping_update ty_env tm_env x ty v)
            | TEntail pre post => exists_term_denote pre ty_env _ tm_env |-- exists_term_denote post ty_env _ tm_env
            end). *)
        (destruct t; rewrite check_valid_forall_unfold in H;
        [ apply (forall (v : wtype_denote ty),
                    f t (type_mapping_update ty_env x ty) H (term_mapping_update ty_env tm_env x ty v)) |
          destruct H as [ H0 H1 ];
          apply (exists_term_denote pre ty_env H0 tm_env |-- exists_term_denote post ty_env H1 tm_env) ]).
Defined.

Print forall_term_denote.

(* Definition ExampleForallTerm0 : ForallTerm :=
    (TForall 0 TyZ (TForall 1 TyZ (TEntail
    (TSep (TSepCon (TSepDataAt (EVar 0 TyZ) Cint (EVar 1 TyZ)) (TSepLeaf (TSepDataAt (EVar 1 TyZ) Cint (EVar 0 TyZ)))))
    (TSep (TSepCon (TSepDataAt (EVar 0 TyZ) Cint (EVar 1 TyZ)) (TSepLeaf (TSepDataAt (EVar 1 TyZ) Cint (EVar 0 TyZ)))))
    ))). *)
    
Definition ExampleForallTerm0 : ForallTerm :=
    (TForall 0 TyZ (TForall 1 TyZ (TEntail
    (TSep (TSepLeaf (TSepDataAt (EVar 1 TyZ) Cint (EVar 0 TyZ))))
    (TSep (TSepLeaf (TSepDataAt (EVar 1 TyZ) Cint (EVar 0 TyZ))))
    ))).

Lemma check_valid_example_forall_term0 :
    check_valid_forall ExampleForallTerm0 empty_type_mapping.
    repeat split.
Qed.

(* Compute (forall_term_denote ExampleForallTerm0 empty_type_mapping check_valid_example_forall_term0 empty_term_mapping). *)

Definition Provable (T : ForallTerm) (H : check_valid_forall T empty_type_mapping) : Prop :=
    forall_term_denote T empty_type_mapping H empty_term_mapping.

Parameter strategy1 : Type.
Parameter apply_strategy1 : ForallTerm -> strategy1 -> option ForallTerm.
Fixpoint apply_strategies (T : ForallTerm) (strategies : list strategy1) : option ForallTerm :=
    match strategies with
    | [] => Some T
    | s :: ss =>
        match apply_strategy1 T s with
        | Some T' => apply_strategies T' ss
        | None => None
        end
    end.

Parameter rc : list strategy1 -> ForallTerm.

Theorem soundness : forall (T1 T2 : ForallTerm) (strategies : list strategy1),
    Provable (rc strategies) -> apply_strategies T1 strategies = Some T2 -> Provable T2 -> Provable T1.