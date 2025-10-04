From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
From SimpleC.SL Require Import Mem SeparationLogic
Require Import Program.

Import CRules.
Local Open Scope sac_scope.

Inductive Wtype : Type :=
| TyZ
.

Definition wtype_eqb : Wtype -> Wtype -> bool :=
  fun t1 t2 =>
    match t1, t2 with
    | TyZ, TyZ => true
    end.

Definition wtype_eq_dec : forall t1 t2 : Wtype, {t1 = t2} + {t1 <> t2}.
    refine (fun t1 t2 =>
              match t1, t2 with
              | TyZ, TyZ => left eq_refl
              end).
Defined.

Lemma wtype_eq_refl :
    forall ty, wtype_eqb ty ty = true.
    intros; destruct ty; reflexivity.
Qed.

Lemma wtype_eqb_eq :
    forall ty1 ty2, wtype_eqb ty1 ty2 = true <-> ty1 = ty2.
    split; intros.
    - destruct ty1; destruct ty2; try reflexivity; try discriminate.
    - rewrite H; apply wtype_eq_refl.
Qed.

Definition wtype_denote (t : Wtype) : Type :=
  match t with
  | TyZ => Z
  end.

Definition wtype_default (t : Wtype) : wtype_denote t :=
    match t with
    | TyZ => 0%Z
    end.

Definition TermMapping : Type :=
    forall (n : Z) (ty : Wtype), wtype_denote ty.

Definition empty_mapping : TermMapping :=
    (fun (n : Z) (ty : Wtype) => wtype_default ty).

Definition term_mapping_update (env : TermMapping) (n : Z) (ty : Wtype) (v : wtype_denote ty) :=
    fun (n' : Z) (ty' : Wtype) =>
        match (Z.eq_dec n n') with
        | left _ => match (wtype_eq_dec ty ty') with
                    | left H => eq_rect _ wtype_denote v _ H
                    | right _ => env n' ty'
                    end
        | right _ => env n' ty'
        end.

Lemma term_mapping_update_lookup :
    forall (env : TermMapping) (n : Z) (ty : Wtype),
        (term_mapping_update env n ty (env n ty)) = env.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality_dep; intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n x); try reflexivity.
    destruct (wtype_eq_dec ty x0); try reflexivity.
    rewrite e, e0.
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma term_mapping_update_eq :
    forall (env : TermMapping) (n : Z) (ty : Wtype) (v : wtype_denote ty),
        (term_mapping_update env n ty v) n ty = v.
    intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n n); [ | contradiction ].
    destruct (wtype_eq_dec ty ty); [ | contradiction ].
    rewrite <- ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.eq_rect_eq.
    reflexivity.
Qed.

Lemma term_mapping_update_neq :
    forall (env : TermMapping) (n n' : Z) (ty ty' : Wtype) (v : wtype_denote ty),
        n <> n' \/ ty <> ty' ->
        (term_mapping_update env n ty v) n' ty' = env n' ty'.
    intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec n n').
    - destruct (wtype_eq_dec ty ty').
      + destruct H; contradiction.
      + reflexivity.
    - reflexivity.
Qed.

Inductive Ctype : Type :=
| Cint
.

Inductive Wexpr : Wtype -> Type :=
| EVar (x : Z) (ty : Wtype) : Wexpr ty
| EConstZ (val : Z) : Wexpr TyZ
.

Inductive SepAtomTerm : Type :=
| TSepDataAt (addr : Wexpr TyZ) (ty : Ctype) (val : Wexpr TyZ)
.

Definition SepTerm : Type := list SepAtomTerm.

Definition VarType : Type := Z * Wtype.
Definition VarList : Type := list VarType.

Inductive ExistsTerm : Type :=
| TExists (vl : VarList) (t : SepTerm)
.

Inductive ForallTerm : Type :=
| TForall (vl : VarList) (pre : ExistsTerm) (post : ExistsTerm)
.

Definition ExistsCons (x : VarType) (t : ExistsTerm) :=
    match t with
    | TExists vl pre => TExists (x :: vl) pre
    end.

Lemma ind_exists :
    forall (t : ExistsTerm),
    forall (P : ExistsTerm -> Prop),
    (forall sep, P (TExists nil sep)) ->
    (forall x t, P t -> P (ExistsCons x t)) ->
    P t.
    intros.
    destruct t.
    induction vl.
    - apply H.
    - specialize (H0 a (TExists vl t)).
      simpl in H0.
      apply (H0 IHvl).
Qed.

Definition ForallCons (x : VarType) (t : ForallTerm) :=
    match t with
    | TForall vl pre post => TForall (x :: vl) pre post
    end.

Lemma ind_forall :
    forall (t : ForallTerm),
    forall (P : ForallTerm -> Prop),
    (forall pre post, P (TForall nil pre post)) ->
    (forall x t, P t -> P (ForallCons x t)) ->
    P t.
    intros.
    destruct t.
    induction vl.
    - apply H.
    - specialize (H0 a (TForall vl pre post)).
      simpl in H0.
      apply (H0 IHvl).
Qed.

Definition wexpr_denote (ty : Wtype) (e : Wexpr ty)
                        (env : TermMapping) : wtype_denote ty :=
    match e in (Wexpr w) return (wtype_denote w) with
    | EVar x ty' => env x ty'
    | EConstZ val => val
    end.

Definition sep_atom_term_denote (t : SepAtomTerm) (env : TermMapping) : model -> Prop :=
    match t with
    | TSepDataAt addr ty val =>
      (wexpr_denote _ addr env # Int |-> wexpr_denote _ val env)
    end.

Definition sep_term_denote (t : SepTerm) (env : TermMapping) : model -> Prop :=
    fold_right (fun b a => a ** sep_atom_term_denote b env) emp t.

Fixpoint var_list_exists_denote (vl : VarList) (env : TermMapping) (cont : TermMapping -> model -> Prop) : model -> Prop :=
    match vl with
    | cons (x, ty) vls =>
        EX v : wtype_denote ty, var_list_exists_denote vls (term_mapping_update env x ty v) cont
    | nil => cont env
    end.

Fixpoint var_list_forall_denote (vl : VarList) (env : TermMapping) (cont : TermMapping -> Prop) : Prop :=
    match vl with
    | cons (x, ty) vls =>
        forall v : wtype_denote ty, var_list_forall_denote vls (term_mapping_update env x ty v) cont
    | nil => cont env
    end.

Definition exists_term_denote (t : ExistsTerm) (env : TermMapping) : model -> Prop :=
    match t with
    | TExists vl t' => var_list_exists_denote vl env (sep_term_denote t')
    end.

Lemma exists_term_denote_nil :
    forall (t : SepTerm) (env : TermMapping),
        exists_term_denote (TExists nil t) env = sep_term_denote t env.
    intros; simpl; reflexivity.
Qed.

Lemma exists_term_denote_cons : forall (x : Z) (ty : Wtype) (t : ExistsTerm) (env : TermMapping),
    exists_term_denote (ExistsCons (x, ty) t) env =
    EX v : wtype_denote ty, exists_term_denote t (term_mapping_update env x ty v).
    intros.
    unfold exists_term_denote.
    unfold ExistsCons.
    destruct t.
    simpl.
    reflexivity.
Qed.

Definition forall_term_denote (t : ForallTerm) (env : TermMapping) : Prop :=
    match t with
    | TForall vl pre post => var_list_forall_denote vl env
        (fun env => (exists_term_denote pre env) |-- (exists_term_denote post env))
    end.

Lemma forall_term_denote_nil :
    forall (pre post : ExistsTerm) (env : TermMapping),
        forall_term_denote (TForall nil pre post) env =
        (exists_term_denote pre env |-- exists_term_denote post env).
    intros; simpl; reflexivity.
Qed.

Lemma forall_term_denote_cons : forall (x : Z) (ty : Wtype) (t : ForallTerm) (env : TermMapping),
    forall_term_denote (ForallCons (x, ty) t) env =
    forall v : wtype_denote ty, forall_term_denote t (term_mapping_update env x ty v).
    intros.
    unfold forall_term_denote.
    unfold ForallCons.
    destruct t.
    simpl.
    reflexivity.
Qed.

Definition Provable (t : ForallTerm) (env : TermMapping) : Prop :=
    forall_term_denote t env.

Inductive Operation : Type :=
| OLeftAdd (H : SepAtomTerm)
| OLeftErase (H : SepAtomTerm)
| ORightAdd (H : SepAtomTerm)
| ORightErase (H : SepAtomTerm)
(* | OLeftExistsAdd (v : VarType)
| OLeftExistsErase (v : VarType)
| ORightExistsAdd (v : VarType)
| ORightExistsErase (v : VarType) *)
.

Definition add_sep (t : SepTerm) (H : SepAtomTerm) :=
    H :: t.

(* Lemma add_sep_equiv :
    forall t H env,
        sep_term_denote (add_sep t H) env --||-- sep_atom_term_denote H env ** sep_term_denote t env.
    induction t; intros.
    - simpl.
      split.
      + destruct (IHt1 H env).
        sep_apply H0.
        entailer!.
      + destruct (IHt1 H env).
        sep_apply derivable1_sepcon_assoc1.
        sep_apply H1.
        entailer!.
    - simpl; split; entailer!.
    - simpl; split; entailer!.
Qed. *)

Definition wexpr_eqb (ty1 ty2 : Wtype) (e1 : Wexpr ty1) (e2 : Wexpr ty2) : bool :=
    wtype_eqb ty1 ty2 &&
    match e1, e2 with
    | EVar x1 ty1, EVar x2 ty2 => Z.eqb x1 x2
    | EConstZ val1, EConstZ val2 => Z.eqb val1 val2
    | _, _ => false
    end.

Lemma wexpr_eqb_eq :
    forall ty e1 e2,
        wexpr_eqb ty ty e1 e2 = true <-> e1 = e2.
    intros; split; intros.
    - unfold wexpr_eqb in H.
      rewrite andb_true_iff in H; destruct H.
      destruct e1.
      + destruct e2.
        * rewrite Z.eqb_eq in H0.
          subst x; reflexivity.
        * discriminate.
      + dependent destruction e2.
        * discriminate.
        * rewrite Z.eqb_eq in H0.
          rewrite H0; reflexivity.
    - rewrite H.
      unfold wexpr_eqb.
      destruct e2; apply andb_true_iff; split; try apply wtype_eq_refl; try apply Z.eqb_refl.
Qed.

Definition ctype_eqb : (Ctype -> Ctype -> bool) :=
    fun ty1 ty2 =>
        match ty1, ty2 with
        | Cint, Cint => true
        end.

Lemma ctype_eqb_eq :
    forall ty1 ty2,
        ctype_eqb ty1 ty2 = true <-> ty1 = ty2.
    intros.
    destruct ty1, ty2; simpl; split; intros; try reflexivity; try discriminate.
Qed.

Definition sep_atom_term_eqb (t1 : SepAtomTerm) (t2 : SepAtomTerm) : bool :=
    match t1, t2 with
    | TSepDataAt addr1 ty1 val1, TSepDataAt addr2 ty2 val2 =>
        (wexpr_eqb _ _ addr1 addr2) && (ctype_eqb ty1 ty2) && (wexpr_eqb _ _ val1 val2)
    end.

Lemma sep_atom_term_eqb_eq :
    forall t1 t2,
        sep_atom_term_eqb t1 t2 = true <-> t1 = t2.
    split; intros.
    - destruct t1, t2.
      unfold sep_atom_term_eqb in H.
      apply andb_true_iff in H; destruct H.
      apply andb_true_iff in H; destruct H.
      rewrite wexpr_eqb_eq in H, H0.
      rewrite ctype_eqb_eq in H1.
      rewrite H, H0, H1; reflexivity.
    - rewrite H.
      unfold sep_atom_term_eqb.
      destruct t2.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      all: try rewrite wexpr_eqb_eq;
           try rewrite ctype_eqb_eq;
           reflexivity.
Qed.

Lemma sep_atom_term_eqb_refl :
    forall t, sep_atom_term_eqb t t = true.
    intros; apply sep_atom_term_eqb_eq; reflexivity.
Qed.

Lemma sep_atom_term_eqb_eq_false :
    forall t1 t2,
        sep_atom_term_eqb t1 t2 = false -> t1 <> t2.
    intros.
    unfold not; intro H1.
    pose proof sep_atom_term_eqb_eq; edestruct H0.
    apply H3 in H1.
    rewrite H1 in H; discriminate.
Qed.

Lemma sep_atom_term_eq_dec :
    forall (a b : SepAtomTerm), {a = b} + {a <> b}.
    intros; destruct (sep_atom_term_eqb a b) eqn : H; [
        apply sep_atom_term_eqb_eq in H; apply (left H) |
        apply sep_atom_term_eqb_eq_false in H; apply (right H)
    ].
Qed.

(* Definition in_sep_atom_term (x : SepAtomTerm) (l : SepTerm) := In_dec sep_atom_term_eq_dec x l. *)

Fixpoint erase_sep (t : SepTerm) (H : SepAtomTerm) : option SepTerm :=
    match t with
    | nil => None
    | cons x xs =>
        if sep_atom_term_eqb x H
        then Some xs
        else match erase_sep xs H with
             | Some xs' => Some (x :: xs')
             | None => None
             end
    end.

Fixpoint erase_list_sep (t1 : SepTerm) (t2 : SepTerm) : option SepTerm :=
    match t2 with
    | nil => Some t1
    | cons x xs => match erase_list_sep t1 xs with
                  | Some t1' => erase_sep t1' x
                  | None => None
                  end
    end.

(* Lemma erase_sep_equiv :
    forall t H env t',
        erase_sep t H = Some t' ->
        sep_term_denote t env --||-- sep_atom_term_denote H env ** sep_term_denote t' env.
    induction t; intros.
    - simpl in *.
      destruct (erase_sep t1 H) eqn : ?.
      + destruct (IHt1 H env s Heqo).
        injection H0 as ?.
        subst t'; simpl.
        split.
        * sep_apply H1.
          entailer!.
        * sep_apply derivable1_sepcon_assoc1.
          sep_apply H2.
          entailer!.
      + destruct (erase_sep t2 H) eqn : ?.
        * destruct (IHt2 H env s Heqo0).
          injection H0 as ?.
          subst t'; simpl.
          split.
          -- sep_apply H1.
             sep_apply sepcon_swap_logic_equiv.
             entailer!.
          -- sep_apply sepcon_swap_logic_equiv.
             sep_apply H2.
             entailer!.
        * discriminate H0.
    - simpl in *.
      destruct (sep_atom_term_eqb t H) eqn : ?; try discriminate.
      injection H0 as H0; rewrite <- H0; simpl.
      apply sep_atom_term_eqb_eq in Heqb; subst t.
      split; entailer!.
    - simpl in H0; discriminate.
Qed. *)

Definition add_exists (t : ExistsTerm) (H : SepAtomTerm) :=
    match t with
    | TExists vl t => TExists vl (add_sep t H)
    end.

Definition erase_exists (t : ExistsTerm) (H : SepAtomTerm) : option ExistsTerm :=
    match t with
    | TExists vl t' =>
        match (erase_sep t' H) with
        | Some t'' => Some (TExists vl t'')
        | None => None
        end
    end.

Definition left_add_forall (t : ForallTerm) (H : SepAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl (add_exists pre H) post
    end.

Definition right_add_forall (t : ForallTerm) (H : SepAtomTerm) :=
    match t with
    | TForall vl pre post => TForall vl pre (add_exists post H)
    end.

Definition left_erase_forall (t : ForallTerm) (H : SepAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_exists pre H) with
        | Some pre' => Some (TForall vl pre' post)
        | None => None
        end
    end.

Definition right_erase_forall (t : ForallTerm) (H : SepAtomTerm) : option ForallTerm :=
    match t with
    | TForall vl pre post =>
        match (erase_exists post H) with
        | Some post' => Some (TForall vl pre post')
        | None => None
        end
    end.

Definition apply_operation (op : Operation) (t : option ForallTerm) : option ForallTerm :=
    match t with
    | Some t =>
        match op with
        | OLeftAdd H => Some (left_add_forall t H)
        | ORightAdd H => Some (right_add_forall t H)
        | OLeftErase H => left_erase_forall t H
        | ORightErase H => right_erase_forall t H
        end
    | None => None
    end.

Definition apply_operations (t : ForallTerm) (ops : list Operation) : option ForallTerm :=
    fold_right apply_operation (Some t) ops.

Lemma apply_operations_cons :
    forall op ops t,
    apply_operations t (op :: ops) = apply_operation op (apply_operations t ops).
    intros; simpl; reflexivity.
Qed.

Inductive RamificationCondition : Type :=
| RC (P P' Q' Q : SepTerm)
.

Definition var_type_eq_dec : forall (x y : VarType), {x = y} + {x <> y}.
    refine (fun x y => match x, y with
                       | (xf, xs), (yf, ys) =>
                           match Z.eq_dec xf yf with
                           | left _ => match wtype_eq_dec xs ys with
                                       | left _ => left _
                                       | right _ => right _
                                       end
                           | right _ => right _
                           end
                       end).
    - rewrite e, e0; reflexivity.
    - unfold not; intros.
      injection H; contradiction.
    - unfold not; intros.
      injection H; contradiction.
Defined.

Definition in_var_list x l := In_dec var_type_eq_dec x l.

Definition var_list_insert (x : VarType) (l : VarList) : VarList :=
    match in_var_list x l with
    | left _ => l
    | right _ => cons x l
    end.

Definition var_list_merge (l1 : VarList) (l2 : VarList) : VarList :=
    fold_left (fun a b => var_list_insert b a) l1 l2.

Definition var_list_no_intersection (l1 : VarList) (l2 : VarList) : Prop :=
    forall x, ~ (In x l1 /\ In x l2).

Definition get_var_list_expr (ty : Wtype) (e : Wexpr ty) : VarList :=
    match e with
    | EVar x ty => cons (x, ty) nil
    | _ => nil
    end.

Definition get_var_list_sep_atom (H : SepAtomTerm) : VarList :=
    match H with
    | TSepDataAt addr ty val =>
        var_list_merge (get_var_list_expr _ addr)
                        (get_var_list_expr _ val)
    end.

Definition get_var_list_sep_atom_list (l : list SepAtomTerm) : VarList :=
    fold_left (fun a b => var_list_merge a (get_var_list_sep_atom b)) l nil.

Definition get_var_list_rc (r : RamificationCondition) : VarList :=
    match r with
    | RC P P' Q' Q =>
        let vlP := get_var_list_sep_atom_list P in
        let vlP' := get_var_list_sep_atom_list P' in
        let vlQ' := get_var_list_sep_atom_list Q' in
        let vlQ := get_var_list_sep_atom_list Q in
        var_list_merge vlP (var_list_merge vlP' (var_list_merge vlQ' vlQ))
        end.

(* Definition gather_max_id_var_list (l : VarList) : Z :=
    fold_left (fun a b => Z.max a (fst b)) l 0%Z.

Definition gather_max_id_sep_atom (t : SepAtomTerm) : Z :=
    match t with
    | TSepDataAt addr ty val => Z.max (gather_max_id_var_list (get_var_list_expr _ addr))
                                      (gather_max_id_var_list (get_var_list_expr _ val))
    end.

Fixpoint gather_max_id_sep (t : SepTerm) : Z :=
    match t with
    | TSepCon t1 t2 => Z.max (gather_max_id_sep t1) (gather_max_id_sep t2)
    | TSepLeaf t => gather_max_id_sep_atom t
    | TSepEmp => 0%Z
    end.

Definition gather_max_id_exists (t : ExistsTerm) : Z :=
    match t with
    | TExists vl pre => Z.max (gather_max_id_var_list vl) (gather_max_id_sep pre)
    end.

Definition gather_max_id_forall (t : ForallTerm) : Z :=
    match t with
    | TForall vl pre post =>
        Z.max (gather_max_id_var_list vl) (Z.max (gather_max_id_exists pre) (gather_max_id_exists post))
    end. *)

(* Definition AlphaConversion : Type := Z -> Z.
Definition empty_alpha_conversion : AlphaConversion := (fun i => i).

(* swap(conv(key), conv(val)); should not affect injective property *)
Definition alpha_conversion_update (conv : AlphaConversion) (key : Z) (val : Z) :=
    fun y => if (Z.eq_dec key y) then val else
             if (Z.eq_dec val y) then key else
             conv y.

Definition injective_conversion (conv : AlphaConversion) :=
    forall x y, conv x = conv y -> x = y.

Lemma alpha_conversion_update_eq_key :
    forall (conv : AlphaConversion) (key val : Z),
        (alpha_conversion_update conv key val) key = val.
    intros.
    unfold alpha_conversion_update.
    destruct (Z.eq_dec key key); [ | contradiction ].
    reflexivity.
Qed.

Lemma alpha_conversion_update_eq_val :
    forall (conv : AlphaConversion) (key val : Z),
        (alpha_conversion_update conv key val) val = key.
    intros.
    unfold alpha_conversion_update.
    destruct (Z.eq_dec key val).
    - subst key; reflexivity.
    - destruct (Z.eq_dec val val); [ reflexivity | contradiction ].
Qed.

Lemma alpha_conversion_update_neq :
    forall (conv : AlphaConversion) (key val y : Z),
        key <> y -> val <> y -> (alpha_conversion_update conv key val) y = conv y.
    intros.
    unfold alpha_conversion_update.
    destruct (Z.eq_dec key y);
    destruct (Z.eq_dec val y);
    try contradiction;
    try reflexivity.
Qed.

Lemma empty_alpha_conversion_injective :
    injective_conversion empty_alpha_conversion.
    unfold injective_conversion, empty_alpha_conversion.
    intros; assumption.
Qed.

(* Do case analysis and use above lemma to simplify *)
Lemma alpha_conversion_update_injective :
    forall (conv : AlphaConversion) (key val : Z),
        injective_conversion conv ->
        injective_conversion (alpha_conversion_update conv key val).
Admitted.

Fixpoint get_conversion_var_list (vl : VarList) (tl : VarList) (conv : AlphaConversion) (cur_id : Z) :=
    match vl with
    | nil => (conv, cur_id)
    | v :: vs => if in_var_list v tl
                 then get_conversion_var_list vs tl (alpha_conversion_update conv (fst v) cur_id) (cur_id + 1)
                 else get_conversion_var_list vs tl conv cur_id
    end.

Definition get_conversion_forall (t : ForallTerm) (conv : AlphaConversion) (cur_id : Z) : AlphaConversion :=
    match t with
    | TForall vl (TExists pl pre) (TExists ql post) =>
        let (conv', cur_id') := get_conversion_var_list pl vl conv cur_id in
        let (ret_conv, _) := get_conversion_var_list ql (vl ++ pl) conv' cur_id' in
        ret_conv
    end. *)

(* Prove lemma about get_conversion_var_list :
       all modification of conv just maintains the injective property;
   Hence this lemma must hold *)
(* Lemma conversion_forall_injective :
    forall t conv,
    conv = get_conversion_forall t empty_alpha_conversion (gather_max_id_forall t) ->
    injective_conversion conv.
Admitted. *)

Definition not_appear_free_expr (ty : Wtype) (e : Wexpr ty) (x : Z) : Prop :=
    match e with
    | EVar y _ => x <> y
    | EConstZ _ => True
    end.

Definition not_appear_free_expr_bool (ty : Wtype) (e : Wexpr ty) (x : Z) : bool :=
    match e with
    | EVar y _ => negb (Z.eqb x y)
    | EConstZ _ => true
    end.

Lemma not_appear_free_expr_true :
    forall ty e x,
        not_appear_free_expr_bool ty e x = true <-> not_appear_free_expr ty e x.
    intros; destruct e; simpl.
    rewrite <- Z.eqb_neq.
    apply negb_true_iff.
    split; auto.
Qed.

Lemma not_appear_free_expr_false :
    forall ty e x,
        not_appear_free_expr_bool ty e x = false <-> ~ not_appear_free_expr ty e x.
    intros; destruct e; simpl.
    rewrite <- Z.eqb_neq.
    rewrite not_false_iff_true.
    apply negb_false_iff.
    split; intro H; [ discriminate H | contradiction ].
Qed.

Lemma not_appear_free_expr_equiv :
    forall ty e x,
        not_appear_free_expr ty e x ->
    forall env ty1 v,
        wexpr_denote ty e env = wexpr_denote ty e (term_mapping_update env x ty1 v).
    intros.
    unfold not_appear_free_expr in H.
    destruct e.
    - simpl; rewrite term_mapping_update_neq; [ reflexivity | left; apply H ].
    - simpl; reflexivity.
Qed.

Definition not_appear_free_sep_atom (t : SepAtomTerm) (x : Z) : Prop :=
    match t with
    | TSepDataAt addr ty val => not_appear_free_expr _ addr x /\ not_appear_free_expr _ val x
    end.

Definition not_appear_free_sep_atom_bool (t : SepAtomTerm) (x : Z) : bool :=
    match t with
    | TSepDataAt addr ty val =>
    (not_appear_free_expr_bool _ addr x && not_appear_free_expr_bool _ val x)%bool
    end.

Lemma not_appear_free_sep_atom_true :
    forall t x,
        not_appear_free_sep_atom_bool t x = true <-> not_appear_free_sep_atom t x.
    intros; destruct t; simpl.
    rewrite andb_true_iff.
    rewrite ! not_appear_free_expr_true.
    tauto.
Qed.

Lemma not_appear_free_sep_atom_false :
    forall t x,
        not_appear_free_sep_atom_bool t x = false <-> ~ not_appear_free_sep_atom t x.
    intros; destruct t; simpl.
    rewrite andb_false_iff.
    rewrite ! not_appear_free_expr_false.
    tauto.
Qed.

Lemma not_appear_free_sep_atom_equiv :
    forall t x,
        not_appear_free_sep_atom t x ->
    forall env ty v,
        sep_atom_term_denote t env --||-- sep_atom_term_denote t (term_mapping_update env x ty v).
    intros.
    destruct t.
    unfold not_appear_free_sep_atom in H.
    destruct H as [? ?].
    simpl.
    eapply not_appear_free_expr_equiv in H, H0.
    rewrite H0, H.
    apply logic_equiv_refl.
Qed.

Definition not_appear_free_sep_term_bool (t : SepTerm) (x : Z) : bool :=
    fold_right (fun a b => andb (not_appear_free_sep_atom_bool a x) b) true t.

Definition not_appear_free_sep_term (t : SepTerm) (x : Z) : Prop :=
    fold_right (fun a b => (not_appear_free_sep_atom a x) /\ b) True t.

Lemma not_appear_free_sep_term_true :
    forall t x,
        not_appear_free_sep_term_bool t x = true <-> not_appear_free_sep_term t x.
    induction t; intros.
    - simpl; tauto.
    - simpl.
      rewrite andb_true_iff.
      rewrite not_appear_free_sep_atom_true.
      rewrite IHt.
      tauto.
Qed.

Lemma not_appear_free_sep_term_false :
    forall t x,
        not_appear_free_sep_term_bool t x = false <-> ~ not_appear_free_sep_term t x.
    induction t; intros.
    - simpl; split; intros.
      + discriminate.
      + contradiction.
    - simpl.
      rewrite andb_false_iff.
      rewrite not_appear_free_sep_atom_false.
      rewrite IHt.
      tauto.
Qed.

Lemma not_appear_free_sep_term_equiv :
    forall t x,
        not_appear_free_sep_term t x ->
    forall env ty v,
        sep_term_denote t env --||-- sep_term_denote t (term_mapping_update env x ty v).
    induction t; intros.
    - simpl; apply logic_equiv_refl.
    - simpl in *.
      destruct H.
      eapply not_appear_free_sep_atom_equiv in H; destruct H.
      edestruct (IHt _ H0).
      split.
      + sep_apply H2.
        sep_apply H.
        entailer!.
      + sep_apply H3.
        sep_apply H1.
        entailer!.
Qed.

Definition var_list_not_appear_free_sep_term_bool (v : VarList) (t : SepTerm) : bool :=
    fold_right (fun a b => andb (not_appear_free_sep_term_bool t (fst a)) b) true v.

Definition var_list_not_appear_free_sep_term (v : VarList) (t : SepTerm) : Prop :=
    fold_right (fun a b => (not_appear_free_sep_term t (fst a)) /\ b) True v.

Lemma var_list_not_appear_free_sep_term_true :
    forall v t,
        var_list_not_appear_free_sep_term_bool v t = true <-> var_list_not_appear_free_sep_term v t.
    induction v; intros.
    - simpl; tauto.
    - simpl.
      rewrite andb_true_iff.
      rewrite not_appear_free_sep_term_true.
      rewrite IHv.
      tauto.
Qed.

Lemma var_list_not_appear_free_sep_term_false :
    forall v t,
        var_list_not_appear_free_sep_term_bool v t = false <-> ~ var_list_not_appear_free_sep_term v t.
    induction v; intros.
    - simpl; split; intros.
      + discriminate.
      + contradiction.
    - simpl.
      rewrite andb_false_iff.
      rewrite not_appear_free_sep_term_false.
      rewrite IHv.
      tauto.
Qed.

Lemma var_list_not_appear_free_sep_term_equiv :
    forall vl t,
        var_list_not_appear_free_sep_term vl t ->
    forall env,
        exists_term_denote (TExists vl t) env --||--
        sep_term_denote t env.
    induction vl.
    - intros; simpl in *; apply logic_equiv_refl.
    - intros.
      replace (TExists (a :: vl) t) with (ExistsCons a (TExists vl t)) by reflexivity.
      destruct a; rewrite exists_term_denote_cons.
      simpl in H; destruct H.
      split.
      + Intros v.
        destruct (IHvl _ H0 (term_mapping_update env z w v)).
        sep_apply H1.
        eapply not_appear_free_sep_term_equiv in H.
        destruct H.
        apply H3.
      + Exists (wtype_default w).
        eapply not_appear_free_sep_term_equiv in H.
        destruct H.
        sep_apply H.
        destruct (IHvl _ H0 (term_mapping_update env z w (wtype_default w))).
        apply H3.
Qed.



(* Fixpoint not_appear_free_sep (t : SepTerm) (x : Z) : Prop :=
    match t with
    | TSepCon t1 t2 => not_appear_free_sep t1 x /\ not_appear_free_sep t2 x
    | TSepLeaf t => not_appear_free_sep_atom t x
    | TSepEmp => True
    end.

Fixpoint not_appear_free_var_list (vl : VarList) (x : Z) : Prop :=
    match vl with
    | nil => True
    | (y, ty) :: vs => (x = y) \/ not_appear_free_var_list vs x
    end.

Definition not_appear_free_exists (t : ExistsTerm) (x : Z) : Prop :=
    match t with
    | TExists vl sep =>
        (not_appear_free_var_list vl x) \/ (not_appear_free_sep sep x)
    end. *)

(* Definition conv_var_list (conv : AlphaConversion) (vl : VarList) : VarList :=
    map (fun x => (conv (fst x), snd x)) vl.

Definition conv_expr (ty : Wtype) (conv : AlphaConversion) (e : Wexpr ty) : Wexpr ty :=
    match e with
    | EVar x ty => EVar (conv x) ty
    | EConstZ val => EConstZ val
    end.

Definition conv_sep_atom (conv : AlphaConversion) (t : SepAtomTerm) : SepAtomTerm :=
    match t with
    | TSepDataAt addr ty val =>
        TSepDataAt (conv_expr _ conv addr) ty (conv_expr _ conv val)
    end.

Fixpoint conv_sep (conv : AlphaConversion) (t : SepTerm) : SepTerm :=
    match t with
    | TSepCon t1 t2 => TSepCon (conv_sep conv t1) (conv_sep conv t2)
    | TSepLeaf t => TSepLeaf (conv_sep_atom conv t)
    | TSepEmp => TSepEmp
    end.

Definition conv_exists (conv : AlphaConversion) (t : ExistsTerm) : ExistsTerm :=
    match t with
    | TExists vl pre => TExists (conv_var_list conv vl) (conv_sep conv pre)
    end.

Lemma conv_exists_nil :
    forall (conv : AlphaConversion) (sep : SepTerm),
        conv_exists conv (TExists nil sep) = TExists nil (conv_sep conv sep).
    intros; simpl; reflexivity.
Qed.

Lemma conv_exists_cons :
    forall (conv : AlphaConversion) (x : Z) (ty : Wtype) (t : ExistsTerm),
        conv_exists conv (ExistsCons (x, ty) t) =
        ExistsCons (conv x, ty) (conv_exists conv t).
    intros; simpl.
    unfold conv_exists, ExistsCons.
    destruct t; simpl; reflexivity.
Qed.

Definition conv_forall (conv : AlphaConversion) (t : ForallTerm) :=
    match t with
    | TForall vl pre post => TForall (conv_var_list conv vl) (conv_exists conv pre) (conv_exists conv post)
    end.

Lemma conv_forall_nil :
    forall (conv : AlphaConversion) (pre : ExistsTerm) (post : ExistsTerm),
        conv_forall conv (TForall nil pre post) =
        TForall nil (conv_exists conv pre) (conv_exists conv post).
    intros; simpl; reflexivity.
Qed.

Lemma conv_forall_cons :
    forall (conv : AlphaConversion) (x : Z) (ty : Wtype) (t : ForallTerm),
        conv_forall conv (ForallCons (x, ty) t) =
        ForallCons (conv x, ty) (conv_forall conv t).
    intros; simpl.
    unfold conv_forall, ForallCons.
    destruct t; simpl; reflexivity.
Qed.

Definition equiv_by_conv (conv : AlphaConversion) (H : injective_conversion conv)
                         (env0 : TermMapping) (env1 : TermMapping) : Prop :=
    forall x ty, env0 x ty = env1 (conv x) ty.

Lemma equiv_by_conv_update :
    forall env0 env1 conv H x ty v,
        equiv_by_conv conv H env0 env1 ->
        equiv_by_conv conv H (term_mapping_update env0 x ty v)
                           (term_mapping_update env1 (conv x) ty v).
    unfold equiv_by_conv.
    intros.
    unfold term_mapping_update.
    destruct (Z.eq_dec x x0);
    destruct (wtype_eq_dec ty ty0);
    destruct (Z.eq_dec (conv x) (conv x0));
    try reflexivity;
    try apply H0.
    - rewrite e in n; contradiction.
    - unfold injective_conversion in H.
      apply H in e0; contradiction.
Qed.

Lemma conv_equivalence_expr :
    forall (ty : Wtype) (e : Wexpr ty) (conv : AlphaConversion) (H : injective_conversion conv)
           (env0 : TermMapping) (env1 : TermMapping),
           equiv_by_conv conv H env0 env1 ->
           wexpr_denote ty e env0 = wexpr_denote ty (conv_expr ty conv e) env1.
    intros.
    destruct e.
    - simpl.
      unfold equiv_by_conv in H0.
      apply H0.
    - simpl.
      reflexivity.
Qed.

Lemma conv_equivalence_sep_atom :
    forall (t : SepAtomTerm) (conv : AlphaConversion) (H : injective_conversion conv)
           (env0 : TermMapping) (env1 : TermMapping),
           equiv_by_conv conv H env0 env1 ->
           sep_atom_term_denote t env0 --||-- sep_atom_term_denote (conv_sep_atom conv t) env1.
    intros.
    destruct t.
    simpl.
    rewrite conv_equivalence_expr with (H := H) (conv := conv) (env1 := env1) by assumption.
    rewrite conv_equivalence_expr with (e := val) (H := H) (conv := conv) (env1 := env1) by assumption.
    split; apply derivable1_refl.
Qed.

Lemma conv_equivalence_sep :
    forall (t : SepTerm) (conv : AlphaConversion) (H : injective_conversion conv)
           (env0 : TermMapping) (env1 : TermMapping),
           equiv_by_conv conv H env0 env1 ->
           sep_term_denote t env0 --||-- sep_term_denote (conv_sep conv t) env1.

    intro t; induction t; intros.
    - specialize (IHt1 _ _ _ _ H0); destruct IHt1.
      specialize (IHt2 _ _ _ _ H0); destruct IHt2.
      simpl; split; intros.
      + sep_apply H1; sep_apply H3.
        apply derivable1_refl.
      + sep_apply H2; sep_apply H4.
        apply derivable1_refl.
    - simpl.
      eapply conv_equivalence_sep_atom.
      apply H0.
    - simpl.
      split; apply derivable1_refl.
Qed.<

Lemma conv_equivalence_exists :
    forall (t : ExistsTerm) (conv : AlphaConversion) (H : injective_conversion conv)
           (env0 : TermMapping) (env1 : TermMapping),
            equiv_by_conv conv H env0 env1 ->
            exists_term_denote t env0 --||-- exists_term_denote (conv_exists conv t) env1.
    intro t; apply (ind_exists t); intros; [
        rewrite conv_exists_nil, ! exists_term_denote_nil |
        destruct x; rewrite conv_exists_cons, ! exists_term_denote_cons
    ].
    - eapply conv_equivalence_sep.
      apply H0.
    - split; Intros v; Exists v;
      apply (equiv_by_conv_update _ _ _ _ z w v) in H1;
      apply H in H1; destruct H1; assumption.
Qed.

Lemma conv_equivalence_forall :
    forall (t : ForallTerm) (conv : AlphaConversion) (H : injective_conversion conv)
           (env0 : TermMapping) (env1 : TermMapping),
           equiv_by_conv conv H env0 env1 ->
           forall_term_denote t env0 <-> forall_term_denote (conv_forall conv t) env1.
    intro t; apply (ind_forall t); intros; [
        rewrite conv_forall_nil, ! forall_term_denote_nil |
        destruct x; rewrite conv_forall_cons, ! forall_term_denote_cons
    ].
    - pose proof (conv_equivalence_exists pre conv H env0 env1 H0).
      destruct H1.
      pose proof (conv_equivalence_exists post conv H env0 env1 H0).
      destruct H3.
      split; intros.
      + sep_apply H2.
        eapply derivable1_trans.
        apply H5.
        apply H3.
      + sep_apply H1.
        eapply derivable1_trans.
        apply H5.
        apply H4.
    - split; intros; specialize (H2 v);
      apply (equiv_by_conv_update _ _ _ _ z w v) in H1;
      apply H in H1; apply H1; assumption.
Qed. *)

Definition rc_denote (r : RamificationCondition) : Prop :=
    match r with
    | RC P P' Q' Q =>
        var_list_forall_denote (get_var_list_rc r) empty_mapping
            (fun env => sep_term_denote P env |--
                        sep_term_denote P' env ** (
                        sep_term_denote Q' env -*
                        sep_term_denote Q env))
    end.

Definition ProvableRC (r : RamificationCondition) : Prop := rc_denote r.

Fixpoint sep_atom_term_inb (t : SepAtomTerm) (l : SepTerm) : bool :=
    match l with
    | nil => false
    | cons x xs => (sep_atom_term_eqb t x || sep_atom_term_inb t xs)%bool
    end.

Lemma sep_atom_term_inb_in :
    forall t l,
    sep_atom_term_inb t l = true <-> In t l.
    intros; split; generalize dependent t.
    - induction l; intros.
      + simpl in H; discriminate.
      + simpl in H.
        apply orb_true_iff in H.
        destruct H.
        * apply sep_atom_term_eqb_eq in H; subst; left; reflexivity.
        * right; apply IHl; assumption.
    - induction l; intros.
      + destruct H.
      + simpl.
        destruct H; apply orb_true_iff.
        * left; apply sep_atom_term_eqb_eq; symmetry; assumption.
        * right; apply IHl; assumption.
Qed.

Lemma sep_atom_term_inb_in_false :
    forall t l,
        sep_atom_term_inb t l = false -> ~ In t l.
    intros; unfold not; intro H1.
    pose proof sep_atom_term_inb_in; edestruct H0.
    apply H3 in H1.
    rewrite H1 in H; discriminate.
Qed.

Fixpoint sep_atom_term_remove (t : SepAtomTerm) (l : SepTerm) : SepTerm :=
    match l with
    | nil => nil
    | cons x xs => if (sep_atom_term_eqb x t) then xs else cons x (sep_atom_term_remove t xs)
    end.

Lemma sep_atom_term_remove_eq :
    forall a l, sep_atom_term_remove a (a :: l) = l.
    intros; simpl.
    pose proof (sep_atom_term_eqb_eq a a).
    destruct H.
    rewrite (H0 eq_refl).
    reflexivity.
Qed.

Lemma sep_atom_term_remove_neq :
    forall a b l, a <> b -> sep_atom_term_remove a (b :: l) = b :: sep_atom_term_remove a l.
    intros; simpl;
    destruct (sep_atom_term_eqb b a) eqn : Heqb; [
        apply sep_atom_term_eqb_eq in Heqb |
        apply sep_atom_term_eqb_eq_false in Heqb
    ].
    - symmetry in Heqb; contradiction.
    - reflexivity.
Qed.

Lemma sep_atom_term_remove_split :
    forall a l1 l2,
        In a l1 ->
        sep_atom_term_remove a l1 = l2 ->
        exists l2a l2b, l2 = l2a ++ l2b /\ l1 = l2a ++ a :: l2b.
    induction l1.
    - intros.
      simpl in *; exfalso; apply H.
    - intros.
      simpl in H.
      destruct (sep_atom_term_eq_dec a a0).
      * subst a0; rewrite sep_atom_term_remove_eq in H0.
        exists nil, l1; rewrite H0; simpl; split; reflexivity.
      * destruct H; [ symmetry in H; contradiction | ].
        rewrite sep_atom_term_remove_neq in H0 by assumption.
        destruct l2; [ discriminate H0 | ].
        injection H0 as ?; subst s.
        specialize (IHl1 _ H H1).
        destruct IHl1 as [l2a [l2b ?]].
        exists (a0 :: l2a), l2b.
        destruct H0; subst.
        simpl; split; reflexivity.
Qed.  

(* Inductive Shuffle (t1 t2 : SepTerm) : Prop :=
| SNil : t1 = nil -> t2 = nil -> Shuffle t1 t2
| SCons : forall a, In a t1 -> In a t2 ->
                    Shuffle (sep_atom_term_remove a t1) (sep_atom_term_remove a t2) ->
                    Shuffle t1 t2
.

Lemma shuffle_cons :
    forall a l1 l2, Shuffle l1 l2 -> Shuffle (a :: l1) (a :: l2).
    intros; apply (SCons _ _ a).
    + simpl; left; reflexivity.
    + simpl; left; reflexivity.
    + rewrite ! sep_atom_term_remove_eq.
      apply H.
Qed.

Lemma shuffle_refl :
    forall l, Shuffle l l.
    induction l.
    - apply SNil; reflexivity.
    - apply shuffle_cons; apply IHl.
Qed.  *)

(* Lemma sep_atom_term_remove_in_equiv :
    forall a t env,
        In a t ->
        sep_term_denote t env --||-- sep_atom_term_denote a env ** sep_term_denote (sep_atom_term_remove a t) env.
    induction t; intros.
    - unfold In in H; exfalso; apply H.
    - simpl in H; destruct H.
      + subst; simpl; rewrite sep_atom_term_eqb_refl.
        split; entailer!.
      + simpl; destruct (sep_atom_term_eqb a0 a) eqn : ?.
        * apply sep_atom_term_eqb_eq in Heqb; subst a0.
          split; entailer!.
        * specialize (IHt env H).
          simpl.
          destruct IHt as [? ?].
          split; [
            sep_apply H0; entailer! |
            sep_apply derivable1_sepcon_assoc1; sep_apply H1; entailer!
          ].
Qed. *)

(* Lemma shuffle_equiv :
    forall t1 t2 env,
        Shuffle t1 t2 ->
        sep_term_denote t1 env --||-- sep_term_denote t2 env.
    intros.
    generalize dependent env.
    induction H.
    - subst; intros; apply logic_equiv_refl.
    - intros; specialize (IHShuffle env).
      destruct IHShuffle as [? ?].
      pose proof (sep_atom_term_remove_in_equiv a t1 env H).
      pose proof (sep_atom_term_remove_in_equiv a t2 env H0).
      destruct H4, H5.
      split; [
        sep_apply H4;
        sep_apply H2;
        sep_apply H7;
        entailer! |
        sep_apply H5;
        sep_apply H3;
        sep_apply H6;
        entailer!
      ].
Qed. *)

Lemma permutation_equiv :
    forall t1 t2 env,
        Permutation t1 t2 ->
        sep_term_denote t1 env --||-- sep_term_denote t2 env.
    intros; generalize dependent env.
    induction H; intros.
    - apply logic_equiv_refl.
    - simpl; split; destruct (IHPermutation env).
      + sep_apply H0; apply derivable1_refl.
      + sep_apply H1; apply derivable1_refl.
    - simpl; split; entailer!.
    - apply (logic_equiv_trans _ _ _ (IHPermutation1 env) (IHPermutation2 env)).
Qed.

Lemma erase_sep_permutation :
    forall P H Q,
        erase_sep P H = Some Q ->
        Permutation P (cons H Q).
    induction P; intros.
    - simpl in H0; discriminate.
    - simpl in *.
      destruct (sep_atom_term_eqb a H) eqn : ?.
      + apply sep_atom_term_eqb_eq in Heqb; subst a.
        injection H0 as ?; subst; apply Permutation_refl.
      + destruct (erase_sep P H) eqn : ?; [ | discriminate H0 ].
        apply IHP in Heqo.
        injection H0 as ?; subst.
        rewrite perm_swap.
        apply Permutation_cons; [ apply eq_refl | apply Heqo ].
Qed.

Lemma in_erase_sep :
    forall P H,
        In H P ->
        exists Q, erase_sep P H = Some Q.
    induction P; intros.
    - simpl in *; exfalso; apply H0.
    - simpl in *; destruct (sep_atom_term_eqb a H) eqn : ?.
      + apply sep_atom_term_eqb_eq in Heqb; subst a.
        exists P; reflexivity.
      + apply sep_atom_term_eqb_eq_false in Heqb.
        destruct H0; [ contradiction | ].
        destruct (IHP _ H0) as [Q ?].
        rewrite H1.
        exists (a :: Q); reflexivity.
Qed.

Definition update_rc (op : Operation) (r : RamificationCondition) : RamificationCondition :=
    match r with
    | RC P P' Q' Q =>
        match op with
        | OLeftErase H => if sep_atom_term_inb H P'
                          then RC P (sep_atom_term_remove H P') Q' Q
                          else RC (cons H P) P' Q' Q
        | OLeftAdd H => RC P (cons H P') Q' Q
        | ORightAdd H => RC P P' (cons H Q') Q
        | ORightErase H => if sep_atom_term_inb H Q'
                           then RC P P' (sep_atom_term_remove H Q') Q
                           else RC P P' Q' (cons H Q)
        end
    end.

Definition gen_rc (ops : list Operation) : RamificationCondition :=
    fold_right update_rc (RC nil nil nil nil) ops.

Lemma gen_rc_cons :
    forall op ops,
    gen_rc (op :: ops) = update_rc op (gen_rc ops).
    intros; simpl; reflexivity.
Qed.

(* Lemma test : forall (t : ForallTerm) x pre post env,
    t = TForall x pre post ->
    forall_term_denote t env -> (exists_term_denote pre env |-- exists_term_denote post env).
    intros.
    generalize dependent t.
    generalize dependent env.
    induction x.
    - unfold forall_term_denote; intros.
      rewrite H in H0; simpl in H0; assumption.
    - intros.
      destruct a.
      rewrite H in H0.
      rewrite test_helper in H0.
      specialize (H0 (env z w)).
      rewrite term_mapping_update_lookup in H0.
      apply (IHx _ (TForall x pre post)).
      reflexivity.
      assumption.
Qed. *)

Definition get_sep_exists (t : ExistsTerm) : SepTerm :=
    match t with
    | TExists vl sep => sep
    end.

Definition get_pre_sep_forall (t : ForallTerm) : SepTerm :=
    match t with
    | TForall vl pre post => get_sep_exists pre
    end.

Definition get_post_sep_forall (t : ForallTerm) : SepTerm :=
    match t with
    | TForall vl pre post => get_sep_exists post
    end.

Lemma soundness_helper0 : forall ops A B C D T1 T2,
    apply_operations T1 ops = Some T2 ->
    gen_rc ops = RC A B C D ->
    exists CP CQ,
    Permutation (get_pre_sep_forall T1) (A ++ CP) /\
    Permutation (get_pre_sep_forall T2) (B ++ CP) /\
    Permutation (get_post_sep_forall T2) (C ++ CQ) /\
    Permutation (get_post_sep_forall T1) (D ++ CQ).
    induction ops.
    - intros.
      simpl in H; injection H as ?.
      simpl in H0; injection H0 as ?; subst.
      destruct T2 as [a [p P] [q Q]].
      exists P, Q.
      simpl; repeat split; apply Permutation_refl.
    - intros.
      rewrite gen_rc_cons in H0;
      rewrite apply_operations_cons in H;
      remember (apply_operations T1 ops) as T1';
      remember (gen_rc ops) as r';
      destruct T1' as [ T1' | ], r'; [ | simpl in H; discriminate ].
      destruct a; simpl in *.
      + destruct B; injection H0 as ?; [ discriminate | ]; subst.
        symmetry in HeqT1'.
        specialize (IHops A B C D _ _ HeqT1' eq_refl).
        destruct IHops as [CP [CQ [? [? [? ?]]]]].
        destruct T1' as [a1 [p1 P1] [q1 Q1]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists CP, CQ.
        split; [ | split; [ | split ]]; try assumption.
        unfold add_sep.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (sep_atom_term_inb H1 P') eqn : Heqb; [
          rewrite sep_atom_term_inb_in in Heqb |
          apply sep_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (sep_atom_term_remove_split _ _ _ Heqb H2).
          destruct H5 as [B_ls [B_rs ?]]; destruct H5.
          subst P Q' Q P' B.
          specialize (IHops A (B_ls ++ H1 :: B_rs) C D _ _ HeqT1' eq_refl).
          destruct IHops as [CP [CQ [? [? [? ?]]]]].
          destruct T1' as [a1 [p1 P1] [q1 Q1]];
          destruct T2 as [a2 [p2 P2] [q2 Q2]];
          simpl in *.
          destruct (erase_sep P1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H5.
          exists CP, CQ.
          repeat split; try assumption.
          apply erase_sep_permutation in Heqo.
          rewrite Heqo in H2.
          rewrite (Permutation_app_comm B_ls _) in H2.
          simpl in H2.
          apply Permutation_cons_inv in H2.
          rewrite (Permutation_app_comm B_rs _) in H2.
          apply H2.
        * destruct A; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops A B C D _ _ HeqT1' eq_refl).
          destruct IHops as [CP [CQ [? [? [? ?]]]]].
          destruct T1' as [a1 [p1 P1] [q1 Q1]];
          destruct T2 as [a2 [p2 P2] [q2 Q2]];
          simpl in *.
          destruct (erase_sep P1 s) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_sep_permutation in Heqo.
          assert (In s CP). {
            assert (In s (s :: P2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H1 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_sep _ _ H) as [CP' ?].
          apply erase_sep_permutation in H4.
          exists CP', CQ; repeat split; try assumption.
          -- rewrite H4 in H0.
             rewrite <- Permutation_middle in H0.
             apply H0.
          -- rewrite H4 in H1.
             rewrite Heqo in H1.
             rewrite <- Permutation_middle in H1.
             apply Permutation_cons_inv in H1.
             apply H1.
      + destruct C; injection H0 as ?; [ discriminate | ]; subst.
        symmetry in HeqT1'.
        specialize (IHops A B C D _ _ HeqT1' eq_refl).
        destruct IHops as [CP [CQ [? [? [? ?]]]]].
        destruct T1' as [a1 [p1 P1] [q1 Q1]]; simpl in *.
        injection H as ?; subst; simpl in *.
        exists CP, CQ.
        split; [ | split; [ | split ]]; try assumption.
        unfold add_sep.
        apply Permutation_cons; [ apply eq_refl | assumption ].
      + destruct (sep_atom_term_inb H1 Q') eqn : Heqb; [
          rewrite sep_atom_term_inb_in in Heqb |
          apply sep_atom_term_inb_in_false in Heqb
        ].
        * symmetry in HeqT1'.
          injection H0 as ?.
          pose proof (sep_atom_term_remove_split _ _ _ Heqb H3).
          destruct H5 as [C_ls [C_rs ?]]; destruct H5.
          subst P Q' Q P' C.
          specialize (IHops A B (C_ls ++ H1 :: C_rs) D _ _ HeqT1' eq_refl).
          destruct IHops as [CP [CQ [? [? [? ?]]]]].
          destruct T1' as [a1 [p1 P1] [q1 Q1]];
          destruct T2 as [a2 [p2 P2] [q2 Q2]];
          simpl in *.
          destruct (erase_sep Q1 H1) eqn : ? ; [ | discriminate H ].
          injection H as ?; subst; rewrite H5.
          exists CP, CQ.
          repeat split; try assumption.
          apply erase_sep_permutation in Heqo.
          rewrite Heqo in H3.
          rewrite (Permutation_app_comm C_ls _) in H3.
          simpl in H3.
          apply Permutation_cons_inv in H3.
          rewrite (Permutation_app_comm C_rs _) in H3.
          apply H3.
        * destruct D; injection H0 as ?; [ discriminate | ]; subst.
          symmetry in HeqT1'.
          specialize (IHops A B C D _ _ HeqT1' eq_refl).
          destruct IHops as [CP [CQ [? [? [? ?]]]]].
          destruct T1' as [a1 [p1 P1] [q1 Q1]];
          destruct T2 as [a2 [p2 P2] [q2 Q2]];
          simpl in *.
          destruct (erase_sep Q1 s) eqn : ?; [ | discriminate H ].
          injection H as ?; subst.
          apply erase_sep_permutation in Heqo.
          assert (In s CQ). {
            assert (In s (s :: Q2)) by (simpl; left; reflexivity).
            rewrite <- Heqo in H.
            rewrite -> H2 in H.
            apply in_app_iff in H.
            destruct H; [ contradiction | assumption ].
          }
          destruct (in_erase_sep _ _ H) as [CQ' ?].
          apply erase_sep_permutation in H4.
          exists CP, CQ'; repeat split; try assumption.
          -- rewrite H4 in H2.
             rewrite Heqo in H2.
             rewrite <- Permutation_middle in H2.
             apply Permutation_cons_inv in H2.
             apply H2.
          -- rewrite H4 in H3.
             rewrite <- Permutation_middle in H3.
             apply H3.
Qed.

Lemma sep_term_denote_app : forall a b env,
    sep_term_denote (a ++ b) env --||-- sep_term_denote a env ** sep_term_denote b env.
    induction a; intros; simpl.
    - split; entailer!.
    - destruct (IHa b env).
      split.
      + sep_apply H; entailer!.
      + pose proof logic_equiv_sepcon_assoc.
        edestruct H1.
        sep_apply H3.
        sep_apply sepcon_swap_logic_equiv.
        sep_apply H0.
        entailer!.
Qed.

Lemma soundness_helper1 : forall ops A B C D T1 T2,
    apply_operations T1 ops = Some T2 ->
    gen_rc ops = RC A B C D ->
    exists CP CQ,
    (forall env, sep_term_denote (get_pre_sep_forall T1) env --||-- (sep_term_denote (A ++ CP) env)) /\
    (forall env, sep_term_denote (get_pre_sep_forall T2) env --||-- (sep_term_denote (B ++ CP) env)) /\
    (forall env, sep_term_denote (get_post_sep_forall T2) env --||-- (sep_term_denote (C ++ CQ) env)) /\
    (forall env, sep_term_denote (get_post_sep_forall T1) env --||-- (sep_term_denote (D ++ CQ) env)).
    intros.
    pose proof soundness_helper0 as H1.
    destruct (H1 _ _ _ _ _ _ _ H H0) as [CP [CQ [? [? [? ?]]]]].
    exists CP, CQ; split; [ | split; [ | split ]]; intros;
    apply (permutation_equiv _ _ env) in H2, H3, H4, H5; assumption.
Qed.

Definition get_var_list_forall (T : ForallTerm) :=
    match T with
    | TForall a _ _ => a
    end.

Definition get_pre_var_list (T : ForallTerm) :=
    match T with
    | TForall _ (TExists a _) _ => a
    end.

Definition get_post_var_list (T : ForallTerm) :=
    match T with
    | TForall _ _ (TExists a _) => a
    end.

Lemma apply_operation_keep_var_list :
    forall op T1 T2,
        apply_operation op (Some T1) = Some T2 ->
        get_var_list_forall T1 = get_var_list_forall T2 /\
        get_pre_var_list T1 = get_pre_var_list T2 /\
        get_post_var_list T1 = get_post_var_list T2.
    intros; destruct op;
    destruct T1 as [a1 [p1 P1] [q1 Q1]];
    destruct T2 as [a2 [p2 P2] [q2 Q2]];
    simpl in *.
    all: try solve [injection H as ?; subst; repeat split; reflexivity].
    destruct (erase_sep P1 H0); try discriminate; try injection H as ?; subst; repeat split; reflexivity.
    destruct (erase_sep Q1 H0); try discriminate; try injection H as ?; subst; repeat split; reflexivity.
Qed.

Lemma apply_operations_keep_var_list :
    forall ops T1 T2,
        apply_operations T1 ops = Some T2 ->
        get_var_list_forall T1 = get_var_list_forall T2 /\
        get_pre_var_list T1 = get_pre_var_list T2 /\
        get_post_var_list T1 = get_post_var_list T2.
    induction ops.
    - intros; simpl in H.
      injection H as ?; subst; repeat split; reflexivity.
    - intros.
      rewrite apply_operations_cons in H.
      destruct (apply_operations T1 ops) eqn : ?; [ | discriminate H ].
      pose proof apply_operation_keep_var_list.
      specialize (IHops _ _ Heqo).
      specialize (H0 _ _ _ H).
      destruct IHops as [A [B C]];
      destruct H0 as [D [E F]];
      rewrite A, B, C, D, E, F;
      repeat split;
      reflexivity.
Qed.

Lemma apply_operations_var_list_cons :
    forall ops x T1 T2,
        apply_operations (ForallCons x T1) ops = Some T2 ->
        exists T2', T2 = ForallCons x T2' /\ apply_operations T1 ops = Some T2'.
    induction ops.
    - intros; simpl in H.
      injection H as ?; subst.
      exists T1; split; reflexivity.
    - intros.
      rewrite apply_operations_cons in *.
      destruct (apply_operations (ForallCons x T1) ops) eqn : ?; [ | discriminate H ].
      destruct (IHops _ _ _ Heqo) as [T2' [? ?]].
      pose proof apply_operation_keep_var_list.
      specialize (H2 _ _ _ H).
Admitted.

Lemma var_list_forall_denote_entail :
    forall vl env cont,
        var_list_forall_denote vl env cont -> cont env.
    induction vl.
    - intros; simpl in H. apply H.
    - intros.
      simpl in H.
      destruct a.
      specialize (IHvl _ _ (H (env z w))).
      rewrite term_mapping_update_lookup in IHvl.
      apply IHvl.
Qed.

Lemma exists_term_denote_sep :
    forall p P Q,
        (forall env, sep_term_denote P env --||-- sep_term_denote Q env) ->
        (forall env, exists_term_denote (TExists p P) env --||-- exists_term_denote (TExists p Q) env).
    induction p.
    - intros; simpl; apply (H env).
    - intros.
      replace (TExists (a :: p) P) with (ExistsCons a (TExists p P)) by reflexivity.
      replace (TExists (a :: p) Q) with (ExistsCons a (TExists p Q)) by reflexivity.
      destruct a; rewrite ! exists_term_denote_cons.
      split; Intros v; Exists v; apply (IHp P Q H _).
Qed.

Lemma exists_term_denote_app :
    forall p P Q env,
        exists_term_denote (TExists p (P ++ Q)) env |-- exists_term_denote (TExists p P) env ** exists_term_denote (TExists p Q) env.
    induction p; intros.
    - intros; simpl; apply sep_term_denote_app.
    - assert (forall P, TExists (a :: p) P = ExistsCons a (TExists p P)) by reflexivity.
      rewrite ! H; destruct a; rewrite ! exists_term_denote_cons.
      Intros v.
      Exists v v.
      sep_apply IHp.
      entailer!.
Qed.

Lemma soundness_helper2 :
    forall p A B C D,
    var_list_not_appear_free_sep_term p C ->
    var_list_not_appear_free_sep_term p D ->
    (forall env, sep_term_denote A env |-- sep_term_denote B env ** (sep_term_denote C env -* sep_term_denote D env)) ->
    (forall env, exists_term_denote (TExists p A) env |-- exists_term_denote (TExists p B) env ** (sep_term_denote C env -* sep_term_denote D env)).
    induction p; intros.
    - simpl; intros; apply H1.
    - assert (forall P, TExists (a :: p) P = ExistsCons a (TExists p P)) by reflexivity.
      rewrite ! H2; destruct a; rewrite ! exists_term_denote_cons.
      Intros v.
      Exists v.
      simpl in H, H0.
      destruct H, H0.
      specialize (IHp _ _ _ _ H3 H4 H1).
      sep_apply IHp.
      eapply not_appear_free_sep_term_equiv in H.
      eapply not_appear_free_sep_term_equiv in H0.
      assert (forall AA BB CC DD, AA --||-- BB -> CC --||-- DD -> (AA -* CC) --||-- (BB -* DD)). {
        clear; intros.
        unfold logic_equiv, wand, derivable1 in *.
        split; intros.
        - destruct H.
          apply H4 in H3.
          apply (H1  _ _ H2) in H3.
          destruct H0.
          apply H0 in H3.
          assumption.
        - destruct H.
          apply H in H3.
          apply (H1 _ _ H2) in H3.
          destruct H0.
          apply H5 in H3.
          assumption.
      }
      specialize (H5 _ _ _ _ H H0).
      destruct H5.
      sep_apply H6.
      entailer!.
Qed.

Lemma soundness_helper3 :
    forall p A B C D,
    var_list_not_appear_free_sep_term p C ->
    var_list_not_appear_free_sep_term p D ->
    (forall env, sep_term_denote A env ** (sep_term_denote C env -* sep_term_denote D env) |-- sep_term_denote B env) ->
    (forall env, exists_term_denote (TExists p A) env ** (sep_term_denote C env -* sep_term_denote D env)|-- exists_term_denote (TExists p B) env).
    induction p; intros.
    - simpl; intros; apply H1.
    - assert (forall P, TExists (a :: p) P = ExistsCons a (TExists p P)) by reflexivity.
      rewrite ! H2; destruct a; rewrite ! exists_term_denote_cons.
      Intros v.
      Exists v.
      simpl in H, H0.
      destruct H, H0.
      specialize (IHp _ _ _ _ H3 H4 H1).
      eapply not_appear_free_sep_term_equiv in H.
      eapply not_appear_free_sep_term_equiv in H0.
      assert (forall AA BB CC DD, AA --||-- BB -> CC --||-- DD -> (AA -* CC) --||-- (BB -* DD)). {
        clear; intros.
        unfold logic_equiv, wand, derivable1 in *.
        split; intros.
        - destruct H.
          apply H4 in H3.
          apply (H1  _ _ H2) in H3.
          destruct H0.
          apply H0 in H3.
          assumption.
        - destruct H.
          apply H in H3.
          apply (H1 _ _ H2) in H3.
          destruct H0.
          apply H5 in H3.
          assumption.
      }
      specialize (H5 _ _ _ _ H H0).
      destruct H5.
      sep_apply H5.
      sep_apply IHp.
      entailer!.
Qed.

Definition get_pre_exists_var_list (t : ForallTerm) :=
    match t with
    | TForall _ (TExists vl _) _ => vl
    end.

Lemma get_pre_exists_var_list_cons :
    forall a t,
        get_pre_exists_var_list (ForallCons a t) = get_pre_exists_var_list t.
    intros; destruct t as [? [? ?] [? ?]]; reflexivity.
Qed.

Lemma rc_denote_all_env :
    forall A B C D,
        rc_denote (RC A B C D) ->
    forall env, sep_term_denote A env |--
                sep_term_denote B env **
                (sep_term_denote C env -* sep_term_denote D env).
Admitted.

Lemma soundness : forall ops A B C D T1 T2 env,
    apply_operations T1 ops = Some T2 ->
    var_list_not_appear_free_sep_term (get_pre_exists_var_list T1) C ->
    var_list_not_appear_free_sep_term (get_pre_exists_var_list T1) D ->
    gen_rc ops = RC A B C D ->
    ProvableRC (RC A B C D) ->
    Provable T2 env ->
    Provable T1 env.
    unfold Provable, ProvableRC in *.
    intros ops A B C D T1.
    apply (ind_forall T1).
    - intros.
      pose proof soundness_helper1.
      destruct (H5 _ _ _ _ _ _ _ H H2) as [CP [CQ [? [? [? ?]]]]]; clear H5.
      destruct pre as [p P];
      destruct post as [q Q];
      destruct T2 as [a [p' P'] [q' Q']].
      apply apply_operations_keep_var_list in H; simpl in H;
      destruct H as [? [? ?]]; subst a p' q'.
      rewrite forall_term_denote_nil in *.
      simpl in H6, H7, H8, H9.
      pose proof rc_denote_all_env.
      specialize (H _ _ _ _ H3).
      assert (forall env, sep_term_denote (A ++ CP) env |--
                          sep_term_denote (B ++ CP) env ** (sep_term_denote C env -* sep_term_denote D env)). {
        intros env0.
        sep_apply sep_term_denote_app.
        sep_apply sep_term_denote_app.
        sep_apply H.
        entailer!.
      }
      pose proof soundness_helper2.
      simpl in H0, H1.
      specialize (H10 _ _ _ _ _ H0 H1 H5).
      eapply exists_term_denote_sep in H6.
      sep_apply H6.
      sep_apply H10.
      eapply exists_term_denote_sep in H7.
      rewrite <- H7.
      sep_apply H4.
      eapply exists_term_denote_sep in H8.
      sep_apply H8.
      assert (forall env, sep_term_denote C env ** (sep_term_denote C env -* sep_term_denote D env) |-- sep_term_denote D env). {
        intros; apply wand_elim.
      }
      assert (forall env, sep_term_denote (C ++ CQ) env ** (sep_term_denote C env -* sep_term_denote D env) |-- sep_term_denote (D ++ CQ) env). {
        intros.
        rewrite sep_term_denote_app.
        rewrite sep_term_denote_app.
        rewrite <- logic_equiv_sepcon_assoc.
        rewrite sepcon_swap_logic_equiv.
        sep_apply H11.
        entailer!.
      }
      sep_apply exists_term_denote_app.
      rewrite <- logic_equiv_sepcon_assoc.
      rewrite sepcon_swap_logic_equiv.
      admit.
    - intros.
      apply apply_operations_var_list_cons in H0; destruct H0 as [T2' [? ?]].
      rewrite H0 in H5; destruct x; rewrite forall_term_denote_cons in *.
      rewrite get_pre_exists_var_list_cons in *.
      intros v; apply (H _ _ H6 H1 H2 H3 H4 (H5 v)).
Admitted.