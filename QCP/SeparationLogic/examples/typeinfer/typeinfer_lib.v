Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Definition TypeVarID: Type := Z.

Inductive TypeTree: Type :=
| TVar (n: TypeVarID)
| TAtom (n: Z)
| TApply (tfn rand: TypeTree)
| TArrow (from to: TypeTree).

Definition sol: Type :=
  TypeVarID -> option TypeTree.

Fixpoint type_subst (t: TypeTree) (s: sol): TypeTree :=
  match t with
  | TVar n =>
      match s n with
      | Some t0 => t0
      | None => TVar n
      end
  | TAtom n => TAtom n
  | TApply t1 t2 => TApply (type_subst t1 s) (type_subst t2 s)
  | TArrow t1 t2 => TArrow (type_subst t1 s) (type_subst t2 s)
  end.

Fixpoint type_subst_var (t: TypeTree) (n: TypeVarID) (tn: TypeTree): TypeTree :=
  match t with
  | TVar n0 => if Z.eq_dec n n0 then tn else t
  | TAtom _ => t
  | TApply t1 t2 => TApply (type_subst_var t1 n tn) (type_subst_var t2 n tn)
  | TArrow t1 t2 => TArrow (type_subst_var t1 n tn) (type_subst_var t2 n tn)
  end.

(* let s[n] = t *)
Definition sol_update (s: sol) (n: TypeVarID) (t: TypeTree): sol :=
  fun n' => if Z.eq_dec n n' then Some t else s n'.

Definition sol_c_update (s: sol) (n: TypeVarID) (t: TypeTree): sol :=
  fun n' => if Z.eq_dec n n' then Some t else
    match (s n') with
    | Some(tn') => Some(type_subst_var tn' n t)
    | None => None
    end.

Fixpoint occur (n: TypeVarID) (t: TypeTree): Prop :=
  match t with
  | TVar n0 => n = n0
  | TAtom _ => False
  | TApply t1 t2 => occur n t1 \/ occur n t2
  | TArrow t1 t2 => occur n t1 \/ occur n t2
  end.

Definition sol_compressed (s: sol): Prop :=
  forall n m: TypeVarID,
    match s n, s m with
    | Some t, Some _ => ~ occur m t
    | _, _ => True
    end.

Definition sol_compress_to (s sc: sol): Prop :=
  sol_compressed sc /\
  forall n: TypeVarID,
    match s n with
    | Some t => sc n = Some (type_subst t sc)
    | None => sc n = None
    end.

Definition sol_no_loop (s: sol): Prop :=
  exists rank: TypeVarID -> Z, 
    forall n m: TypeVarID,
      match s n, s m with
      | Some t, Some _ => occur m t -> rank m < rank n
      | _, _ => True
      end.

(* notice that sol_valid_eq(s) do not mean there is no variable in TypeTree *)
Definition sol_valid_eq (t1 t2: TypeTree) (s: sol): Prop :=
  type_subst t1 s = type_subst t2 s.

Definition sol_valid_eqs (eqns: list (TypeTree * TypeTree)) (s: sol): Prop :=
  forall t1 t2,
    In (t1, t2) eqns -> sol_valid_eq t1 t2 s.

(* s1 s2 should be compressed *)
Definition sol_refine (general specific: sol): Prop :=
  forall n: TypeVarID,
    match general n with
    | Some t => specific n = Some (type_subst t specific)
    | None => True
    end.

Definition sol_correct_eqs eqns (s: sol): Prop :=
  forall s': sol,
    sol_compressed s' ->
    (sol_valid_eqs eqns s' <-> sol_refine s s').

Definition sol_correct_iter (t1 t2: TypeTree) (s_pre s_post: sol): Prop :=
  forall s': sol,
    sol_compressed s' ->
    (sol_valid_eq t1 t2 s' /\ sol_refine s_pre s' <->
     sol_refine s_post s').

Definition sol_finite (s: sol): Prop :=
  exists ids: list TypeVarID,
    forall n: TypeVarID,
      In n ids <-> s n <> None.

Definition not_var (t: TypeTree): Prop :=
  match t with
  | TVar _ => False
  | _ => True
  end.

Inductive repr_rel_id (s: sol): TypeVarID -> TypeTree -> Prop :=
| repr_rel_var:
    forall n, s n = None -> repr_rel_id s n (TVar n)
| repr_rel_not_var:
    forall n t, s n = Some t -> not_var t -> repr_rel_id s n t
| repr_rel_rec:
    forall n m t,
      s n = Some (TVar m) -> repr_rel_id s m t -> repr_rel_id s n t.

Inductive repr_rel_node (s: sol): TypeTree -> TypeTree -> Prop :=
| repr_rel_node_var:
    forall n t, repr_rel_id s n t -> repr_rel_node s (TVar n) t
| repr_rel_node_not_var:
    forall t, not_var t -> repr_rel_node s t t.

Definition not_occur_final (s: sol) (n: TypeVarID) (t: TypeTree): Prop :=
  forall sc,
  sol_compress_to s sc ->
  ~occur n (type_subst t sc).

Inductive unify_rel: TypeTree -> TypeTree -> sol -> sol -> Prop :=
| unify_rel_left_var:
    forall s t1 n1 t2 t2',
      repr_rel_node s t1 (TVar n1) ->
      repr_rel_node s t2 t2' ->
      not_occur_final s n1 t2' ->
      unify_rel t1 t2 s (sol_update s n1 t2')
| unify_rel_right_var:
    forall s t1 t1' t2 n2,
      repr_rel_node s t1 t1' ->
      repr_rel_node s t2 (TVar n2) ->
      not_occur_final s n2 t1' ->
      unify_rel t1 t2 s (sol_update s n2 t1')
| unify_rel_apply:
    forall s0 s1 s2 t1 t11 t12 t2 t21 t22,
      repr_rel_node s0 t1 (TApply t11 t12) ->
      repr_rel_node s0 t2 (TApply t21 t22) ->
      unify_rel t11 t21 s0 s1 ->
      unify_rel t12 t22 s1 s2 ->
      unify_rel t1 t2 s0 s2
| unify_rel_arrow:
    forall s0 s1 s2 t1 t11 t12 t2 t21 t22,
      repr_rel_node s0 t1 (TArrow t11 t12) ->
      repr_rel_node s0 t2 (TArrow t21 t22) ->
      unify_rel t11 t21 s0 s1 ->
      unify_rel t12 t22 s1 s2 ->
      unify_rel t1 t2 s0 s2
| unify_rel_atom:
    forall s t1 t2 n,
      repr_rel_node s t1 (TAtom n) ->
      repr_rel_node s t2 (TAtom n) ->
      unify_rel t1 t2 s s.

Definition unify_sound: Prop :=
  forall t1 t2 s_pre s_post s_cpre,
  sol_compress_to s_pre s_cpre ->
  sol_no_loop s_pre ->
  sol_finite s_cpre ->
  unify_rel t1 t2 s_pre s_post ->
  exists s_cpost,
    sol_compress_to s_post s_cpost /\
    sol_no_loop s_post /\
    sol_finite s_cpost /\
    sol_correct_iter t1 t2 s_cpre s_cpost.

Fixpoint store_type(p: addr) (t: TypeTree) : Assertion :=
  match t with
    | TVar n =>
      [|0 <= n|] && [|n < 100|] &&
      (&((p) # "atype" ->ₛ "t") # Int |-> 3) **
      (&((p) # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    | TAtom n =>
      (&((p) # "atype" ->ₛ "t") # Int |-> 0) **
      (&((p) # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> n)
    | TArrow from to =>
      EX p1 p2,
      (&(p # "atype" ->ₛ "t") # Int |-> 1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> p2) **
      store_type p1 from ** store_type p2 to
    | TApply tfn rand =>
      EX p1 p2,
      (&(p # "atype" ->ₛ "t") # Int |-> 2) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> p2) **
      store_type p1 tfn ** store_type p2 rand
  end.

Definition store_type_aux(p: addr) (tp: TypeVarID) (t : TypeTree) : Assertion :=
  match t with
    | TVar n =>
      [| tp = 3 |] &&
      [|0 <= n|] && [|n < 100|] &&
      (&((p) # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    | TAtom n =>
      [| tp = 0 |] &&
      (&((p) # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> n)
    | TArrow from to =>
      EX p1 p2,
      [| tp = 1 |] &&
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> p2) **
      store_type p1 from ** store_type p2 to
    | TApply tfn rand =>
      EX p1 p2,
      [| tp = 2 |] &&
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> p2) **
      store_type p1 tfn ** store_type p2 rand
  end.

Definition store_option_type (x: addr) (t: option TypeTree) : Assertion :=
  match t with
  | None => [| x = NULL |] && emp
  | Some t => [| x <> NULL |] && store_type x t
end.

(* Pointer to pointer | Address of address *)
Definition store_type_addr (s : sol) (x: addr) (m: Z) (p: addr) : Assertion :=
  (x + m * sizeof(PTR)) # Ptr |-> p ** store_option_type p (s m).

Definition store_solution(x: addr) (s: sol): Assertion :=
EX l : (list addr),
  store_array (store_type_addr s) x 100 l.

(* x[n] = y. Solution except for lo == n  *)
Definition store_solution_aux(x : addr) (s : sol) (n : Z) (y : addr) (t : option TypeTree): Assertion :=
EX l : (list addr),
  [| 0 <= n |] && [| n < 100 |] && [| y = Znth n l 100 |] && [| t = s n |] &&
  ((x + n * sizeof(PTR)) # Ptr |-> y) **
  (store_option_type y t) **
  (store_array_missing_i_rec (store_type_addr s) x n 0 100 l).

Definition solution_at(s : sol) (n : Z) (t : TypeTree) : Prop :=
  Some t = s n.

Definition not_occur (n: Z) (t: TypeTree): Prop :=
  ~occur n t.

Definition debug: Assertion :=
  emp.

Lemma solution_split: forall s x n,
  0 <= n < 100 ->
  store_solution x s
  |-- EX y, store_solution_aux x s n y (s n).
Proof.
  intros.
  unfold store_solution.
  Intros l.
  rewrite (store_array_split (store_type_addr s) x n 100 l 100) .
  2: auto.

  unfold store_solution_aux.
  Exists (Znth n l 100) l.
  entailer!.
Qed.

Lemma store_some_type: forall x o,
  x <> 0 ->
  store_option_type x o
  |-- EX t, [|o = Some t|] && store_type x t.
Proof.
  intros.
  destruct o.
  - intros.
    unfold store_option_type.
    Exists t.
    entailer!.
  - intros.
    unfold store_option_type.
    entailer!.
Qed.

Lemma store_none_type: forall x,
  store_option_type x None
  |-- emp.
Proof.
  intros.
  unfold store_option_type.
  entailer!.
Qed.
