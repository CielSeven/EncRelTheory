Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qcanon.
Require Import Lia.


Require Import AUXLib.Feq.
From LangLib.ImpP Require Import PermissionModel.

(**********************************************************************************)
(*                                                                                *)
(*                   memory model with fractional premission                      *)
(*                        permission mem map: mem                                 *)
(*                                                                                *)
(**********************************************************************************)
Local Open Scope Qc_scope.

Notation "'addr'" := Z (at level 1, only parsing).
(* Address type, using Z for simplicity *)
Definition addr_eqb : addr -> addr -> bool := Z.eqb.
Definition addr_dec : forall (x y : addr), {x = y} + {x <> y} := Z.eq_dec.

Definition addr_eqb_eq : forall p1 p2,
  addr_eqb p1 p2 = true <-> p1 = p2 := Z.eqb_eq.

Definition addr_eqb_neq : forall p1 p2,
  addr_eqb p1 p2 = false <-> p1 <> p2 := Z.eqb_neq.

Definition addr_eqb_refl : forall p,
  addr_eqb p p = true := Z.eqb_refl.

Ltac addr_destruct x y :=
  let H := fresh "E" in
  destruct (addr_eqb x y) eqn:H;
  [apply addr_eqb_eq in H | apply addr_eqb_neq in H].

Inductive vtype : Type := 
  vint  | vptr. 

Definition value : Type := (Z * vtype)%type.

Definition memblock: Type := (value * Perm.t).

Definition mem : Type := addr -> option memblock.

Definition empty_mem : mem := fun p => None.

Definition single_mem (p : addr)  (b : memblock) : mem :=
  fun p' => if addr_eqb p' p then Some b else None.

Definition mem_update' (m : mem) (p : addr) (v : value) : option mem :=
  match m p with 
  | None => None 
  | Some (_, t) => if Perm.writable_permB t then Some (fun p' => if addr_eqb p' p then Some (v, t) else m p') 
              else None
  end.

Definition mem_update (m : mem) (p : addr) (v : value) :  mem := 
  fun p' => match mem_update' m p v with | None => None | Some m' => m' p' end.


Definition mem_remove' (m : mem) (p : addr) : option mem :=
  match m p with 
  | None => None 
  | Some (_, t) => if Perm.writable_permB t then Some (fun p' => if addr_eqb p' p then None else m p') 
              else None
  end.

Definition mem_remove (m : mem) (p : addr) :  mem := 
  fun p' => match mem_remove' m p  with | None => None | Some m' => m' p' end.  


Definition mem_add (m: mem) (p: addr) (b: memblock) : mem :=
  fun p' => if addr_eqb p' p then Some b else m p'.

Fixpoint mem_add_list (m : mem) (ps : list addr) (ns : list value) :  mem :=
  match ps, ns with
  | p :: ps', n :: ns' =>  mem_add ( mem_add_list m ps' ns') p (n, Perm.fullperm) 
  | _, _ => m
  end.

Fixpoint Zseq (p: addr) (n: nat) : list Z :=
  match n with 
  | O => nil 
  | S n' => p :: (Zseq (p + 1)%Z  n')
  end.


Definition mem_add_N (m : mem) (p : addr) (v: Z) (vl : list vtype) (n : nat) :  mem :=
  mem_add_list m (Zseq p n) (map (fun (t: vtype) => (v, t)) vl).

Definition mem_empty (m : mem) : Prop :=
  forall p, m p = None.

Definition mem_single (m : mem) (p : addr) (n : memblock) : Prop :=
  m p = Some n /\ (forall p', p' <> p -> m p' = None).


Definition mem_join (m1 m2 m: mem) : Prop :=
  forall p,
  (m1 p = None /\ m2 p = None /\ m p = None) \/
  (exists n, m1 p = None /\ m2 p = Some n /\ m p = Some n) \/
  (exists n, m1 p = Some n /\ m2 p = None /\ m p = Some n) \/ 
  (exists t1 t2 t3 i, Perm.join t1 t2 t3 /\ m1 p = Some (i, t1) /\ m2 p = Some (i, t2) /\ m p = Some (i,t3) ).

Definition Perm_add_aux (t1 t2: Perm.t) : Qc :=
  match (t1.(frac) +ᶜ t2.(frac))  ?= 1 with 
  |Gt  => 1 | _ => (t1.(frac) + t2.(frac)) end.

Lemma Perm_add_aux_range : forall t1 t2 , Perm.perRange  (Perm_add_aux t1 t2) .
Proof. 
  intros. unfold Perm.perRange,Perm_add_aux.
  destruct t1 as [q ?]. destruct t2 as [q0 ?].
  simpl in *.
  destruct ((q + q0 ?= 1)) eqn:?.
  - rewrite <- Qceq_alt in Heqc.
    rewrite Heqc.
    unfoldlt. simpl in *. lia.
  - rewrite <- Qclt_alt in Heqc.
    unfold Perm.perRange in *.
    split.
    apply plus_positives_gt0;try tauto.
    tauto.
  - unfoldlt. simpl in *. lia.
Qed.

Definition value_eqb (v1 v2: value) :=
  let (z1,t1) := v1 in let (z2,t2) := v2 in 
  match t1, t2 with 
  | vint, vint => Z.eqb z1 z2 
  | vptr, vptr => Z.eqb z1 z2 
  | _, _ => false
  end.


Definition bjoin (b1 b2 : memblock) : option memblock :=
    match b1, b2 with
    | (x, t1),  (y, t2) =>
      if (value_eqb x y) then 
            match (t1.(frac) +ᶜ t2.(frac))  ?= 1 with 
            |Gt  => None | _ => Some (x,(Perm.mkper (Perm_add_aux t1 t2) (Perm_add_aux_range t1 t2))) end
      else None
    end.

Definition merge (m1 m2:mem)  : mem :=
  fun (a : addr) =>
  match (m1 a, m2 a) with
  | (Some b1, Some b2) => bjoin b1 b2
  | (Some b1, None) => Some b1
  | (None, Some b2) => Some b2
  | (None, None) => None
  end.

Ltac my_destruct H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | mem => let m := fresh "m" in destruct H as [m H];my_destruct H
              | addr -> option Z => let m := fresh "m" in destruct H as [m H];my_destruct H
              | value => let i := fresh "v" in destruct H as [i H];my_destruct H
              | Perm.t => let i := fresh "t" in destruct H as [i H];my_destruct H
              | memblock  => let i := fresh "b" in destruct H as [i H];my_destruct H
              | _ => destruct H as [? H];my_destruct H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct H;
              my_destruct H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct H
  | _ => (discriminate || contradiction  || idtac)
  end.

Ltac splits :=
  match goal with 
  | |- _ /\ _ => split;splits
  | |- _ => idtac end.

#[export] Instance mem_join_congr :
  Proper (f_eq ==> f_eq ==> f_eq ==> iff) mem_join.
Proof.
  unfold Proper, respectful, mem_join, f_eq.
  intros. split.
  - intros.
    specialize (H p). specialize (H0 p). specialize (H1 p).
    specialize (H2 p).
    repeat split; intros; my_destruct H2;
    [left | right; left; exists b | right; right;left; exists b| right;right;right ];
    repeat split; try congruence.
    exists t, t0, t1, v.
    splits;congruence.
  - intros.
    specialize (H p). specialize (H0 p). specialize (H1 p).
    specialize (H2 p).
    repeat split; intros; my_destruct H2;
    [left | right; left; exists b | right; right;left; exists b| right;right;right ];
    repeat split; try congruence.
    exists t, t0, t1, v.
    splits;congruence.
Qed.

Lemma empty_mem_empty : mem_empty empty_mem.
Proof.
  unfold mem_empty, empty_mem. auto.
Qed.

Lemma mem_empty_IS_empty_mem : forall m, mem_empty m -> f_eq m empty_mem.
Proof.
  unfold mem_empty, empty_mem, f_eq. intros.  auto.
Qed.

Lemma single_mem_single : forall p n, mem_single (single_mem p n) p n.
Proof.
  unfold mem_single, single_mem.
  intros. split; intros.
  - addr_destruct p p; congruence.
  - addr_destruct p' p; congruence.
Qed.

Lemma mem_join_comm : forall m1 m2 m,
  mem_join m1 m2 m ->
  mem_join m2 m1 m.
Proof.
  unfold mem_join. intros.
  specialize (H p);my_destruct H.
  - left. tauto.
  - right. right;left. exists b. tauto.
  - right. left. exists b. tauto.
  - right; right; right.
    exists t0, t, t1, v.
    splits;auto.
    apply Perm.join_comm;auto.
Qed.

Arguments mem_join_comm [m1] [m2] [m].

