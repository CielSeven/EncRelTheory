Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.

Require Import compcert.lib.Integers.
From AUXLib Require Import Feq Idents List_lemma int_auto ListLib.
From FP Require Import SetsFixedpoints.
From SetsClass Require Import SetsClass.
From EncRelSeq Require Import callsem basicasrt contexthoare_imp.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib.

Import SetsNotation.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(**********************************************************************************)
(*                                                                                *)
(*               imperitive language model with memory permission                 *)
(*                                                                                *)
(**********************************************************************************)


Inductive aexp : Type :=
  | ENull : aexp 
  | ENum : Z -> aexp
  | EVarLocal : var -> aexp
  | EVarGlobal : var -> aexp
  | EAdd : aexp -> aexp -> aexp
  | ESub : aexp -> aexp -> aexp
  | EMul : aexp -> aexp -> aexp
  | EDiv : aexp -> aexp -> aexp
.


Inductive bexp : Type :=
  | ETrue : bexp
  | EFalse : bexp
  | EEq : aexp -> aexp -> bexp
  | ENe : aexp -> aexp -> bexp
  | ELt : aexp -> aexp -> bexp
  | ELe : aexp -> aexp -> bexp
  | ENot : bexp -> bexp
  | EAnd : bexp -> bexp -> bexp
  | EOr : bexp -> bexp -> bexp
.

Inductive com : Type :=
  | CSkip : com
  | CAsgnLocal : var -> aexp -> com
  | CAsgnGlobal : var -> aexp -> com
  | CLoad : var -> aexp -> com
  | CStore : aexp -> aexp -> com
  | CAlloc : var -> list vtype -> aexp -> com
  | CFree : aexp -> com
  | CCall : func -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
.


Definition main_func : func := 1%positive.

Coercion EVarLocal : var >-> aexp.
Coercion ENum : Z >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "'%' x" := (EVarGlobal x) (in custom com at level 0, x constr at level 0).
Notation "x + y" := (EAdd x y) (in custom com at level 50, left associativity).
Notation "x - y" := (ESub x y) (in custom com at level 50, left associativity).
Notation "x * y" := (EMul x y) (in custom com at level 40, left associativity).
Notation "x ÷ y" := (EDiv x y) (in custom com at level 39, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := ETrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := EFalse (in custom com at level 0).
Notation "x == y"  := (EEq x y) (in custom com at level 70, no associativity).
Notation "x != y"  := (ENe x y) (in custom com at level 70, no associativity).
Notation "x < y" := (ELt x y) (in custom com at level 70, no associativity).
Notation "x <= y" := (ELe x y) (in custom com at level 70, no associativity).
Notation "'!' b"  := (ENot b) (in custom com at level 75, right associativity).
Notation "x && y" := (EAnd x y) (in custom com at level 80, left associativity).
Notation "x || y" := (EOr x y) (in custom com at level 80, left associativity).
Notation "'Skip'"  := CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgnLocal x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity) : com_scope.
Notation "% x := y"  := (CAsgnGlobal x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity) : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'If' x 'Then' y 'Else' z 'End'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99) : com_scope.
Notation "'While' x 'Do' y 'End'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99) : com_scope.
Notation "'Call' '(' f ')'" := (CCall f)
  (in custom com at level 0) : com_scope.
Notation "'Load' '(' x ',' '*' e ')'" := (CLoad x e)
  (in custom com at level 0) : com_scope.
Notation "'Store' '(' '*' e1 ',' e2 ')'" := (CStore e1 e2)
  (in custom com at level 0) : com_scope.
Notation "x := '[' e ']'" := (CLoad x e)
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'[' e1 ']' := e2" := (CStore e1 e2)
  (in custom com at level 0, e2 at level 85, no associativity) : com_scope.
Notation "'Alloc' '(' x ',' tl ',' e ')'" := (CAlloc x tl e)
  (in custom com at level 0) : com_scope.
Notation "'Free' '(' x ')'" := (CFree x)
  (in custom com at level 0) : com_scope.


#[global] Instance memjoinm : @JoinM  mem := {|
  join :=  mem_join;
  is_unit:= mem_empty;
|}.


#[global] Instance implgstate: lgstate :={
  local_env := var -> value ;
  global_env := var -> value;
  memory := mem;
  memm := memjoinm;
}.


Definition state := local_cstate.

Definition substmem (σ : state) (m : mem) : state :=
  mk_lstate σ.(lenv) σ.(genv) m.
  
(**********************************************************************************)
(*              表达式的denotation                                                 *)
(**********************************************************************************)
Module EDenote.


Record EDenote: Type := {
  nrm: state -> value -> Prop;
  err: state -> Prop;
}.

End EDenote.

Ltac any_nrm x ::=
  match type of x with
  | EDenote.EDenote => exact (EDenote.nrm x)
  | practicaldeno.denosem => exact (practicaldeno.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote.EDenote => exact (EDenote.err x)
  | practicaldeno.denosem => exact (practicaldeno.err x)
  end.

Import EDenote.
Definition null_denote  : EDenote :=
  {|
    nrm := fun s '(i,t) =>
             i = 0 /\ t = vptr; 
    err := ∅;
  |}.

Definition const_denote (n : Z) : EDenote :=
  {|
    nrm := fun s '(i,t) =>
             i = n /\ t = vint /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition local_var_denote (x : var) : EDenote := 
  {|
    nrm := fun s i => i = s.(lenv) x;
    err := ∅;
  |}.  


Definition global_var_denote (gx : var) : EDenote :=
  {|
    nrm := fun s i => i = s.(genv) gx;
    err := ∅;
  |}.

Inductive Zbop : Type := zadd | zsub | zmul | zdiv. 

Definition arith_compute (op: Zbop) (v1: value) (v2: value)  (r: value) : Prop :=
  let (z1,t1) := v1 in 
  let (z2,t2) := v2 in 
  match op, t1, t2 with 
  | zadd, vint, vint =>  r = (Int64.signed (Int64.repr (z1 + z2)), vint)
  | zsub, vint, vint =>  r = (Int64.signed (Int64.repr (z1 - z2)), vint)
  | zmul, vint, vint =>  r = (Int64.signed (Int64.repr (z1 * z2)), vint)
  | zdiv, vint, vint =>  z2 <> 0 /\ r = (Int64.signed (Int64.repr (Z.div z1 z2)), vint)
  | zadd, vptr, vint =>  r = (z1 + z2, vptr)
  | zsub, vptr, vint =>  r = (z1 - z2, vptr) 
  | _, _, _ => False
  end.

Definition arith_compute_err (op: Zbop) (v1: value) (v2: value)  : Prop :=
  let (z1,t1) := v1 in 
  let (z2,t2) := v2 in 
  match op, t1, t2 with 
  | zdiv, vint, vint =>  z2 = 0 
  | zmul, vptr, vint =>  True
  | zdiv, vptr, vint =>  True
  | _, _ , vptr =>  True
  | _, _, _ => False
  end.

Definition arith_sem_nrm (op: Zbop)
             (D1 D2: state -> value -> Prop)
             (s: state)
             (i: value): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute op i1 i2 i.

Definition arith_sem_err (op: Zbop)
             (D1 D2: state -> value -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute_err op i1 i2.

Definition arith_sem op (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem_nrm op D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪  arith_sem_err op D1.(nrm) D2.(nrm);
  |}.

Fixpoint aeval (e : aexp) : EDenote :=
  match e with
  | ENull => null_denote
  | ENum n => const_denote n
  | EVarLocal x => local_var_denote x
  | EVarGlobal gx => global_var_denote gx
  | EAdd e1 e2 => arith_sem zadd (aeval e1) (aeval e2)
  | ESub e1 e2 => arith_sem zsub (aeval e1) (aeval e2)
  | EMul e1 e2 => arith_sem zmul (aeval e1) (aeval e2)
  | EDiv e1 e2 => arith_sem zdiv (aeval e1) (aeval e2)
  end.

Definition true_denote : EDenote :=
  {|
    nrm := fun s i => i = (1, vint);
    err := ∅
  |}.

Definition false_denote : EDenote :=
  {|
    nrm := fun s i => i = (0, vint);
    err := ∅
  |}.

Definition zcmp (c: comparison) (x y: Z) : bool :=
  match c with
  | Ceq => Z.eqb x y
  | Cne => negb (Z.eqb x y)
  | Clt => Z.ltb x y
  | Cle => negb (Z.ltb y x)
  | Cgt => Z.ltb y x
  | Cge => negb (Z.ltb x y)
  end.


Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2: Z)
             (v: value) : Prop :=
  v = if zcmp c i1 i2
      then (1, vint)
      else (0, vint).

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> value -> Prop)
             (s: state)
             (v: value) : Prop :=
  exists i1 i2,
    D1 s (i1,vint) /\ D2 s (i2,vint) /\ cmp_compute_nrm c i1 i2 v.

Definition cmp_compute_err
             (v1 v2 : value) : Prop :=
  let (z1,t1) := v1 in 
  let (z2,t2) := v2 in 
  match t1, t2 with 
  | vint, vint =>  False 
  | _, _  =>  True
  end.


Definition cmp_sem_err
             (D1 D2: state -> value -> Prop)
             (s: state) : Prop :=
  exists v1 v2,
    D1 s v1 /\ D2 s v2 /\ cmp_compute_err v1 v2.


Definition cmp_denote c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪ cmp_sem_err D1.(nrm) D2.(nrm);
  |}.


Definition eqneq_sem_nrm
             (c: comparison)
             (D1 D2: state -> value -> Prop)
             (s: state)
             (v: value) : Prop :=
  exists i1 i2 t,
    D1 s (i1, t) /\ D2 s (i2, t) /\ cmp_compute_nrm c i1 i2 v.

Definition eqneq_compute_err
             (v1 v2 : value) : Prop :=
  let (z1,t1) := v1 in 
  let (z2,t2) := v2 in 
  match t1, t2 with 
  | vint, vint =>  False 
  | vptr, vptr =>  False 
  | _, _  =>  True
  end.


Definition eqneq_sem_err
             (D1 D2: state -> value -> Prop)
             (s: state) : Prop :=
  exists v1 v2,
    D1 s v1 /\ D2 s v2 /\ eqneq_compute_err v1 v2.

Definition eqneq_denote c (D1 D2: EDenote): EDenote :=
  {|
    nrm := eqneq_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪ eqneq_sem_err D1.(nrm) D2.(nrm);
  |}.

Definition not_compute_nrm (i1 i: Z): Prop :=
  i1 <> 0 /\ i = 0 \/
  i1 =  0 /\ i =  1.

Definition not_sem_nrm
             (D1: state -> value -> Prop)
             (s: state)
             (v: value): Prop :=
  exists i1 i, D1 s (i1, vint) /\ not_compute_nrm i1 i /\ v = (i, vint).

Definition not_sem_err
             (D1: state -> value -> Prop)
             (s: state) : Prop :=
  exists i1, D1 s (i1, vptr).

Definition not_denote (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err)  ∪  not_sem_err D1.(nrm) ;
  |}.

Definition SC_and_compute_nrm (i1 i: Z): Prop :=
  i1 = 0 /\ i =  0.

Definition SC_or_compute_nrm (i1 i: Z): Prop :=
  i1 <> 0 /\ i = 1.

Definition NonSC_and (i1: Z): Prop :=
  i1 <> 0.

Definition NonSC_or (i1: Z): Prop :=
  i1 = 0.

Definition NonSC_compute_nrm (i2 i: Z): Prop :=
  i2 = 0 /\ i = 0 \/
  i2 <> 0 /\ i = 1.

Definition and_sem_nrm
             (D1 D2: state -> value -> Prop)
             (s: state)
             (v: value): Prop :=
  exists i1 ,
    D1 s (i1, vint) /\
    ( (exists i, SC_and_compute_nrm i1 i /\ v = (i, vint)) \/
     NonSC_and i1 /\
     exists i2 i,
       D2 s (i2, vint) /\ NonSC_compute_nrm i2 i /\ v = (i, vint) ).

Definition and_sem_err
             (D1: state -> value -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s (i1,vint) /\ NonSC_and i1 /\ D2 s.

Definition and_sem_err2
             (D1: state -> value -> Prop)
             (D2: state -> value ->  Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s (i1,vint) /\ NonSC_and i1 /\ D2 s (i2, vptr).

Definition andor_sem_err
             (D1: state -> value -> Prop)
             (s: state): Prop :=
  exists i1,
  D1 s (i1,vptr).

Definition and_denote (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err)∪ andor_sem_err D1.(nrm)  ∪  
           and_sem_err D1.(nrm) D2.(err) ∪ and_sem_err2 D1.(nrm) D2.(nrm);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> value -> Prop)
             (s: state)
             (v: value): Prop :=
  exists i1,
    D1 s (i1,vint) /\
    ((exists i, SC_or_compute_nrm i1 i /\ v = (i, vint)) \/
     NonSC_or i1 /\
     exists i2 i,
       D2 s (i2,vint) /\ NonSC_compute_nrm i2 i /\ v = (i, vint)).

Definition or_sem_err
             (D1: state -> value -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s (i1, vint) /\ NonSC_or i1 /\ D2 s.

Definition or_sem_err2
             (D1 D2: state -> value -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s (i1, vint) /\ NonSC_or i1 /\ D2 s (i2, vptr).

Definition or_denote (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ andor_sem_err D1.(nrm) ∪ or_sem_err D1.(nrm) D2.(err) 
          ∪ or_sem_err2 D1.(nrm) D2.(nrm);
  |}.

Fixpoint beval (b : bexp) : EDenote :=
  match b with
  | ETrue => true_denote
  | EFalse => false_denote
  | EEq e1 e2 => eqneq_denote Ceq (aeval e1) (aeval e2)
  | ENe e1 e2 => eqneq_denote Cne (aeval e1) (aeval e2)
  | ELt e1 e2 => cmp_denote Clt (aeval e1) (aeval e2)
  | ELe e1 e2 => cmp_denote Cle (aeval e1) (aeval e2)
  | ENot b0 => not_denote (beval b0)
  | EAnd b1 b2 => and_denote (beval b1) (beval b2)
  | EOr b1 b2 => or_denote (beval b1) (beval b2)
  end.

(***********************************************************************************)
(*              程序语句的denotation                                               *)
(*          field necall : nrm_err_call                                            *)
(***********************************************************************************)
Import practicaldeno.

Definition asgn_local_denote (x:var) (De : EDenote) : @denosem state :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        De.(nrm) s1 i /\ s2.(lenv) x = i /\
        (forall Y, x <> Y -> s1.(lenv) Y = s2.(lenv) Y) /\
        f_eq s1.(genv) s2.(genv) /\
        f_eq s1.(st_mem) s2.(st_mem);
    err := De.(err);
  |}.

Definition asgn_global_denote (gx : var) (De : EDenote) : @denosem state :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        De.(nrm) s1 i /\ s2.(genv) gx = i /\
        (forall Y, gx <> Y -> s1.(genv) Y = s2.(genv) Y) /\
        f_eq s1.(lenv) s2.(lenv) /\
        f_eq s1.(st_mem) s2.(st_mem);
    err := De.(err);
  |}.

Definition load_sem_nrm (x: var)
             (D: state -> value -> Prop)
             (st1: state)
             (st2: state): Prop :=
  exists pi i,
        D st1 (pi, vptr) /\ pi > 0 /\ 
        st1.(st_mem) pi = Some i /\
        st2.(lenv) x = fst i /\
        (forall y, y <> x -> st1.(lenv) y = st2.(lenv) y) /\
        f_eq st1.(genv) st2.(genv) /\
        f_eq st1.(st_mem) st2.(st_mem).

Definition load_sem_err (x: var)
             (D: state -> value  -> Prop)
             (st1: state) : Prop :=
  exists pi t,
        D st1 (pi, t) /\ 
        ( t = vint \/  t = vptr /\
        (pi <= 0 \/ 
        st1.(st_mem) pi = None)). 

Definition load_denote (x : var) (De : EDenote) : @denosem state :=
  {|
    nrm := load_sem_nrm x (De.(nrm));
    err := De.(err) ∪ load_sem_err x (De.(nrm));
  |}.

Definition asgn_deref_sem_nrm
             (D1 D2: state -> value -> Prop)
             (s1 s2: state): Prop :=
  exists p v,
    D1 s1 (p, vptr) /\ 
    D2 s1 v /\ p > 0 /\
    writable_m s1.(st_mem) p  /\
    s2.(st_mem) p = Some (v, Perm.fullperm) /\
    f_eq s1.(lenv) s2.(lenv) /\
    f_eq s1.(genv) s2.(genv) /\
    (forall p', p' <> p -> s1.(st_mem) p' = s2.(st_mem) p').

Definition asgn_deref_sem_err
             (D1: state -> value -> Prop)
             (s1: state): Prop :=
  exists i1 t1,
    D1 s1 (i1, t1) /\ 
    (t1 = vint \/ t1 = vptr /\ (i1 = 0 \/ 
    ~ writable_m s1.(st_mem) i1) ).

Definition store_denote (De1 De2 : EDenote) : @denosem state :=
  {|
    nrm := asgn_deref_sem_nrm De1.(nrm) De2.(nrm);
    err := De1.(err) ∪ De2.(err) ∪
           asgn_deref_sem_err De1.(nrm);
  |}.

Definition alloc_sem_nrm (x: var) (tl: list vtype)
                          (D1: state -> value -> Prop)
                          (st1 st2: state): Prop :=
  exists i,
    D1 st1 (i, vint) /\ i >= 0 /\
    exists p0, p0 > 0 /\
    (forall p, p >= p0 -> p < p0 + i -> st1.(st_mem) p = None) /\
    (forall p, p >= p0 -> p < p0 + i -> st2.(st_mem) p = Some ((0, Znth (p - p0) tl vint), Perm.fullperm)) /\
    (forall p, (p < p0 \/ p >= p0 + i) -> st1.(st_mem) p = st2.(st_mem) p) /\
    st2.(lenv) x = (p0, vptr) /\
    (forall y, y <> x -> st1.(lenv) y = st2.(lenv) y) /\
    f_eq st1.(genv) st2.(genv).


Definition alloc_denote (x : var) (tl: list vtype) (De : EDenote) : @denosem state:=
  {|
    nrm := alloc_sem_nrm x tl De.(nrm);
    err := De.(err)
           (*   不考虑内存不够导致的失败alloc *);
  |}.

Definition free_sem_nrm (D1: state -> value -> Prop)
                        (st1 st2: state): Prop :=
  exists p,
    D1 st1 (p, vptr) /\ 
    writable_m st1.(st_mem) p  /\
    st2.(st_mem) p = None /\
    (forall p', p' <> p -> st1.(st_mem) p' = st2.(st_mem) p') /\
    f_eq st1.(lenv) st2.(lenv) /\
    f_eq st1.(genv) st2.(genv).

Definition free_sem_err
             (D1: state -> value -> Prop)
             (s1: state): Prop :=
  exists i t,
    D1 s1 (i, t) /\ 
    ( t = vint \/ t = vptr /\ 
    ( i = 0 /\
    ~ writable_m s1.(st_mem) i)).

Definition free_denote (De : EDenote) : @denosem state:=
  {|
    nrm := free_sem_nrm De.(nrm);
    err := De.(err) ∪
           free_sem_err De.(nrm);
  |}.



Definition test_true (D: EDenote):
  state -> state -> Prop :=
  fun st1 st2 => exists i t, D.(nrm) st1 (i, t) /\ i <> 0 /\ st2 = st1.

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  fun st1 st2 => exists t,  D.(nrm) st1 (0, t) /\ st1 = st2.


Definition if_denote
             (D0: EDenote)
             (D1 D2:@denosem state): @denosem state :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           ((test_true D0) ∘ D1.(err)) ∪
           ((test_false D0) ∘ D2.(err));
  |}.

Definition while_denote
             (Db: EDenote)
             (Dc: @denosem state): @denosem state :=
  {|
    nrm := Lfix (fun X => (test_true Db ∘ Dc.(nrm) ∘ X) ∪ test_false Db);
    err := Lfix (fun X => ((test_true Db) ∘ ((Dc.(nrm) ∘ X) ∪ Dc.(err))) ∪ Db.(err))
  |}.

Import PracticalDenoConstructs.
Import EnvProgramSem.
Section Ceval.

Variable χnrm : func -> global_cstate -> global_cstate -> Prop.
Variable χerr : func -> global_cstate ->  Prop.

Fixpoint cevalnrm (c : com) : state -> state -> Prop :=
 match c with
 | CSkip => (@skip state).(nrm)
 | CAsgnLocal x e => (asgn_local_denote x (aeval e)).(nrm)
 | CAsgnGlobal gx e => (asgn_global_denote gx (aeval e)).(nrm)
 | CLoad x e => (load_denote x (aeval e)).(nrm)
 | CStore e1 e2 => (store_denote (aeval e1) (aeval e2)).(nrm)
 | CAlloc x t e => (alloc_denote x t (aeval e)).(nrm)
 | CFree e => (free_denote (aeval e)).(nrm)
 | CCall f =>  call_nrm χnrm f
 | CSeq c1 c2 => (cevalnrm c1) ∘ (cevalnrm c2)
 | CIf b c1 c2 =>  (test_true (beval b) ∘ (cevalnrm c1)) ∪
                   (test_false (beval b) ∘ (cevalnrm c2))
 | CWhile b c0 => Lfix (fun X => (test_true (beval b) ∘ (cevalnrm c0) ∘ X) ∪ test_false (beval b))
 end.


Fixpoint cevalerr (c : com) : state -> Prop :=
 match c with
 | CSkip => (@skip state).(err)
 | CAsgnLocal x e => (asgn_local_denote x (aeval e)).(err)
 | CAsgnGlobal gx e => (asgn_global_denote gx (aeval e)).(err)
 | CLoad x e => (load_denote x (aeval e)).(err)
 | CStore e1 e2 => (store_denote (aeval e1) (aeval e2)).(err)
 | CAlloc x tl e => (alloc_denote x tl (aeval e)).(err)
 | CFree e => (free_denote (aeval e)).(err)
 | CCall f =>  call_err χerr f
 | CSeq c1 c2 =>  (cevalerr c1) ∪ ((cevalnrm c1) ∘ (cevalerr c2))
 | CIf b c1 c2 =>  (test_true (beval b) ∘ (cevalerr c1)) ∪
                   (test_false (beval b) ∘ (cevalerr c2))
 | CWhile b c0 => Lfix (fun X => ((test_true (beval b)) ∘ 
                              (((cevalnrm c0) ∘ X) ∪ (cevalerr c0))) ∪ (beval b).(err))
 end.

End Ceval.


#[global] Instance  impcalllang : @calllang_envstate state global_cstate:= {
  Langstmts:= com;
  evalnrm:= cevalnrm;
  evalerr:= cevalerr
}.



Section ModLocal.

Variable x : var.

Fixpoint modvars_local (c : com) : bool :=
  match c with
  | CSkip => false
  | CAsgnLocal y _ => var_eqb y x
  | CAsgnGlobal _ _ => false
  | CLoad y _ => var_eqb y x
  | CStore _ _ => false
  | CAlloc y _ _ => var_eqb y x
  | CFree _ => false
  | CCall y => false
  | CSeq c1 c2 => modvars_local c1 || modvars_local c2
  | CIf _ c1 c2 => modvars_local c1 || modvars_local c2
  | CWhile _ c0 => modvars_local c0
  end.

End ModLocal.


Section ModGlobal.

Variable gx : var.

Fixpoint modvars_global (c : com) : bool :=
  match c with
  | CSkip => false
  | CAsgnLocal _ _ => false
  | CAsgnGlobal gy _ => var_eqb gy gx
  | CLoad _ _ => false
  | CStore _ _ => false
  | CAlloc _ _ _ => false
  | CFree _ => false
  | CCall _ => true
  | CSeq c1 c2 => modvars_global c1 || modvars_global c2
  | CIf _ c1 c2 => modvars_global c1 || modvars_global c2
  | CWhile _ c0 => modvars_global c0
  end.

End ModGlobal.


Lemma modvars_spec : forall (χnrm: func -> global_cstate -> global_cstate -> Prop)
  c st1 st2,
  (cevalnrm χnrm c) st1 st2 ->
  (forall x, modvars_local x c = false -> st1.(lenv) x = st2.(lenv) x) /\
  (forall gx, modvars_global gx c = false -> st1.(genv) gx = st2.(genv) gx).
Proof.
  induction c; simpl; intros.
  - sets_unfold in H. subst. auto.
  - unfold asgn_local_denote in H. destruct H as [? [? [? [? [? ?]]] ] ].
    split; intros; auto.
    eapply H1. apply var_eqb_neq in H4. auto.
  - unfold asgn_global_denote in H. destruct H as [? [? [? [? [? ?]]] ] ].
    split; intros; auto.
    apply H1. apply var_eqb_neq in H4. auto.
  - unfold load_sem_nrm in H.
    destruct H as [p [n [? [? [? [? [? [? ?] ] ] ] ] ] ] ].
    split; intros; auto.
    apply H3. apply var_eqb_neq in H6. auto.
  - unfold asgn_deref_sem_nrm in H.
    my_destruct H.
    split; intros; auto.
  - unfold alloc_sem_nrm in H.
    my_destruct H.
    split; intros; auto.
    apply H6. apply var_eqb_neq in H8. auto.
  - unfold free_sem_nrm in H.
    my_destruct H.
    split; intros; auto.
  - unfold call_nrm in H.
    destruct H as [? ?].
    split; intros; try congruence.
    destruct_st st1. destruct_st st2. cbn in H0. subst.
    cbn. auto.
  - destruct H as [st3 [? ?] ].
    apply IHc1 in H. destruct H. apply IHc2 in H0. destruct H0.
    split; intros.
    + apply Bool.orb_false_iff in H3. destruct H3.
      rewrite H; auto.
    + apply Bool.orb_false_iff in H3. destruct H3.
      rewrite H1; auto.
  - unfold test_true, test_false in H.
    destruct H as [ [st1' [ [? [? [? [? <-]]]] ?] ] | [st1' [ [? [? <-]] ?] ] ].
    + apply IHc1 in H1. destruct H1. split; intros.
      * apply Bool.orb_false_iff in H3. destruct H3. auto.
      * apply Bool.orb_false_iff in H3. destruct H3. auto.
    + apply IHc2 in H0. destruct H0. split; intros.
      * apply Bool.orb_false_iff in H2. destruct H2. auto.
      * apply Bool.orb_false_iff in H2. destruct H2. auto.
  - destruct H as [n ?]. revert H. revert st2 st1.
    induction n; intros; simpl in H.
    + inversion H.
    + destruct H as [ [st3 [ [? [? [? [? <-]]]] [st4 [? ?] ] ] ] | [? [? <-]] ]; auto.
      apply IHc in H1. destruct H1.
      apply IHn in H2. destruct H2.
      split; intros.
      * rewrite H1; auto.
      * rewrite H3; auto.
Qed.

 
(**********************************************************************************)
(*                                                                                *)
(*                    the following lemmas use excluded middle                    *)
(*                                                                                *)
(**********************************************************************************)
Definition ceval (χ : func -> @denosem global_cstate) c : @denosem state := {|
  nrm := evalnrm (fun f => (χ f).(nrm)) c;
  err := evalerr (fun f => (χ f).(nrm)) (fun f => (χ f).(err)) c
|}.

Require Import Coq.Logic.Classical_Prop.
Lemma cevalerr_exmid : forall c callees s1, 
  (ceval callees c).(err) s1\/ 
  ~ (ceval callees c).(err) s1.
Proof. intros. pose proof classic ((ceval callees c).(err) s1). auto. Qed.

Lemma aeval_excluded_middle : forall a st1,
  (exists i, (aeval a).(nrm) st1 i) \/ 
  (aeval a).(err) st1.
Proof.
  induction a;simpl;intros.
  - left. exists (0, vptr).  splits;eauto.
  - assert (z < Int64.min_signed \/ Int64.min_signed <= z) as [? | ?] by lia;[right;auto  | ].
    assert (z > Int64.max_signed \/ z <= Int64.max_signed) as [? | ?] by lia;[right;auto  | ].
    left.
    exists (z, vint).
    split;auto.
  - left.
    eexists.
    eauto. 
  - left.
    eexists.
    eauto.
  - sets_unfold.
    unfold arith_sem_nrm.
    specialize (IHa1 st1) as [[[i1 ?] ?] | ?];[ | auto].
    specialize (IHa2 st1) as [[[i2 ?] ?] | ?];[ | auto].
    destruct v,v0.
    left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right.  unfold arith_compute. do 2 eexists;splits;eauto;simpl;eauto.
    left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
  - sets_unfold.
    unfold arith_sem_nrm.
    specialize (IHa1 st1) as [[[i1 ?] ?] | ?];[ | auto].
    specialize (IHa2 st1) as [[[i2 ?] ?] | ?];[ | auto].
    destruct v,v0.
    left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right.  unfold arith_compute. do 2 eexists;splits;eauto;simpl;eauto.
    left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
  - sets_unfold.
    unfold arith_sem_nrm.
    specialize (IHa1 st1) as [[[i1 ?] ?] | ?];[ | auto].
    specialize (IHa2 st1) as [[[i2 ?] ?] | ?];[ | auto].
    destruct v,v0.
    left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right.  unfold arith_compute. do 2 eexists;splits;eauto;simpl;eauto.
    right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
  - sets_unfold.
    unfold arith_sem_nrm.
    specialize (IHa1 st1) as [[[i1 ?] ?] | ?];[ | auto].
    specialize (IHa2 st1) as [[[i2 ?] ?] | ?];[ | auto].
    destruct v,v0.
    + assert (i2 <> 0 \/ i2 = 0) as [ ?| ?] by lia.
      left. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
      right;right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    + right. right.  unfold arith_compute. do 2 eexists;splits;eauto;simpl;eauto.
    + right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
    + right. right. unfold arith_compute. do 3 eexists;splits;eauto;simpl;eauto.
Qed.


Lemma mem_join_aeval_nrm : forall a l g m1 m2 m3 i,
  mem_join m1 m2 m3 ->
  (aeval a).(nrm) (mk_lstate l g m1) i -> 
  (aeval a).(nrm) (mk_lstate l g m3) i.
Proof.
  induction a;simpl;sets_unfold; intros.
  - destruct i. auto. 
  - auto.
  - auto.
  - auto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
Qed.

Arguments mem_join_aeval_nrm [a] [l] [g] [m1] [m2] [m3] [i].

Lemma arith_compute_determined : forall op  v v0 r r0,
  arith_compute op v v0 r -> arith_compute op v v0 r0 ->  r = r0.
Proof.
  intros ? [? ?] [? ?] * H H0.
  unfold arith_compute in *;destruct op, v, v0; try congruence; try contradiction.
  destruct H, H0.
  congruence.
Qed.

Lemma mem_join_aeval_nrm_eq : forall a l g m1 m2 m3 i i0,
  mem_join m1 m2 m3 ->
  (aeval a).(nrm) (mk_lstate l g m3) i -> 
  (aeval a).(nrm) (mk_lstate l g m1) i0 -> i0 = i.
Proof.
  induction a;simpl;sets_unfold; intros.
  - destruct i, i0. destruct H0, H1. congruence. 
  - destruct i, i0. my_destruct H0;my_destruct H1. congruence.
  - congruence.
  - congruence.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    my_destruct H1.
    specialize (IHa1 _ _ _ _ _ _ _ H H0 H1).
    specialize (IHa2 _ _ _ _ _ _ _ H H2 H4);
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    my_destruct H1.
    specialize (IHa1 _ _ _ _ _ _ _ H H0 H1).
    specialize (IHa2 _ _ _ _ _ _ _ H H2 H4);
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    my_destruct H1.
    specialize (IHa1 _ _ _ _ _ _ _ H H0 H1).
    specialize (IHa2 _ _ _ _ _ _ _ H H2 H4);
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    my_destruct H1.
    specialize (IHa1 _ _ _ _ _ _ _ H H0 H1).
    specialize (IHa2 _ _ _ _ _ _ _ H H2 H4);
    subst.
    eapply arith_compute_determined;eauto.
Qed.

Arguments mem_join_aeval_nrm_eq [a] [l] [g] [m1] [m2] [m3] [i] [i0].

Lemma mem_join_aeval_nrm_rev : forall a l g m1 m2 m3 i,
  mem_join m1 m2 m3 ->
  (aeval a).(nrm) (mk_lstate l g m3) i -> 
  (aeval a).(nrm) (mk_lstate l g m1) i.
Proof.
  induction a;simpl;sets_unfold; intros.
  - auto.
  - auto.
  - auto.
  - auto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H0;
    exists v, v0;
    splits;
    intuition eauto.
Qed.

Arguments mem_join_aeval_nrm_rev [a] [l] [g] [m1] [m2] [m3] [i].

Lemma mem_join_aeval_err : forall a l g m1 m2 m3,
  mem_join m1 m2 m3 ->
  (aeval a).(err) (mk_lstate l g m1)  -> 
  (aeval a).(err) (mk_lstate l g m3).
Proof.
  induction a;simpl;sets_unfold; intros.
  - auto.
  - auto.
  - auto.
  - auto.
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm;eauto | eapply mem_join_aeval_nrm;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm;eauto | eapply mem_join_aeval_nrm;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm;eauto | eapply mem_join_aeval_nrm;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm;eauto | eapply mem_join_aeval_nrm;eauto| auto ].
Qed.


Lemma mem_join_aeval_err_rev : forall a l g m1 m2 m3,
  mem_join m1 m2 m3 ->
  (aeval a).(err) (mk_lstate l g m3)  -> 
  (aeval a).(err) (mk_lstate l g m1).
Proof.
  induction a;simpl;sets_unfold; intros.
  - auto.
  - auto.
  - auto.
  - auto.
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm_rev;eauto | eapply mem_join_aeval_nrm_rev;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm_rev;eauto | eapply mem_join_aeval_nrm_rev;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm_rev;eauto | eapply mem_join_aeval_nrm_rev;eauto| auto ].
  - my_destruct H0.
    + left. left. eapply IHa1;eauto.
    + left. right. eapply IHa2;eauto.
    + right. 
      unfold arith_sem_err in *.
      my_destruct H0.
      exists v,v0.
      splits;[ eapply mem_join_aeval_nrm_rev;eauto | eapply mem_join_aeval_nrm_rev;eauto| auto ].
Qed.

Lemma aeval_nrm_eq : forall e st v1 v2,
  (aeval e).(nrm) st v1 ->
  (aeval e).(nrm) st v2 ->
  v1 = v2.
Proof.
  induction e ; simpl ; sets_unfold ; intros.
  - destruct v1 , v2. my_destruct H;my_destruct H0. subst.  auto.
  - destruct v1 , v2. my_destruct H;my_destruct H0. subst.  auto.
  - rewrite H, H0. auto.
  - rewrite H, H0. auto.
  - unfold arith_sem_nrm in *.
    my_destruct H. my_destruct H0.
    specialize (IHe1 _ _ _ H H0).
    specialize (IHe2 _ _ _ H1 H3).
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H. my_destruct H0.
    specialize (IHe1 _ _ _ H H0).
    specialize (IHe2 _ _ _ H1 H3).
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H. my_destruct H0.
    specialize (IHe1 _ _ _ H H0).
    specialize (IHe2 _ _ _ H1 H3).
    subst.
    eapply arith_compute_determined;eauto.
  - unfold arith_sem_nrm in *.
    my_destruct H. my_destruct H0.
    specialize (IHe1 _ _ _ H H0).
    specialize (IHe2 _ _ _ H1 H3).
    subst.
    eapply arith_compute_determined;eauto.
Qed.
Arguments aeval_nrm_eq [e] [st] [v1] [v2].

Lemma aeval_nrm_nerr : forall e st v,
  (aeval e).(nrm) st v ->
  ~ (aeval e).(err) st.
Proof.
  induction e; simpl ; sets_unfold; intros ; try lia ; try tauto.
  - destruct v. my_destruct H. lia.  
  - intro. 
    hnf in H. destruct H as [i1 [i2  [?  [?  ?]]]].
    my_destruct H0.
    + revert H0. eapply IHe1. eauto.
    + revert H0. eapply IHe2. eauto.
    + unfold arith_sem_err in H0.
      my_destruct H0.
      pose proof aeval_nrm_eq H H0.
      pose proof aeval_nrm_eq H1 H3.
      subst.
      unfold arith_compute, arith_compute_err in *.
      destruct v0 ,v1.
      destruct v0, v1;try contradiction.
  - intro. 
    hnf in H. destruct H as [i1 [i2  [?  [?  ?]]]].
    my_destruct H0.
    + revert H0. eapply IHe1. eauto.
    + revert H0. eapply IHe2. eauto.
    + unfold arith_sem_err in H0.
      my_destruct H0.
      pose proof aeval_nrm_eq H H0.
      pose proof aeval_nrm_eq H1 H3.
      subst.
      unfold arith_compute, arith_compute_err in *.
      destruct v0 ,v1.
      destruct v0, v1;try contradiction.
  - intro. 
    hnf in H. destruct H as [i1 [i2  [?  [?  ?]]]].
    my_destruct H0.
    + revert H0. eapply IHe1. eauto.
    + revert H0. eapply IHe2. eauto.
    + unfold arith_sem_err in H0.
      my_destruct H0.
      pose proof aeval_nrm_eq H H0.
      pose proof aeval_nrm_eq H1 H3.
      subst.
      unfold arith_compute, arith_compute_err in *.
      destruct v0 ,v1.
      destruct v0, v1;try contradiction.
  - intro. 
    hnf in H. destruct H as [i1 [i2  [?  [?  ?]]]].
    my_destruct H0.
    + revert H0. eapply IHe1. eauto.
    + revert H0. eapply IHe2. eauto.
    + unfold arith_sem_err in H0.
      my_destruct H0.
      pose proof aeval_nrm_eq H H0.
      pose proof aeval_nrm_eq H1 H3.
      subst.
      unfold arith_compute, arith_compute_err in *.
      destruct v0 ,v1.
      destruct v0, v1;try contradiction.
      lia.
Qed.
Arguments aeval_nrm_nerr [e] [st] [v].


Lemma beval_excluded_middle : forall b st1,
  (exists i, (beval b).(nrm) st1 i) \/ 
  (beval b).(err) st1.
Proof.
  induction b;simpl; sets_unfold ; intros.
  - left. exists (1, vint). auto.  
  - left. eexists. eauto.
  - pose proof (aeval_excluded_middle a st1).
    pose proof (aeval_excluded_middle a0 st1).
    destruct H, H0 ; try tauto.
    destruct H, H0.
    destruct x as (? & [ | ]);
    destruct x0 as (? & [ | ]).
    + left.
      unfold eqneq_sem_nrm.
      do 4 eexists ; repeat split ; eauto.
    + right. right.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + left.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 4 eexists ; repeat split ; eauto; simpl;auto. 
  - pose proof (aeval_excluded_middle a st1).
    pose proof (aeval_excluded_middle a0 st1).
    destruct H, H0 ; try tauto.
    destruct H, H0.
    destruct x as (? & [ | ]);
    destruct x0 as (? & [ | ]).
    + left.
      unfold eqneq_sem_nrm.
      do 4 eexists ; repeat split ; eauto.
    + right. right.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + left.
      unfold eqneq_sem_err, eqneq_compute_err. 
      do 4 eexists ; repeat split ; eauto; simpl;auto. 
  - pose proof (aeval_excluded_middle a st1).
    pose proof (aeval_excluded_middle a0 st1).
    destruct H, H0 ; try tauto.
    destruct H, H0.
    destruct x as (? & [ | ]);
    destruct x0 as (? & [ | ]).
    + left.
      unfold cmp_sem_nrm.
      do 3 eexists ; repeat split ; eauto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto. 
  - pose proof (aeval_excluded_middle a st1).
    pose proof (aeval_excluded_middle a0 st1).
    destruct H, H0 ; try tauto.
    destruct H, H0.
    destruct x as (? & [ | ]);
    destruct x0 as (? & [ | ]).
    + left.
      unfold cmp_sem_nrm.
      do 3 eexists ; repeat split ; eauto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto.
    + right. right.
      unfold cmp_sem_err, cmp_compute_err. 
      do 2 eexists ; repeat split ; eauto; simpl;auto. 
  - unfold not_sem_nrm.
    destruct (IHb st1) ; try tauto.
    destruct H as [(? & [ | ]) ?].
    + 
      left. unfold not_compute_nrm.
      assert (z = 0 \/ z <> 0) as [? | ?] by lia.
      ++ do 3 eexists ; split ; eauto.
      ++ do 3 eexists ; split ; eauto.
    + right.  right.
      unfold not_sem_err.
      eexists. eauto.
  - unfold and_sem_nrm, and_sem_err, NonSC_and,     NonSC_compute_nrm, SC_and_compute_nrm.
    destruct (IHb1 st1) ; destruct (IHb2 st1) ; try tauto.
    + destruct H as [(? & [ | ]) ?].
      assert (z = 0 \/ z <> 0) as [? | ?] by lia.
      { left. eexists ; eexists ; split ; eauto. }
      { destruct H0 as [(? & [ | ]) ?].
      * left. assert (z0 = 0 \/ z0 <> 0) as [? | ?] by lia.
        ++ subst. exists (0, vint).
           exists z. split ; auto. right.
           split;auto.
           do 2 eexists.
           splits;eauto.
        ++ exists (1, vint).
           exists z. split ; auto. right.
           split;auto.
           do 2 eexists.
           splits;eauto.
      * right. right.  unfold and_sem_err2, NonSC_and. do 2 eexists. eauto.  }
      right. left. left. right.  unfold andor_sem_err. eexists. eauto.
    + destruct H as [(? & [ | ]) ?].
      { assert (z = 0 \/ z <> 0) as [? | ?] by lia.
      * left. eexists ; eexists ; split ; eauto.
      * right. left. right. 
        exists z. repeat split ; auto. }
      right. left. left. right.  unfold andor_sem_err. eexists. eauto.
  - unfold or_sem_nrm, or_sem_err, NonSC_or, NonSC_compute_nrm,   SC_or_compute_nrm.
    destruct (IHb1 st1); destruct (IHb2 st1) ; try tauto.
    + destruct H as [(? & [ | ]) ?].
      assert (z <> 0 \/ z = 0) as [? | ?] by lia.
      { left. eexists ; eexists ; split ; eauto. }
      { destruct H0 as [(? & [ | ]) ?].
      * left. assert (z0 <> 0 \/ z0 = 0) as [? | ?] by lia.
        ++ subst. exists (1, vint).
           exists 0. split ; auto. right.
           split;auto.
           do 2 eexists.
           splits;eauto.
        ++ exists (0, vint). subst.
           exists 0. split ; auto. right.
           split;auto.
           do 2 eexists.
           splits;eauto.
      * right. right.  unfold  or_sem_err2, NonSC_or. do 2 eexists. eauto.  }
      right. left. left. right.  unfold andor_sem_err. eexists. eauto.
    + destruct H as [(? & [ | ]) ?].
      { assert (z <> 0 \/ z = 0) as [? | ?] by lia.
      * left. eexists ; eexists ; split ; eauto.
      * right. left. right. 
        exists z. repeat split ; auto. }
      right. left. left. right.  unfold andor_sem_err. eexists. eauto.
Qed. 

Lemma mem_join_beval_nrm : forall b l g m1 m2 m3 i,
  mem_join m1 m2 m3 ->
  (beval b).(nrm) (mk_lstate l g m1) i -> 
  (beval b).(nrm) (mk_lstate l g m3) i.
Proof.
  induction b ; simpl in * ; sets_unfold ; intros ; auto.
  - unfold eqneq_sem_nrm, cmp_compute_nrm in *.
    my_destruct H0.
    eexists ; eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm ; eauto.
  - unfold eqneq_sem_nrm, cmp_compute_nrm in *.
    my_destruct H0.
    eexists ; eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm ; eauto.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0.
    eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm ; eauto.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0.
    eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm ; eauto.
  - unfold not_sem_nrm , not_compute_nrm in *.
    my_destruct H0.
    subst.
    do 2 eexists.
    split;eauto.
    do 2 eexists.
    split;eauto.
  - unfold and_sem_nrm , and_sem_nrm in *.
    my_destruct H0.
    subst.
    eexists.
    split;eauto.
    eexists.
    split;eauto.
    right.
    splits;eauto.
    do 2 eexists.
    splits;eauto.
  - unfold or_sem_nrm , or_sem_nrm in *.
    my_destruct H0.
    subst.
    eexists.
    split;eauto.
    eexists.
    split;eauto.
    right.
    splits;eauto.
    do 2 eexists.
    splits;eauto.
Qed.

Arguments mem_join_beval_nrm [b] [l] [g] [m1] [m2] [m3] [i].

Lemma mem_join_beval_nrm_rev : forall b l g m1 m2 m3 i,
  mem_join m1 m2 m3 ->
  (beval b).(nrm) (mk_lstate l g m3) i -> 
  (beval b).(nrm) (mk_lstate l g m1) i.
Proof.
  induction b ; simpl in * ; sets_unfold ; intros ; auto.
  - unfold eqneq_sem_nrm, cmp_compute_nrm in *.
    my_destruct H0.
    eexists ; eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm_rev ; eauto.
  - unfold eqneq_sem_nrm, cmp_compute_nrm in *.
    my_destruct H0.
    eexists ; eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm_rev ; eauto.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0.
    eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm_rev ; eauto.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0.
    eexists;  eexists ; repeat split ; eauto ; eapply mem_join_aeval_nrm_rev ; eauto.
  - unfold not_sem_nrm , not_compute_nrm in *.
    my_destruct H0;subst;
    do 2 eexists; splits;eauto.
  - unfold and_sem_nrm , and_sem_nrm in *.
    my_destruct H0;subst;
    do 2 eexists; splits;eauto.
    right.
    splits;eauto. do 2 eexists; splits;eauto.
  - unfold or_sem_nrm , or_sem_nrm in *.
    my_destruct H0;subst;
    do 2 eexists; splits;eauto.
    right.
    splits;eauto. do 2 eexists; splits;eauto.
Qed.

Arguments mem_join_beval_nrm_rev [b] [l] [g] [m1] [m2] [m3] [i].

Lemma mem_join_beval_nrm_eq : forall b l g m1 m2 m3 i i0,
  mem_join m1 m2 m3 ->
  (beval b).(nrm) (mk_lstate l g m3) i -> 
  (beval b).(nrm) (mk_lstate l g m1) i0 -> i0 = i.
Proof. 
  induction b ; simpl in * ; sets_unfold ; intros ; subst ; auto.
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0. my_destruct H1.
    pose proof (mem_join_aeval_nrm_eq H H0 H1).
    pose proof (mem_join_aeval_nrm_eq H H2 H4).
    inversion H6. inversion H7.
    subst. simpl. reflexivity.
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0. my_destruct H1.
    pose proof (mem_join_aeval_nrm_eq H H0 H1).
    pose proof (mem_join_aeval_nrm_eq H H2 H4).
    inversion H6. inversion H7.
    subst. simpl. reflexivity.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0. my_destruct H1.
    pose proof (mem_join_aeval_nrm_eq H H0 H1).
    pose proof (mem_join_aeval_nrm_eq H H2 H4).
    inversion H6. inversion H7.
    subst. simpl. reflexivity.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H0. my_destruct H1.
    pose proof (mem_join_aeval_nrm_eq H H0 H1).
    pose proof (mem_join_aeval_nrm_eq H H2 H4).
    inversion H6. inversion H7.
    subst. simpl. reflexivity.
  - unfold not_sem_nrm , not_compute_nrm in *.
    my_destruct H0; my_destruct H1;
    subst;auto.
    specialize (IHb _ _ _ _ _ _ _ H H0 H1). inversion IHb. lia. 
    specialize (IHb _ _ _ _ _ _ _ H H0 H1). inversion IHb. lia. 
  - unfold and_sem_nrm, SC_and_compute_nrm, NonSC_and, NonSC_compute_nrm in *.
    my_destruct H0; my_destruct H1;subst;auto;
    specialize (IHb1 _ _ _ _ _ _ _ H H0 H1);inversion IHb1; try lia.
    all: specialize (IHb2 _ _ _ _ _ _ _ H H3 H8) ; inversion IHb2; try lia.
  - unfold or_sem_nrm, SC_or_compute_nrm, NonSC_or, NonSC_compute_nrm in *.
    my_destruct H0; my_destruct H1;subst;auto;
    specialize (IHb1 _ _ _ _ _ _ _ H H0 H1);inversion IHb1; try lia.
    all: specialize (IHb2 _ _ _ _ _ _ _ H H3 H8) ; inversion IHb2; try lia.
Qed.

Arguments mem_join_beval_nrm_eq [b] [l] [g] [m1] [m2] [m3] [i] [i0].

Lemma mem_join_beval_err : forall b l g m1 m2 m3,
  mem_join m1 m2 m3 ->
  (beval b).(err) (mk_lstate l g m1)  -> 
  (beval b).(err) (mk_lstate l g m3).
Proof.
  induction b ; simpl ; sets_unfold ; intros ; auto.
  - my_destruct H0;
    try eapply mem_join_aeval_err in H0 ; eauto.
    right.
    unfold eqneq_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm in H0;eauto.
    eapply mem_join_aeval_nrm in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err in H0 ; eauto.
    right.
    unfold eqneq_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm in H0;eauto.
    eapply mem_join_aeval_nrm in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err in H0 ; eauto.
    right.
    unfold cmp_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm in H0;eauto.
    eapply mem_join_aeval_nrm in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err in H0 ; eauto.
    right.
    unfold cmp_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm in H0;eauto.
    eapply mem_join_aeval_nrm in H1;eauto.
  - my_destruct H0. left. eapply IHb ; eauto.
    right. unfold not_sem_err in *. my_destruct H0.
    eapply mem_join_beval_nrm in H0;eauto.
  - unfold and_sem_err, NonSC_and in *.
    my_destruct H0.
    + left. left. left. eapply IHb1 ; eauto.
    + left. left. right.
      unfold andor_sem_err in *.
      my_destruct H0. eapply mem_join_beval_nrm in H0;eauto.
    + left. right. 
      exists x ; split ; auto.
      eapply mem_join_beval_nrm; eauto.
      split ; auto.
      eapply IHb2 ; eauto.
    + right. unfold and_sem_err2 in *.
      my_destruct H0. eapply mem_join_beval_nrm in H0;eauto.
      do 2 eexists.
      splits;eauto.
      eapply mem_join_beval_nrm; eauto.
  - unfold or_sem_err, NonSC_or in *.
    my_destruct H0.
    + left. left. left. eapply IHb1 ; eauto.
    + left. left. right.
      unfold andor_sem_err in *.
      my_destruct H0. eapply mem_join_beval_nrm in H0;eauto.
    + left. right. 
      exists x ; split ; auto.
      eapply mem_join_beval_nrm; eauto.
      split ; auto.
      eapply IHb2 ; eauto.
    + right. unfold or_sem_err2 in *.
      my_destruct H0. eapply mem_join_beval_nrm in H0;eauto.
      do 2 eexists.
      splits;eauto.
      eapply mem_join_beval_nrm; eauto.
Qed.

Arguments mem_join_beval_err [b] [l] [g] [m1] [m2] [m3].

Lemma mem_join_beval_err_rev : forall b l g m1 m2 m3,
  mem_join m1 m2 m3 ->
  (beval b).(err) (mk_lstate l g m3)  -> 
  (beval b).(err) (mk_lstate l g m1).
Proof. 
  induction b ; simpl ; sets_unfold ; intros ; auto.
  - my_destruct H0;
    try eapply mem_join_aeval_err_rev in H0 ; eauto.
    right.
    unfold eqneq_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm_rev in H0;eauto.
    eapply mem_join_aeval_nrm_rev in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err_rev in H0 ; eauto.
    right.
    unfold eqneq_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm_rev in H0;eauto.
    eapply mem_join_aeval_nrm_rev  in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err_rev in H0 ; eauto.
    right.
    unfold cmp_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm_rev in H0;eauto.
    eapply mem_join_aeval_nrm_rev in H1;eauto.
  - my_destruct H0;
    try eapply mem_join_aeval_err_rev in H0 ; eauto.
    right.
    unfold cmp_sem_err in *.
    my_destruct H0.
    eapply mem_join_aeval_nrm_rev in H0;eauto.
    eapply mem_join_aeval_nrm_rev in H1;eauto.
  - my_destruct H0. left. eapply IHb ; eauto.
    right. unfold not_sem_err in *. my_destruct H0.
    eapply mem_join_beval_nrm_rev in H0;eauto.
  - unfold and_sem_err, NonSC_and in *.
    my_destruct H0.
    + left. left. left. eapply IHb1 ; eauto.
    + left. left. right.
      unfold andor_sem_err in *.
      my_destruct H0. eapply mem_join_beval_nrm_rev in H0;eauto.
    + left. right. 
      exists x ; split ; auto.
      eapply mem_join_beval_nrm_rev; eauto.
      split ; auto.
      eapply IHb2 ; eauto.
    + right. unfold and_sem_err2 in *.
      my_destruct H0. eapply mem_join_beval_nrm_rev in H0;eauto.
      do 2 eexists.
      splits;eauto.
      eapply mem_join_beval_nrm_rev ;eauto.
  - unfold or_sem_err, NonSC_or in *.
    my_destruct H0.
    + left. left. left. eapply IHb1 ; eauto.
    + left. left. right.
      unfold andor_sem_err in *.
      my_destruct H0. eapply mem_join_beval_nrm_rev in H0;eauto.
    + left. right. 
      exists x ; split ; auto.
      eapply mem_join_beval_nrm_rev; eauto.
      split ; auto.
      eapply IHb2 ; eauto.
    + right. unfold or_sem_err2 in *.
      my_destruct H0. eapply mem_join_beval_nrm_rev in H0;eauto.
      do 2 eexists.
      splits;eauto.
      eapply mem_join_beval_nrm_rev ;eauto.
Qed.

Arguments mem_join_beval_err_rev [b] [l] [g] [m1] [m2] [m3].

Lemma beval_nrm_eq : forall b st v1 v2,
  (beval b).(nrm) st v1 ->
  (beval b).(nrm) st v2 ->
  v1 = v2.
Proof.
  induction b ; simpl in * ; sets_unfold ; intros ; subst ; auto.
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H. my_destruct H0.
    pose proof (aeval_nrm_eq H H0).
    pose proof (aeval_nrm_eq H1 H3).
    inversion H5;inversion H6.
    subst. reflexivity.
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H. my_destruct H0.
    pose proof (aeval_nrm_eq H H0).
    pose proof (aeval_nrm_eq H1 H3).
    inversion H5;inversion H6.
    subst. reflexivity.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H. my_destruct H0.
    pose proof (aeval_nrm_eq H H0).
    pose proof (aeval_nrm_eq H1 H3).
    inversion H5;inversion H6.
    subst. reflexivity.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H. my_destruct H0.
    pose proof (aeval_nrm_eq H H0).
    pose proof (aeval_nrm_eq H1 H3).
    inversion H5;inversion H6.
    subst. reflexivity.
  - unfold not_sem_nrm , not_compute_nrm in *.
    my_destruct H; my_destruct H0;subst;eauto.
    all: specialize (IHb _ _ _ H H0); inversion IHb; subst;lia.
  - unfold and_sem_nrm, SC_and_compute_nrm, NonSC_and, NonSC_compute_nrm in *.
    my_destruct H; my_destruct H0;subst;eauto.
    all: specialize (IHb1 _ _ _ H H0); inversion IHb1; subst;try lia.
    all: specialize (IHb2 _ _ _ H2 H7); inversion IHb2; subst;try lia.
  - unfold or_sem_nrm, SC_or_compute_nrm, NonSC_or, NonSC_compute_nrm in *.
    my_destruct H; my_destruct H0;subst;eauto.
    all: specialize (IHb1 _ _ _ H H0); inversion IHb1; subst;try lia.
    all: specialize (IHb2 _ _ _ H2 H7); inversion IHb2; subst;try lia.
Qed.
Arguments beval_nrm_eq [b] [st] [v1] [v2].

Lemma beval_nrm_nerr : forall e st v,
  (beval e).(nrm) st v ->
  ~ (beval e).(err) st.
Proof. 
  induction e ; simpl in * ; sets_unfold ; intros ; auto.
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H.
    unfold not;intros.
    apply aeval_nrm_nerr in H as ?.
    apply aeval_nrm_nerr in H0 as ?.
    my_destruct H2; try tauto.
    unfold eqneq_sem_err, eqneq_compute_err in H2.
    my_destruct H2.
    pose proof aeval_nrm_eq H H2.
    pose proof aeval_nrm_eq H0 H5.
    subst.
    destruct x1;auto. 
  - unfold eqneq_sem_nrm , cmp_compute_nrm in *.
    my_destruct H.
    unfold not;intros.
    apply aeval_nrm_nerr in H as ?.
    apply aeval_nrm_nerr in H0 as ?.
    my_destruct H2; try tauto.
    unfold  eqneq_sem_err, eqneq_compute_err in H2.
    my_destruct H2.
    pose proof aeval_nrm_eq H H2.
    pose proof aeval_nrm_eq H0 H5.
    subst. 
    destruct x1;auto. 
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H.
    unfold not;intros.
    apply aeval_nrm_nerr in H as ?.
    apply aeval_nrm_nerr in H0 as ?.
    my_destruct H2; try tauto.
    unfold cmp_sem_err, cmp_compute_err in H2.
    my_destruct H2.
    pose proof aeval_nrm_eq H H2.
    pose proof aeval_nrm_eq H0 H5.
    subst. 
    tauto.
  - unfold cmp_sem_nrm , cmp_compute_nrm in *.
    my_destruct H.
    unfold not;intros.
    apply aeval_nrm_nerr in H as ?.
    apply aeval_nrm_nerr in H0 as ?.
    my_destruct H2; try tauto.
    unfold cmp_sem_err, cmp_compute_err in H2.
    my_destruct H2.
    pose proof aeval_nrm_eq H H2.
    pose proof aeval_nrm_eq H0 H5.
    subst. 
    tauto.
  - unfold not_sem_nrm, not_compute_nrm in *.
    destruct H as [? [? [? ?]]].
    unfold not;intros.
    destruct H1.
    eapply IHe ; eauto.
    unfold not_sem_err in H1. my_destruct H1.
    pose proof beval_nrm_eq  H H1.
    inversion H2.
  - unfold and_sem_err, and_sem_nrm, SC_and_compute_nrm, NonSC_and, NonSC_compute_nrm in *.
    my_destruct H; apply and_not_or ; split ; eauto ; intro; my_destruct H3;subst.
    + eapply IHe1;eauto.
    + unfold andor_sem_err in H3. my_destruct H3.
      pose proof beval_nrm_eq H H3. inversion H0.
    + pose proof beval_nrm_eq H H3. inversion H0. lia.
    + unfold and_sem_err2,NonSC_and in H3. my_destruct H3.
      pose proof beval_nrm_eq H H3. inversion H2. lia.
    + my_destruct H5. 
      * eapply IHe1;eauto.
      * unfold andor_sem_err in H5. my_destruct H5. 
        pose proof beval_nrm_eq H H5. inversion H2.
      * eapply IHe2;eauto. 
    + unfold and_sem_err2,NonSC_and in H5. my_destruct H5.
      pose proof beval_nrm_eq H1 H3. inversion H4. 
    +  my_destruct H5. 
      * eapply IHe1;eauto.
      * unfold andor_sem_err in H5. my_destruct H5. 
        pose proof beval_nrm_eq H H5. inversion H3.
      * eapply IHe2;eauto. 
    + unfold and_sem_err2,NonSC_and in H5. my_destruct H5.
      pose proof beval_nrm_eq H1 H4. inversion H6.
  - unfold or_sem_err, or_sem_nrm, SC_or_compute_nrm, NonSC_or, NonSC_compute_nrm in *.
    my_destruct H; apply and_not_or ; split ; eauto ; intro; my_destruct H3;subst.
    + eapply IHe1;eauto.
    + unfold andor_sem_err in H3. my_destruct H3.
      pose proof beval_nrm_eq H H3. inversion H1.
    + pose proof beval_nrm_eq H H3. inversion H1. lia.
    + unfold or_sem_err2,NonSC_or in H3. my_destruct H3.
      pose proof beval_nrm_eq H H3. inversion H4. lia.
    + my_destruct H5. 
      * eapply IHe1;eauto.
      * unfold andor_sem_err in H5. my_destruct H5. 
        pose proof beval_nrm_eq H H5. inversion H0.
      * eapply IHe2;eauto. 
    + unfold or_sem_err2,NonSC_or in H5. my_destruct H5.
      pose proof beval_nrm_eq H1 H2. inversion H3. 
    +  my_destruct H5. 
      * eapply IHe1;eauto.
      * unfold andor_sem_err in H5. my_destruct H5. 
        pose proof beval_nrm_eq H H5. inversion H0.
      * eapply IHe2;eauto. 
    + unfold or_sem_err2,NonSC_or in H5. my_destruct H5.
      pose proof beval_nrm_eq H1 H3. inversion H4. 
Qed. 
Arguments beval_nrm_nerr [e] [st] [v].
