Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.

Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Local Open Scope sac.

Definition store_map {A B: Type} (P: A -> B -> Assertion) (m: A -> option B): Assertion :=
  EX l: list A,
    [| forall a, In a l <-> exists b, m a = Some b |] &&
    [| NoDup l |] &&
    iter_sepcon
      (map (fun a => match m a with Some b => P a b | None => emp end) l).

Definition store_map_missing_i {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (i:A): Assertion :=
  EX l: list A,
    [| forall a, In a l <-> (exists b, m a = Some b ) /\ a <> i |] &&
    [| NoDup l |] &&
    iter_sepcon
      (map (fun a => match m a with Some b => P a b | None => emp end) l).

Lemma store_map_split:
  forall {A B: Type} (P: A -> B -> Assertion) (a: A) (b: B) (m: A -> option B),
    m a = Some b ->
    store_map P m |-- store_map_missing_i P m a ** P a b.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  assert (In a l). {
    apply H0.
    eauto.
  }
  apply in_split in H2.
  destruct H2 as [l1 [l2 ?] ].
  Exists (l1 ++ l2).
  entailer!.
  + subst l.
    change (l1 ++ a :: l2) with (l1 ++ (a :: nil) ++ l2).
    rewrite !map_app.
    rewrite !derivable1_sepcon_iter_sepcon2.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    entailer!.
    rewrite derivable1_iter_sepcon_l.
    simpl.
    rewrite H.
    entailer!.
  + subst l.
    apply NoDup_remove in H1.
    tauto.
  + intros.
    subst l.
    apply NoDup_remove in H1.
    specialize (H0 a0).
    rewrite in_app_iff in *.
    simpl in H0.
    rewrite <- H0.
    assert (a = a0 <-> a0 = a) by (split; intros; congruence).
    assert (a = a0 -> ~ (In a0 l1 \/ In a0 l2)) by (intros; subst; tauto).
    tauto.
Qed.

Lemma store_map_merge:
  forall {A B: Type} (P: A -> B -> Assertion) (a: A) (b: B) (m: A -> option B),
    m a = Some b ->
    store_map_missing_i P m a ** P a b |-- store_map P m.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists ((a :: nil) ++ l).
  entailer!.
  + rewrite !map_app.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    entailer!.
    rewrite <- derivable1_iter_sepcon_r.
    simpl.
    rewrite H.
    entailer!.
  + simpl; constructor.
    - rewrite H0.
      tauto.
    - tauto.
  + intros.
    simpl.
    rewrite H0.
    assert (a = a0 <-> a0 = a) by (split; intros; congruence).
    assert (a = a0 -> exists b0, m a0 = Some b0) by (intros; subst; eauto).
    tauto.
Qed.

Lemma store_map_missing_equiv_store_map : 
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (a: A),
    m a = None ->
    store_map_missing_i P m a |-- store_map P m.
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists l.
  entailer!.
  intros.
  rewrite H0.
  split;  intros ; destruct H2; auto.
  split.
  - exists x. auto.
  - intro. subst. rewrite H in H2. inversion H2.  
Qed.

Lemma store_map_equiv_store_map_missing : 
  forall {A B: Type} (P: A -> B -> Assertion) (m: A -> option B) (a: A),
    m a = None ->
    store_map P m |-- store_map_missing_i P m a .
Proof.
  intros.
  unfold store_map, store_map_missing_i.
  Intros l.
  Exists l.
  entailer!.
  intros.
  rewrite H0.
  split;  intros ; destruct H2; auto.
  split.
  - exists x. auto.
  - intro. subst. rewrite H in H2. inversion H2.  
Qed.

Lemma store_map_equiv : 
  forall {A B: Type} (P: A -> B -> Assertion) (m m1: A -> option B),
    (forall a, m a = m1 a) ->
    store_map P m --||-- store_map P m1.
Proof.
  intros.
  unfold store_map.
  split; Intros l ; Exists l; entailer!.
  - assert (map (fun a : A => match m a with
                               | Some b => P a b
                               | None => emp
                               end) l = 
            map (fun a : A => match m1 a with
                               | Some b => P a b
                               | None => emp
                               end) l). {
      apply map_ext_in.
      intros.
      rewrite H.
      auto.
    }
    rewrite H2. entailer!.
  - intros. rewrite H0. rewrite H. reflexivity.
  - assert (map (fun a : A => match m a with
                                | Some b => P a b
                                | None => emp
                              end) l = 
            map (fun a : A => match m1 a with
                                | Some b => P a b
                                | None => emp
                              end) l). {
        apply map_ext_in.
        intros.
        rewrite H.
        auto.
    }
    rewrite H2. entailer!.
  - intros. rewrite H0. rewrite H. reflexivity.
Qed.

Lemma store_map_missing_i_equiv : 
  forall {A B: Type} (P: A -> B -> Assertion) (m m1: A -> option B) (i : A),
    (forall a, (a <> i) -> m a = m1 a) ->
    store_map_missing_i P m i --||-- store_map_missing_i P m1 i.
Proof.
  intros.
  unfold store_map_missing_i.
  split; Intros l ; Exists l; entailer!.
  - assert (map (fun a : A => match m a with
                               | Some b => P a b
                               | None => emp
                               end) l = 
            map (fun a : A => match m1 a with
                               | Some b => P a b
                               | None => emp
                               end) l). {
      apply map_ext_in.
      intros. rewrite H0 in H2.
      rewrite H; 
      auto.
      apply H2.
    }
    rewrite H2. entailer!.
  - intros. split; intros.
    + apply H0 in H2. rewrite H in H2 ; auto. apply H2.
    + apply H0. rewrite H ; auto. apply H2.
  - assert (map (fun a : A => match m a with
                                | Some b => P a b
                                | None => emp
                              end) l = 
            map (fun a : A => match m1 a with
                                | Some b => P a b
                                | None => emp
                              end) l). {
        apply map_ext_in.
        intros. rewrite H0 in H2.
        rewrite H; 
        auto.
        apply H2.
    }
    rewrite H2. entailer!.
  - intros. split; intros.
    + apply H0 in H2. rewrite H; auto. apply H2.
    + apply H0. rewrite H in H2; auto. apply H2.
Qed.

Definition dllseg {A: Type} (storeA: addr -> A -> Assertion) (x px y py: addr) (l: list (DL_Node A)): Assertion :=
  (fix dllseg x px y py l :=
     match l with
     | nil     => [| x = y /\ px = py |] && emp
     | a :: l0 => EX z: addr,
                    [| x = a.(ptr) |] &&
                    storeA x a.(dll_data) **
                    &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px ** 
                    &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
                    dllseg z x y py l0
     end) x px y py l.

Definition dllseg_shift {A: Type} (storeA: addr -> A -> Assertion) (px py: addr) (l: list (DL_Node A)): Assertion :=
  (fix dllseg_shift px py l :=
     match l with
     | nil     => [| px = py |] && emp
     | a :: l0 => EX x: addr,
                    [| x = a.(ptr) |] &&
                    storeA x a.(dll_data) **
                    &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px ** 
                    &(px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x **
                    dllseg_shift x py l0
     end) px py l.

Definition dllseg_shift_rev {A: Type} (storeA: addr -> A -> Assertion) (x y : addr) (l: list (DL_Node A)): Assertion :=
  (fix dllseg_shift_rev x y l :=
    match l with
    | nil     => [| x = y |] && emp
    | a :: l0 => EX z: addr,
                    [| x = a.(ptr) |] &&
                    storeA x a.(dll_data) **
                    &(z # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x ** 
                    &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
                    dllseg_shift_rev z y l0
    end) x y l.

Definition store_dll {A: Type} (storeA: addr -> A -> Assertion) (x: addr) (l: list (DL_Node A)): Assertion :=
  EX h pt: addr,
    &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> pt ** 
    &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> h **
    dllseg storeA h x x pt l.

Definition occupy_dll_node (x: addr): Assertion :=
  (EX __, &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> __) ** 
  (EX __, &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> __).

Theorem dllseg_concat:
  forall
    {A : Type} (storeA : addr -> A -> Assertion)
    (x px y py z pz: addr) (l1 l2: list (DL_Node A)),
  dllseg storeA x px y py l1 ** dllseg storeA y py z pz l2 |--
  dllseg storeA x px z pz (l1 ++ l2).
Proof.
  intros.
  revert x px y py z pz l2. 
  induction l1 ; intros.
  + simpl.
    entailer!.
    destruct H. subst. reflexivity.
  + simpl.
    Intros x0.
    Exists x0. entailer!.
Qed.

Theorem dllseg_split:
  forall 
    {A : Type} (storeA : addr -> A -> Assertion)
    (x px z pz: addr) (l1 l2: list (DL_Node A)),
  dllseg storeA x px z pz (l1 ++ l2) |--
  EX y py,dllseg storeA x px y py l1 ** dllseg storeA y py z pz l2.
Proof.
  intros.
  revert x px.
  induction l1 ; intros.
  + simpl.
    Exists x px.
    entailer!.
  + simpl.
    Intros z0.
    sep_apply IHl1.
    Intros y y0.
    Exists y y0 z0.
    entailer!.
Qed.

Theorem dllseg_shift_split:
  forall 
    {A : Type} (storeA : addr -> A -> Assertion)
    (px pz: addr) (l1 l2: list (DL_Node A)),
  dllseg_shift storeA px pz (l1 ++ l2) |--
  EX py ,dllseg_shift storeA px py l1 ** dllseg_shift storeA py pz l2.
Proof.
  intros.
  revert px.
  induction l1;intros.
  + simpl.
    Exists px;entailer!.
  + simpl.
    Intros x.
    sep_apply IHl1.
    Intros py.
    Exists py x.
    entailer!. 
Qed.

Theorem dllseg_shift_concat: 
forall 
    {A : Type} (storeA : addr -> A -> Assertion)
    (px py pz: addr) (l1 l2: list (DL_Node A)),
    dllseg_shift storeA px py l1 ** dllseg_shift storeA py pz l2
    |--
    dllseg_shift storeA px pz (l1 ++ l2).
Proof.
  intros.
  revert px.
  induction l1;intros.
  + simpl.
    entailer!;destruct H;subst;reflexivity.
  + simpl.
    Intros x.
    Exists x.
    sep_apply (IHl1).
    entailer!.
Qed.


Theorem dllseg_shift_rev_split:
forall 
    {A : Type} (storeA : addr -> A -> Assertion)
    (x z: addr) (l1 l2: list (DL_Node A)),
  dllseg_shift_rev storeA x z (l1 ++ l2) |--
  EX y,dllseg_shift_rev storeA x y l1 ** dllseg_shift_rev storeA y z l2.
Proof.
  intros.
  revert x.
  induction l1;intros.
  + Exists x;simpl.
    entailer!.
  + simpl.
    Intros z0.
    sep_apply (IHl1 z0).
    Intros y;Exists y z0.
    entailer!.
Qed.

Theorem dllseg_shift_rev_concat: 
forall 
    {A : Type} (storeA : addr -> A -> Assertion)
    (x y z: addr) (l1 l2: list (DL_Node A)),
    dllseg_shift_rev storeA x y l1 ** dllseg_shift_rev storeA y z l2 |--
    dllseg_shift_rev storeA x z (l1 ++ l2).
Proof.
  intros.
  revert x.
  induction l1;intros.
  + simpl.
    entailer!.
    subst;reflexivity.
  + simpl.
    Intros z0.
    Exists z0.
    entailer!.
Qed.


Module ListAddSpec_LowLevel.

Definition Pre
            {A: Type} (storeA: addr -> A -> Assertion)
            (x y u: addr) (a: A): Assertion :=
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> __) ** 
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> __) **
  storeA u a **
  &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x.

Definition Post
            {A: Type} (storeA: addr -> A -> Assertion)
            (x y u: addr) (a: A): Assertion :=
  &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> u **
  dllseg_shift storeA x u ({| DLL.data := a; DLL.ptr := u |} :: nil).

End ListAddSpec_LowLevel.

Module ListAddSpec_ForStoreDLL.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node A)) (a: A): Assertion :=
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> __) ** 
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> __) **
  storeA u a **
  store_dll storeA x l.

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node A)) (a: A): Assertion :=
  store_dll storeA x ({| DLL.data := a; DLL.ptr := u |} :: l).

End ListAddSpec_ForStoreDLL.

Module ListDelSpec_ForStoreDLL.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  store_dll storeA x (l1 ++ {| DLL.data := a; DLL.ptr := u |} :: l2).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  storeA u a **
  &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> 0 **
  &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> 0 **
  store_dll storeA x (l1++l2).

End ListDelSpec_ForStoreDLL.

Module ListTailAddSpec_ForStoreDLL.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node A)) (a: A): Assertion :=
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> __) ** 
  (EX __, &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> __) **
  storeA u a **
  store_dll storeA x l.

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node A)) (a: A): Assertion :=
  store_dll storeA x (l ++ {| DLL.data := a; DLL.ptr := u |} :: nil).

End ListTailAddSpec_ForStoreDLL.

Module ListDelInitSpec_ForStoreDLL.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  store_dll storeA x (l1 ++ {| DLL.data := a; DLL.ptr := u |} :: l2).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node A)) (a: A) (l2: list (DL_Node A)): Assertion :=
  storeA u a **
  &(u # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> u **
  &(u # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> u **
  store_dll storeA x (l1 ++ l2).

End ListDelInitSpec_ForStoreDLL.

Module ListInitSpec_ForStoreDLL.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr): Assertion :=
  (EX __, &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> __) ** 
  (EX __, &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> __).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr): Assertion :=
  store_dll storeA x nil.

End ListInitSpec_ForStoreDLL.

Module Emptycheck.

Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr)(l: list (DL_Node A)): Assertion :=
  store_dll storeA x l.

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr) (l: list (DL_Node A))(__return: Z): Assertion :=
  [| (l = nil /\ __return = 1) \/ (l <> nil /\ __return = 0) |] **
  store_dll storeA x l.

End Emptycheck.

Definition store_pend_list_dll (sg: StableGlobVars) (x: addr) (l: list TaskID): Assertion :=
  EX l0: list (DL_Node TaskID),
    [| map DLL.data l0 = l |] &&
    store_dll
      (fun p (taskID: TaskID) =>
         [| p = &((sg.(g_taskCBArray) # "LosTaskCB" + taskID) ->ₛ "pendList") |] 
         && emp)
      x l0.

Lemma dllseg_to_dllseg_shift:
forall {A: Type} (storeA: addr -> A -> Assertion) (x px y py: addr) (l: list (DL_Node A)),
  dllseg storeA x px y py l **
  &(px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x 
  |--
  &(py # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  dllseg_shift storeA px py l.
Proof.
  intros.
  revert x px.
  induction l;intros.
  + simpl;entailer!;destruct H;subst;reflexivity.
  + simpl.
    Intros z.
    subst.
    sep_apply (IHl z a.(ptr)).
    Exists a.(ptr).
    entailer!.
Qed.

Lemma dllseg_to_dllseg_shift_rev:
forall {A: Type} (storeA: addr -> A -> Assertion) (x px y py: addr) (l: list (DL_Node A)),
  dllseg storeA x px y py l **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py
  |--
  dllseg_shift_rev storeA x y l **
  &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px.
Proof.
  intros.
  revert x px.
  induction l;intros.
  + simpl.
    entailer!.
    destruct H.
    subst.
    reflexivity.
  + simpl.
    Intros z.
    subst.
    sep_apply (IHl).
    Exists z.
    entailer!.
Qed.

Lemma dllseg_shift_to_dllseg:
forall {A: Type} (storeA: addr -> A -> Assertion) (px py y: addr) (l: list (DL_Node A)),
  &(py # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  dllseg_shift storeA px py l
  |--
  EX x,
  dllseg storeA x px y py l **
  &(px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x 
.
Proof.
  intros.
  revert px.
  induction l;intros;simpl.
  + Exists y.
    entailer!.
    subst;reflexivity.
  + Intros x.
    sep_apply IHl.
    Intros z;Exists x z.
    entailer!.
Qed.

Lemma dllseg_shift_rev_to_dllseg:
forall {A: Type} (storeA: addr -> A -> Assertion) (x px y: addr) (l: list (DL_Node A)),
  dllseg_shift_rev storeA x y l **
  &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px
  |--
  EX py,
  dllseg storeA x px y py l **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py.
Proof.
  intros.
  revert x px.
  induction l;intros;simpl.
  + Exists px.
    entailer!.
    subst;reflexivity.
  + Intros z.
    sep_apply (IHl z x).
    Intros py.
    Exists py z.
    entailer!.
Qed.

Lemma dllseg_shift_to_dllseg_shift_rev:
forall {A: Type} (storeA: addr -> A -> Assertion) (px y py: addr) (l: list (DL_Node A)),
  dllseg_shift storeA px py l **
  &(py # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py 
  |--
  EX x,
  dllseg_shift_rev storeA x y l **
  &(px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x **
  &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px.
Proof.
  intros.
  revert px.
  induction l;intros;simpl.
  + entailer!.
    Exists y;subst;entailer!;reflexivity.
  + Intros x.
    sep_apply IHl.
    Intros x0.
    Exists x x0.
    entailer!.
Qed.


Lemma store_dll_shift_unfold: 
forall {A: Type} (storeA: addr -> A -> Assertion)(x: addr) (l: list (DL_Node A)),
  store_dll storeA x l |--
  EX px: addr,
  &(px # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x **
  &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px **
  dllseg_shift storeA x px l .
Proof.
  intros.
  unfold store_dll.
  Intros h pt.
  sep_apply (dllseg_to_dllseg_shift storeA h x x pt l).
  Exists pt.
  entailer!.
Qed.

Lemma store_dll_shift_rev_unfold:
forall {A: Type} (storeA: addr -> A -> Assertion)(x: addr) (l: list (DL_Node A)),
  store_dll storeA x l |--
  EX xn: addr ,
  &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> xn **
  &(xn # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x **
  dllseg_shift_rev storeA xn x l.
Proof.
  intros.
  unfold store_dll.
  Intros h pt.
  sep_apply (dllseg_to_dllseg_shift_rev storeA h x x pt l).
  Exists h.
  entailer!.
Qed.

Lemma dllseg_head_insert:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (py y z x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z |--
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l).
Proof.
    intros.
    simpl.
    Exists z.
    entailer!.
Qed.