Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Local Open Scope sac_scope.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.

Axiom sizeof_OsMemNodeHead : sizeof("OsMemNodeHead") = 16.
Axiom sizeof_OsMemFreeNodeHead : sizeof("OsMemFreeNodeHead") = 32.
Axiom sizeof_OsMemUsedNodeHead : sizeof("OsMemUsedNodeHead") = 16.

Axiom store_undef_OsMemFreeNodeHead : forall p,
  store_undef_array (fun p i => (p + i * sizeof(CHAR)) # Char |->_)
                    p sizeof("OsMemFreeNodeHead") --||--
  let header := &(p # "OsMemFreeNodeHead" ->ₛ "header") in
  &(header # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") # Ptr |->_ **
  &(header # "OsMemNodeHead" ->ₛ "sizeAndFlag") # UInt |->_ **
  &(p # "OsMemFreeNodeHead" ->ₛ "prev") # Ptr |->_ **
  &(p # "OsMemFreeNodeHead" ->ₛ "next") # Ptr |->_.

Axiom OsMemFreeNodeHead_header_offset : forall p,
  &(p # "OsMemFreeNodeHead" ->ₛ "header") = p.

Lemma OsMemFreeNodeHead_deinit : forall p v1 v2,
  &(p # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") # Ptr |-> v1 **
  &(p # "OsMemNodeHead" ->ₛ "sizeAndFlag") # UInt |-> v2 **
  &(p # "OsMemFreeNodeHead" ->ₛ "prev") # Ptr |->_ **
  &(p # "OsMemFreeNodeHead" ->ₛ "next") # Ptr |->_ |--
  store_undef_array (fun p i => (p + i * sizeof(CHAR)) # Char |->_)
                    p sizeof("OsMemFreeNodeHead").
Proof.
  intros.
  rewrite -> store_undef_OsMemFreeNodeHead.
  rewrite -> OsMemFreeNodeHead_header_offset.
  sep_apply (poly_store_poly_undef_store &(p # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") FET_ptr).
  sep_apply (poly_store_poly_undef_store &(p # "OsMemNodeHead" ->ₛ "sizeAndFlag") FET_uint).
  entailer!.
Qed.

Definition addr_eq_dec : forall (x y : addr), {x = y} + {x <> y} := Z.eq_dec.

Definition UINTPTR_MAX : Z := UINT_MAX.

Definition OS_MEM_NODE_USED_FLAG_BIT : Z := 31.
Definition OS_MEM_NODE_ALIGNED_FLAG_BIT : Z := 30.
Definition OS_MEM_NODE_LEAK_FLAG_BIT : Z := 29.
Definition OS_MEM_NODE_LAST_FLAG_BIT : Z := 28.
Definition OS_MEM_NODE_USED_FLAG : Z := Z.setbit 0 OS_MEM_NODE_USED_FLAG_BIT.
Definition OS_MEM_NODE_ALIGNED_FLAG : Z := Z.setbit 0 OS_MEM_NODE_ALIGNED_FLAG_BIT.
Definition OS_MEM_NODE_LEAK_FLAG : Z := 0.
Definition OS_MEM_NODE_LAST_FLAG : Z := 0.

Definition OS_MEM_NODE_SIZE_BITS : Z := 27.
Definition OS_MEM_NODE_MAX_SIZE : Z := 2 ^ OS_MEM_NODE_SIZE_BITS - 1.
Definition OS_MEM_NODE_HEAD_SIZE : Z := sizeof("OsMemUsedNodeHead").
Definition OS_MEM_MIN_LEFT_SIZE : Z := sizeof("OsMemFreeNodeHead").

Inductive MemNodeFlag : Type :=
| MemNodeFreeFlag : MemNodeFlag
| MemNodeUsedFlag : (* aligned *) bool -> MemNodeFlag
.
Record MemNode : Type := {
  mem_node_size : Z;
  mem_node_flag : MemNodeFlag;
}.

Definition mem_node_sizeAndFlag (node : MemNode) : Z :=
  match node.(mem_node_flag) with
  | MemNodeFreeFlag         => node.(mem_node_size)
  | MemNodeUsedFlag aligned =>
      let set_used := Z.setbit node.(mem_node_size) OS_MEM_NODE_USED_FLAG_BIT in
      if aligned then Z.setbit set_used OS_MEM_NODE_ALIGNED_FLAG_BIT else set_used
  end.
Notation "node '.(mem_node_sizeAndFlag)'" := (mem_node_sizeAndFlag node) (at level 0).

Definition update_mem_node_size (node : MemNode) (size : Z) : MemNode := {|
  mem_node_size := size;
  mem_node_flag := node.(mem_node_flag);
|}.
Notation "node '.(update_mem_node_size)'" := (update_mem_node_size node) (at level 0).

Definition update_mem_node_flag (node : MemNode) (flag : MemNodeFlag) : MemNode := {|
  mem_node_size := node.(mem_node_size);
  mem_node_flag := flag;
|}.
Notation "node '.(update_mem_node_flag)'" := (update_mem_node_flag node) (at level 0).

Definition mem_node_next (p : addr) (node : MemNode) : addr :=
  p + node.(mem_node_size).

Lemma mem_node_size_impl : forall node,
  0 <= node.(mem_node_size) <= OS_MEM_NODE_MAX_SIZE ->
  node.(mem_node_size) = Z.land node.(mem_node_sizeAndFlag)
                                (unsigned_last_nbits (Z.lnot (Z.lor (Z.lor (Z.lor OS_MEM_NODE_USED_FLAG
                                                             OS_MEM_NODE_ALIGNED_FLAG)
                                               OS_MEM_NODE_LEAK_FLAG)
                                        OS_MEM_NODE_LAST_FLAG)) 32).
Proof.
  intros.
  enough (node.(mem_node_size) = Z.land node.(mem_node_size)
                                        (unsigned_last_nbits (Z.lnot (Z.lor OS_MEM_NODE_USED_FLAG
                                                       OS_MEM_NODE_ALIGNED_FLAG)) 32)). {
    repeat rewrite -> Z.lor_0_r.
    rewrite -> Z.lnot_lor in *.
    unfold unsigned_last_nbits in *.
    rewrite <- Z.land_ones in * ; try lia.
    rewrite -> Z.land_assoc in *.
    unfold mem_node_sizeAndFlag.
    repeat rewrite -> Z.setbit_spec'.
    destruct mem_node_flag;
    [ |destruct b];
    repeat rewrite -> Z.land_lor_distr_l;
    simpl;
    repeat rewrite -> Z.lor_0_r;
    assumption.
  }
  apply Z.bits_inj_iff'.
  intros.
  unfold unsigned_last_nbits. rewrite <- Z.land_ones ; try lia.
  rewrite -> !Z.land_spec.
  rewrite -> Z.lnot_spec by assumption.
  rewrite Z.testbit_ones ; try lia.
  rewrite -> Z.lor_spec.
  unfold OS_MEM_NODE_USED_FLAG,
         OS_MEM_NODE_ALIGNED_FLAG.
  repeat rewrite -> Z.setbit_eqb
                 by (unfold OS_MEM_NODE_USED_FLAG_BIT in *;
                     unfold OS_MEM_NODE_ALIGNED_FLAG_BIT in *;
                     lia).
  rewrite -> Z.bits_0.
  repeat rewrite -> orb_false_r.
  destruct (Z_le_gt_dec n OS_MEM_NODE_SIZE_BITS);
  destruct (Z.eqb_spec OS_MEM_NODE_USED_FLAG_BIT n);
  destruct (Z.eqb_spec OS_MEM_NODE_ALIGNED_FLAG_BIT n);
  try (unfold OS_MEM_NODE_SIZE_BITS in *;
       unfold OS_MEM_NODE_USED_FLAG_BIT in *;
       unfold OS_MEM_NODE_ALIGNED_FLAG_BIT in *;
       lia);
  simpl;
  try (rewrite -> andb_true_r; reflexivity); try 
  rewrite -> andb_false_r; try (
  rewrite Z.bits_above_log2; try lia;
  apply Z.le_lt_trans with OS_MEM_NODE_SIZE_BITS; try lia;
  apply Z.le_trans with (Z.log2 OS_MEM_NODE_MAX_SIZE);
  try (apply Z.log2_le_mono; lia);
  simpl;
  unfold OS_MEM_NODE_SIZE_BITS;
  lia).
  assert (( (0 <=? n) && (n <? 32))%bool = true).
    unfold OS_MEM_NODE_SIZE_BITS in *. lia.
    rewrite H1. rewrite andb_true_r. reflexivity.
Qed.

Lemma mem_node_used_flag_impl : forall node,
  0 <= node.(mem_node_size) <= OS_MEM_NODE_MAX_SIZE ->
  node.(mem_node_flag) = MemNodeFreeFlag <->
  Z.land node.(mem_node_sizeAndFlag) OS_MEM_NODE_USED_FLAG = 0.
Proof.
  split;
  unfold mem_node_sizeAndFlag;
  intros.
  - rewrite -> H0.
    apply Z.bits_inj_0.
    intros.
    rewrite -> Z.land_spec.
    unfold OS_MEM_NODE_USED_FLAG.
    rewrite -> Z.setbit_eqb by (unfold OS_MEM_NODE_USED_FLAG_BIT; lia).
    rewrite -> Z.bits_0.
    rewrite -> orb_false_r.
    destruct (Z.eqb_spec OS_MEM_NODE_USED_FLAG_BIT n).
    + rewrite -> Z.bits_above_log2; try lia.
      apply Z.le_lt_trans with OS_MEM_NODE_SIZE_BITS;
      [ |unfold OS_MEM_NODE_SIZE_BITS, OS_MEM_NODE_USED_FLAG_BIT in *; lia].
      apply Z.le_trans with (Z.log2 OS_MEM_NODE_MAX_SIZE);
      [apply Z.log2_le_mono; lia| ].
      simpl.
      unfold OS_MEM_NODE_SIZE_BITS.
      lia.
    + apply andb_false_r.
  - destruct mem_node_flag; auto.
    destruct b;
    repeat rewrite -> Z.setbit_spec' in H0;
    repeat rewrite -> Z.land_lor_distr_l in H0;
    simpl in H0;
    try rewrite -> Z.lor_0_r in H0;
    apply Z.lor_eq_0_iff in H0;
    lia.
Qed.

Definition store_mem_block (p : addr) (node : MemNode) : Assertion :=
  match node.(mem_node_flag) with
  | MemNodeFreeFlag   => [| node.(mem_node_size) >= sizeof("OsMemFreeNodeHead") |] &&
                         store_undef_array (fun p i => (p + i * sizeof(CHAR)) # Char |->_)
                                           (p + sizeof("OsMemFreeNodeHead"))
                                           (node.(mem_node_size) - sizeof("OsMemFreeNodeHead"))
  | MemNodeUsedFlag _ => [| node.(mem_node_size) = 0 \/
                            node.(mem_node_size) >= sizeof("OsMemFreeNodeHead") |] &&
                         emp
  end.

Definition store_mem_node (p : addr) (node : MemNode) : Assertion :=
  &(p # "OsMemNodeHead" ->ₛ "sizeAndFlag") # UInt |-> node.(mem_node_sizeAndFlag) **
  store_mem_block p node.

Lemma store_mem_node_prop : forall p node,
  store_mem_node p node |--
  [| node.(mem_node_size) >= 0 |].
Proof.
  intros.
  unfold store_mem_node,
         store_mem_block.
  destruct mem_node_flag;
  rewrite -> sizeof_OsMemFreeNodeHead;
  entailer!.
Qed.

Fixpoint mem_nodes_seg (px x py y : addr) (l : list (DL_Node MemNode)) : Assertion :=
  match l with
  | nil    => [| px = py |] &&
              [| x = y |] &&
              emp
  | h :: t => [| x = h.(ptr) |] &&
              store_mem_node x h.(data) **
              &(x # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") # Ptr |-> px **
              mem_nodes_seg x (mem_node_next x h.(data)) py y t
  end.

Lemma fold_mem_nodes_seg : forall h t px x py y,
  store_mem_node x h **
  &(x # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") # Ptr |-> px **
  mem_nodes_seg x (mem_node_next x h) py y t |--
  mem_nodes_seg px x py y ({| data := h; ptr := x; |} :: t).
Proof.
  intros.
  simpl.
  entailer!.
Qed.

Lemma mem_nodes_seg_split : forall px x pz z l1 l2,
  mem_nodes_seg px x pz z (l1 ++ l2) |-- EX py y,
  mem_nodes_seg px x py y l1 **
  mem_nodes_seg py y pz z l2.
Proof.
  intros.
  revert px x
         pz z
         l2.
  induction l1;
  intros;
  simpl.
  - Exists px x.
    entailer!.
  - Intros.
    sep_apply IHl1.
    Intros py y.
    Exists py y.
    entailer!.
Qed.

Lemma mem_nodes_seg_concat : forall l1 l2 px x py y pz z,
  mem_nodes_seg px x py y l1 **
  mem_nodes_seg py y pz z l2 |--
  mem_nodes_seg px x pz z (l1 ++ l2).
Proof.
  induction l1;
  intros;
  simpl;
  Intros.
  - subst.
    entailer!.
  - sep_apply IHl1.
    entailer!.
Qed.

Lemma mem_nodes_seg_prop : forall l px x py y,
  mem_nodes_seg px x py y l |--
  [| Forall (Z.le 0) (map mem_node_size (map data l)) /\
     NoDup (map ptr l) /\
     x <= y |].
Proof.
  induction l as [ |h t];
  intros;
  simpl;
  Intros.
  - entailer!.
    constructor.
  - prop_apply store_mem_node_prop.
    prop_apply IHt.
    rewrite -> prop_add_left with (Q := ~ In h.(ptr) (map ptr t)).
    + entailer!;
      unfold mem_node_next in *;
      try constructor;
      intuition.
    + destruct (in_dec addr_eq_dec h.(ptr) (map ptr t)); [ |entailer!].
      apply in_map_iff in i.
      destruct i as [node [? ?]].
      apply in_split in H1.
      destruct H1 as [l1 [l2 ?]].
      subst t.
      Intros.
      sep_apply mem_nodes_seg_split.
      simpl.
      Intros pz z.
      replace z with x by lia.
      prop_apply (dup_store_ptr &(x # "OsMemNodeHead" ->ₛ "ptr" .ₛ "prev") px pz).
      entailer!.
Qed.

Lemma mem_nodes_seg_in_split : forall px x py y node l m r,
  In m (l ++ {| data := node; ptr := m.(ptr); |} :: r) ->
  mem_nodes_seg px x py y (l ++ {| data := node; ptr := m.(ptr); |} :: r) |--
  [| m.(data) = node |].
Proof.
  intros.
  prop_apply mem_nodes_seg_prop.
  Intros.
  destruct H0 as [_ [? _]].
  rewrite -> map_app in H0.
  simpl in H0.
  apply NoDup_remove in H0.
  destruct H0 as [_ ?].
  rewrite -> in_app_iff in H0.
  apply in_app_iff in H.
  simpl in H.
  destruct H as [?|[?|?]];
  try (apply (in_map ptr) in H; intuition).
  rewrite <- H.
  entailer!.
Qed.

Definition mem_nodes_inv (l : list (DL_Node MemNode)) : Prop :=
  l <> nil /\
  sum (map mem_node_size (map data l)) <= OS_MEM_NODE_MAX_SIZE.

Definition store_mem_nodes (p q : addr) (l : list (DL_Node MemNode)) : Assertion :=
  [| mem_nodes_inv l |] &&
  mem_nodes_seg q p q q l.

Lemma fold_store_mem_nodes : forall p q l,
  mem_nodes_inv l ->
  mem_nodes_seg q p q q l |--
  store_mem_nodes p q l.
Proof.
  intros.
  unfold store_mem_nodes.
  entailer!.
Qed.

Lemma store_mem_nodes_prop_at_i : forall p q l node r,
  r <> nil ->
  store_mem_nodes p q (l ++ node :: r) |--
  [| OS_MEM_MIN_LEFT_SIZE <= node.(data).(mem_node_size) <= OS_MEM_NODE_MAX_SIZE |].
Proof.
  intros.
  unfold store_mem_nodes.
  Intros.
  prop_apply mem_nodes_seg_prop.
  Intros.
  destruct H1 as [? [? _]].
  sep_apply mem_nodes_seg_split.
  simpl.
  Intros py y.
  rewrite -> prop_add_left with (Q := node.(data).(mem_node_size) <> 0).
  - Intros.
    unfold mem_nodes_inv in H0.
    destruct H0 as [_ ?].
    repeat rewrite -> map_app in *.
    rewrite -> sum_app in H0.
    simpl in H0.
    apply Forall_app in H1.
    simpl in H1.
    rewrite -> Forall_cons_iff in H1.
    destruct H1 as [? [_ ?]].
    assert (forall l, Forall (Z.le 0) l -> sum l >= 0)
        by (clear; intros; induction H; simpl; lia).
    apply H6 in H1.
    apply H6 in H5.
    unfold store_mem_node.
    unfold store_mem_block.
    destruct mem_node_flag;
    Intros;
    [ |destruct H7; [contradiction| ]];
    unfold OS_MEM_MIN_LEFT_SIZE in *;
    entailer!.
  - destruct (Z.eq_dec node.(data).(mem_node_size) 0); [ |entailer!].
    destruct r; [contradiction| ].
    simpl.
    Intros.
    unfold mem_node_next in H4.
    rewrite -> e in H4.
    rewrite -> Z.add_0_r in H4.
    subst y.
    rewrite -> map_app in H2.
    simpl in H2.
    apply NoDup_remove in H2.
    destruct H2 as [_ ?].
    rewrite -> in_app_iff in H2.
    simpl in H2.
    rewrite -> H4 in H2.
    intuition.
Qed.

Lemma store_mem_nodes_prop_at_end : forall p q l,
  store_mem_nodes p q l |--
  [| exists hs t,
     l = hs ++ {| data := t; ptr := q; |} :: nil /\
     t.(mem_node_size) = 0 /\
     t.(mem_node_flag) <> MemNodeFreeFlag |].
Proof.
  assert (forall p q r l, l <> nil -> exists hs t,
          mem_nodes_seg r p q q l |--
          [| l = hs ++ {| data := t; ptr := q; |} :: nil /\
             t.(mem_node_size) = 0 /\
             t.(mem_node_flag) <> MemNodeFreeFlag |]). {
    intros.
    revert p q r.
    induction l as [ |a l]; [contradiction| ].
    intros.
    simpl.
    Intros.
    destruct l as [ |b l].
    - exists nil, a.(data).
      simpl.
      unfold store_mem_node,
             store_mem_block,
             mem_node_next.
      rewrite -> sizeof_OsMemFreeNodeHead.
      destruct mem_node_flag;
      entailer!.
      * subst.
        destruct a.
        reflexivity.
      * discriminate.
    - pose proof IHl ltac:(discriminate) as IHl.
      specialize IHl with (mem_node_next p a.(data)) q p.
      destruct IHl as [bs [t IHl]].
      exists (a :: bs), t.
      Intros.
      prop_apply IHl.
      entailer!.
      destruct H1 as [? [? ?]].
      rewrite -> H1.
      reflexivity.
  }
  intros.
  unfold store_mem_nodes.
  destruct l as [ |h ts].
  - unfold mem_nodes_inv.
    entailer!.
  - pose proof (H p q q (h :: ts)) ltac:(discriminate) as H.
    destruct H as [hs [t H]].
    Intros.
    prop_apply H.
    entailer!.
    exists hs, t.
    intuition.
Qed.

Lemma free_node_not_end : forall p q l1 node l2,
  node.(data).(mem_node_flag) = MemNodeFreeFlag ->
  store_mem_nodes p q (l1 ++ node :: l2) |--
  [| l2 <> nil |].
Proof.
  intros.
  prop_apply store_mem_nodes_prop_at_end.
  entailer!.
  intros contra.
  subst.
  destruct H0 as [hs [t [? [? ?]]]].
  apply app_inj_tail_iff in H0.
  destruct H0.
  subst.
  contradiction.
Qed.

Fixpoint free_mem_list_seg (px x py y : addr) (l : list addr) : Assertion :=
  match l with
  | nil    => [| px = py |] &&
              [| x = y |] &&
              emp
  | h :: t => EX nx,
              [| x <> NULL |] &&
              [| x = h |] &&
              &(x # "OsMemFreeNodeHead" ->ₛ "prev") # Ptr |-> px **
              &(x # "OsMemFreeNodeHead" ->ₛ "next") # Ptr |-> nx **
              free_mem_list_seg x nx py y t
  end.

Lemma free_mem_list_seg_zero : forall px x py y l,
  x = NULL ->
  free_mem_list_seg px x py y l |--
  [| l = nil |].
Proof.
  intros.
  destruct l;
  simpl.
  - entailer!.
  - Intros nx.
    contradiction.
Qed.

Lemma free_mem_list_seg_split : forall px x pz z l1 l2,
  free_mem_list_seg px x pz z (l1 ++ l2) |-- EX py y,
  free_mem_list_seg px x py y l1 **
  free_mem_list_seg py y pz z l2.
Proof.
  intros.
  revert px x
         pz z
         l2.
  induction l1;
  intros;
  simpl.
  - Exists px x.
    entailer!.
  - Intros nx.
    sep_apply IHl1.
    Intros py y.
    Exists py y.
    Exists nx.
    entailer!.
Qed.

Lemma free_mem_list_seg_concat : forall l1 l2 px x py y pz z,
  free_mem_list_seg px x py y l1 **
  free_mem_list_seg py y pz z l2 |--
  free_mem_list_seg px x pz z (l1 ++ l2).
Proof.
  induction l1;
  intros;
  simpl.
  - Intros.
    subst.
    entailer!.
  - Intros nx.
    Exists nx.
    sep_apply IHl1.
    entailer!.
Qed.

Definition store_free_mem_list (p : addr) (l : list addr) : Assertion :=
  EX q,
  free_mem_list_seg NULL p q NULL l.

Definition OS_MEM_SLI : Z := 3.
Definition OS_MEM_SMALL_BUCKET_COUNT : Z := 31.
Definition OS_MEM_SMALL_BUCKET_MAX_SIZE : Z := 128.
Definition OS_MEM_LARGE_BUCKET_COUNT : Z := 24.
Definition OS_MEM_FREE_LIST_COUNT : Z := OS_MEM_SMALL_BUCKET_COUNT +
                                         OS_MEM_LARGE_BUCKET_COUNT * 2 ^ OS_MEM_SLI.
Definition OS_MEM_BITMAP_WORDS : Z := OS_MEM_FREE_LIST_COUNT / 2 ^ 5 + 1.

Definition free_mem_lists_bitmap_inv
  (lists : list (list addr)) (bitmap : list Z)
: Prop := forall i,
          Znth i lists nil = nil <->
          Z.testbit (Znth (i / 2 ^ 5) bitmap 0) (i mod 2 ^ 5) = false.

Definition store_free_mem_bitmap (p : addr) (lists : list (list addr)) : Assertion :=
  EX bitmap,
  [| free_mem_lists_bitmap_inv lists bitmap |] &&
  store_array (fun p i v => (p + i * sizeof(UINT)) # UInt |-> v)
              p OS_MEM_BITMAP_WORDS bitmap.

Definition store_free_mem_lists (p : addr) (lists : list (list addr)) : Assertion :=
  store_array (fun p i l => EX q,
                            (p + i * sizeof(PTR)) # Ptr |-> q **
                            store_free_mem_list q l)
              p OS_MEM_FREE_LIST_COUNT lists.

Lemma store_free_mem_lists_prop : forall p lists,
  store_free_mem_lists p lists |--
  [| Zlength lists = OS_MEM_FREE_LIST_COUNT |].
Proof.
  intros.
  unfold store_free_mem_lists.
  prop_apply (@store_array_Zlength (list addr)).
  entailer!.
Qed.

Lemma dangling_not_in_free_mem_lists : forall p_node p_lists lists,
  store_free_mem_lists p_lists lists **
  &(p_node # "OsMemFreeNodeHead" ->ₛ "prev") # Ptr |->_ **
  &(p_node # "OsMemFreeNodeHead" ->ₛ "next") # Ptr |->_ |--
  [| ~ In p_node (concat lists) |].
Proof.
  intros.
  destruct (in_dec addr_eq_dec p_node (concat lists)); [ |entailer!].
  apply in_concat in i.
  destruct i as [l [? ?]].
  apply in_split in H.
  destruct H as [lists_l [lists_r ?]].
  subst lists.
  prop_apply store_free_mem_lists_prop.
  Intros.
  unfold store_free_mem_lists.
  sep_apply (@store_array_split (list addr)).
  - Intros p_l.
    rewrite -> app_Znth2 with (i := Zlength lists_l) (d := nil) by lia.
    rewrite -> Z.sub_diag.
    rewrite -> Znth0_cons.
    apply in_split in H0.
    destruct H0 as [l1 [l2 ?]].
    subst l.
    unfold store_free_mem_list.
    Intros q.
    sep_apply free_mem_list_seg_split.
    Intros py y.
    simpl.
    Intros nx.
    subst y.
    sep_apply (poly_store_poly_undef_store &(p_node # "OsMemFreeNodeHead" ->ₛ "prev") FET_ptr).
    prop_apply (dup_undef_store_ptr &(p_node # "OsMemFreeNodeHead" ->ₛ "prev")).
    entailer!.
  - rewrite <- H.
    rewrite -> Zlength_app.
    rewrite -> Zlength_cons.
    pose proof (Zlength_nonneg lists_l).
    pose proof (Zlength_nonneg lists_r).
    lia.
Qed.

Definition OS_MEM_POOL_UNLOCK_ENABLE_BIT : Z := 1.
Definition OS_MEM_POOL_UNLOCK_ENABLE : Z := Z.setbit 0 OS_MEM_POOL_UNLOCK_ENABLE_BIT.

Record MemPool : Type := {
  mem_pool_lock_free : bool;
  mem_pool_mem_nodes : list (DL_Node MemNode);
  mem_pool_free_list : list (list addr);
}.

Definition mem_pool_size (pool : MemPool) : Z :=
  sizeof("OsMemPoolHead") + sum (map mem_node_size (map data pool.(mem_pool_mem_nodes))).
Notation "pool '.(mem_pool_size)'" := (mem_pool_size pool) (at level 0).

Definition mem_pool_attr (pool : MemPool) : Z :=
  if pool.(mem_pool_lock_free) then OS_MEM_POOL_UNLOCK_ENABLE else 0.
Notation "pool '.(mem_pool_attr)'" := (mem_pool_attr pool) (at level 0).

Definition update_mem_pool_mem_nodes
  (pool : MemPool) (mem_nodes : list (DL_Node MemNode))
: MemPool := {|
  mem_pool_lock_free := pool.(mem_pool_lock_free);
  mem_pool_mem_nodes := mem_nodes;
  mem_pool_free_list := pool.(mem_pool_free_list);
|}.
Notation "pool '.(update_mem_pool_mem_nodes)'" := (update_mem_pool_mem_nodes pool) (at level 0).

Definition update_mem_pool_free_list
  (pool : MemPool) (free_list : list (list addr))
: MemPool := {|
  mem_pool_lock_free := pool.(mem_pool_lock_free);
  mem_pool_mem_nodes := pool.(mem_pool_mem_nodes);
  mem_pool_free_list := free_list;
|}.
Notation "pool '.(update_mem_pool_free_list)'" := (update_mem_pool_free_list pool) (at level 0).

Definition mem_pool_first_node (p : addr) : addr := p + sizeof("OsMemPoolHead").

Definition mem_pool_end_node (p : addr) (pool : MemPool) : addr :=
  p + pool.(mem_pool_size) - sizeof("OsMemNodeHead").

Definition addr_in_mem_pool (p_pool : addr) (pool : MemPool) (p : addr) : Prop :=
  p_pool + sizeof("OsMemPoolHead") <= p < p_pool + pool.(mem_pool_size).

Definition free_list_index (node : MemNode) : Z :=
  if Z_lt_ge_dec node.(mem_node_size) OS_MEM_SMALL_BUCKET_MAX_SIZE
  then node.(mem_node_size) / 4 - 1
  else let log_sz := Z.log2 node.(mem_node_size) in
       (node.(mem_node_size) - 2 ^ log_sz) * 2 ^ OS_MEM_SLI / 2 ^ log_sz.

Lemma free_list_index_in_bounds : forall node,
  OS_MEM_MIN_LEFT_SIZE <= node.(mem_node_size) <= OS_MEM_NODE_MAX_SIZE ->
  0 <= free_list_index node < OS_MEM_FREE_LIST_COUNT.
Proof.
  intros.
  unfold free_list_index.
  unfold OS_MEM_MIN_LEFT_SIZE in *.
  unfold OS_MEM_NODE_MAX_SIZE in *.
  unfold OS_MEM_NODE_SIZE_BITS in *.
  unfold OS_MEM_SMALL_BUCKET_MAX_SIZE.
  unfold OS_MEM_FREE_LIST_COUNT.
  unfold OS_MEM_SMALL_BUCKET_COUNT,
         OS_MEM_LARGE_BUCKET_COUNT,
         OS_MEM_SLI.
  rewrite -> sizeof_OsMemFreeNodeHead in *.
  assert (0 < 2 ^ Z.log2 node.(mem_node_size) <= node.(mem_node_size)). {
    split.
    - apply Z.pow_pos_nonneg; [lia| ].
      apply Z.log2_nonneg.
    - pose proof (Z.log2_spec node.(mem_node_size)) ltac:(lia).
      intuition.
  }
  destruct Z_lt_ge_dec;
  split.
  - apply Z.le_0_sub.
    apply Z.div_le_lower_bound;
    lia.
  - apply Z.lt_sub_lt_add_r.
    apply Z.div_lt_upper_bound;
    lia.
  - apply Z.div_pos;
    lia.
  - apply Z.div_lt_upper_bound; [lia| ].
    eapply Z.lt_trans.
    + apply Z.mul_lt_mono_pos_r; [lia| ].
      apply Z.lt_sub_lt_add_r.
      rewrite -> Z.sub_simpl_r.
      pose proof (Z.log2_spec node.(mem_node_size)) ltac:(lia).
      destruct H1 as [_ ?].
      eassumption.
    + rewrite -> Z.pow_succ_r by (apply Z.log2_nonneg).
      rewrite <- Z.add_diag.
      rewrite -> Z.add_simpl_r.
      apply Z.mul_lt_mono_pos_l;
      lia.
Qed.

Definition free_list_add
  (free_list : list (list addr)) (p : addr) (node : MemNode)
: list (list addr) :=
  let index := free_list_index node in
  replace_Znth index (p :: Znth index free_list nil) free_list.

Definition free_list_del
  (free_list : list (list addr)) (p : addr) (node : MemNode)
: list (list addr) :=
  let index := free_list_index node in
  replace_Znth index (remove addr_eq_dec p (Znth index free_list nil)) free_list.

Lemma Znth_In : forall {A} (l : list A) n d,
  0 <= n < Zlength l ->
  In (Znth n l d) l.
Proof.
  induction l;
  intros.
  - rewrite -> Zlength_nil in H.
    lia.
  - simpl.
    destruct (Z.eq_dec n 0); subst; auto.
    right.
    rewrite -> Znth_cons by lia.
    apply IHl.
    rewrite -> Zlength_cons in H.
    lia.
Qed.

Lemma Zlength_replace_Znth : forall {A} (l : list A) n a,
  Zlength (replace_Znth n a l) = Zlength l.
Proof.
  enough (forall {A} (l : list A) n a, n >= 0 ->
          Zlength (replace_Znth n a l) = Zlength l). {
    intros.
    destruct n;
    try replace (replace_Znth (Z.neg p) a l)
           with (replace_Znth 0 a l)
             by reflexivity;
    apply H;
    lia.
  }
  induction l;
  intros.
  - rewrite -> replace_Znth_nothing
            by (rewrite -> Zlength_nil; assumption).
    reflexivity.
  - destruct (Z.eq_dec n 0).
    + subst.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      repeat rewrite -> Zlength_cons.
      rewrite -> IHl by lia.
      reflexivity.
Qed.

Lemma Znth_replace_Znth_eq : forall {A} (l : list A) n a d,
  0 <= n < Zlength l ->
  Znth n (replace_Znth n a l) d = a.
Proof.
  induction l;
  intros.
  - rewrite -> Zlength_nil in H.
    lia.
  - destruct (Z.eq_dec n 0); subst.
    + reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      apply IHl.
      rewrite -> Zlength_cons in H.
      lia.
Qed.

Lemma Znth_replace_Znth_neq : forall {A} (l : list A) n m a d,
  n >= 0 -> m >= 0 -> n <> m ->
  Znth n (replace_Znth m a l) d = Znth n l d.
Proof.
  induction l;
  intros.
  - rewrite -> replace_Znth_nothing
            by (rewrite -> Zlength_nil; assumption).
    reflexivity.
  - destruct (Z.eq_dec m 0);
    destruct (Z.eq_dec n 0);
    subst.
    + contradiction.
    + replace (replace_Znth 0 a0 (a :: l))
         with (a0 :: l)
           by reflexivity.
      rewrite -> Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      reflexivity.
    + rewrite -> replace_Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      rewrite -> Znth_cons by lia.
      rewrite -> IHl by lia.
      reflexivity.
Qed.

Lemma free_list_add_In : forall free_list i x p node,
  In x (Znth i (free_list_add free_list p node) nil) ->
  x = p \/ In x (Znth i free_list nil).
Proof.
  enough (forall {A} ls i j (x y : A),
          In x (nth i (replace_nth j (y :: nth j ls nil) ls) nil) ->
          x = y \/ In x (nth i ls nil))
      by (unfold free_list_add, Znth, replace_Znth; eauto).
  induction ls;
  destruct i;
  destruct j;
  simpl;
  intros;
  eauto;
  intuition.
Qed.

Lemma free_list_add_incl : forall free_list i p node,
  incl (Znth i free_list nil)
       (Znth i (free_list_add free_list p node) nil).
Proof.
  enough (forall {A} ls i j (a : A),
          incl (nth i ls nil)
               (nth i (replace_nth j (a :: nth j ls nil) ls) nil))
      by (unfold free_list_add, Znth, replace_Znth; auto).
  induction ls;
  destruct i;
  destruct j;
  simpl;
  intros;
  auto using incl_refl, incl_tl.
Qed.

Lemma free_list_del_In : forall free_list i x p node,
  In x (Znth i free_list nil) ->
  x = p \/ In x (Znth i (free_list_del free_list p node) nil).
Proof.
  enough (forall {A} eq_dec ls i j (x y : A),
          In x (nth i ls nil) ->
          x = y \/ In x (nth i (replace_nth j (remove eq_dec y (nth j ls nil)) ls) nil))
      by (unfold free_list_del, Znth, replace_Znth; auto).
  induction ls;
  destruct i;
  destruct j;
  simpl;
  intros;
  auto.
  destruct (eq_dec x y);
  auto using in_in_remove.
Qed.

Lemma free_list_del_incl : forall free_list i p node,
  incl (Znth i (free_list_del free_list p node) nil)
       (Znth i free_list nil).
Proof.
  enough (forall {A} eq_dec ls i j (a : A),
          incl (nth i (replace_nth j (remove eq_dec a (nth j ls nil)) ls) nil)
               (nth i ls nil))
      by (unfold free_list_del, Znth, replace_Znth; auto).
  induction ls;
  destruct i;
  destruct j;
  simpl;
  intros;
  auto using incl_refl.
  enough (forall a l, incl (remove eq_dec a l) l) by auto.
  induction l;
  simpl;
  intros.
  - apply incl_refl.
  - destruct eq_dec; subst.
    + auto using incl_tl.
    + apply incl_cons;
      intuition.
Qed.

Definition store_mem_pool_info (p : addr) (pool : MemPool) : Assertion :=
  let info := &(p # "OsMemPoolHead" ->ₛ "info") in
  [| p + pool.(mem_pool_size) <= UINTPTR_MAX |] &&
  &(info # "OsMemPoolInfo" ->ₛ "pool") # Ptr |-> p **
  &(info # "OsMemPoolInfo" ->ₛ "totalSize") # UInt |-> pool.(mem_pool_size) **
  &(info # "OsMemPoolInfo" ->ₛ "attr") # UInt |-> pool.(mem_pool_attr) **
  &(info # "OsMemPoolInfo" ->ₛ "waterLine") # UInt |->_ **
  &(info # "OsMemPoolInfo" ->ₛ "curUsedSize") # UInt |->_ **
  &(p # "OsMemPoolHead" ->ₛ "nextPool") # Ptr |->_.

Definition mem_pool_with_danglings_inv (pool : MemPool) (danglings : list addr) : Prop :=
  let free_nodes_in_free_list_except_danglings :=
    Forall (fun node => node.(data).(mem_node_flag) = MemNodeFreeFlag ->
                        In node.(ptr) danglings \/
                        In node.(ptr) (Znth (free_list_index node.(data))
                                            pool.(mem_pool_free_list)
                                            nil))
           pool.(mem_pool_mem_nodes) in
  let free_list_addrs_valid :=
    Forall (fun p => exists node,
                     node.(ptr) = p /\
                     In node pool.(mem_pool_mem_nodes))
           (concat pool.(mem_pool_free_list)) in
  let dangling_nodes_valid :=
    Forall (fun p => exists node,
                     node.(ptr) = p /\
                     node.(data).(mem_node_flag) = MemNodeFreeFlag /\
                     In node pool.(mem_pool_mem_nodes))
           danglings in
  free_nodes_in_free_list_except_danglings /\
  free_list_addrs_valid /\
  dangling_nodes_valid.
Notation mem_pool_inv pool := (mem_pool_with_danglings_inv pool nil).
Notation mem_pool_with_dangling_i_inv pool i := (mem_pool_with_danglings_inv pool (i :: nil)).

Definition store_mem_pool_with_danglings
  (p : addr) (pool : MemPool) (danglings : list addr)
: Assertion :=
  [| mem_pool_with_danglings_inv pool danglings |] &&
  store_mem_pool_info p pool **
  store_free_mem_bitmap &(p # "OsMemPoolHead" ->ₛ "freeListBitmap") pool.(mem_pool_free_list) **
  store_free_mem_lists &(p # "OsMemPoolHead" ->ₛ "freeList") pool.(mem_pool_free_list) **
  store_mem_nodes (mem_pool_first_node p) (mem_pool_end_node p pool) pool.(mem_pool_mem_nodes) **
  iter_sepcon (map (fun p => &(p # "OsMemFreeNodeHead" ->ₛ "prev") # Ptr |->_ **
                             &(p # "OsMemFreeNodeHead" ->ₛ "next") # Ptr |->_)
                   danglings).
Notation store_mem_pool p pool := (store_mem_pool_with_danglings p pool nil).
Notation store_mem_pool_with_dangling_i p pool i :=
  (store_mem_pool_with_danglings p pool (i :: nil)).

Lemma mem_pool_permute_danglings : forall pool danglings danglings',
  Permutation danglings danglings' ->
  mem_pool_with_danglings_inv pool danglings ->
  mem_pool_with_danglings_inv pool danglings'.
Proof.
  intros.
  assert (forall i, In i danglings <-> In i danglings'). {
    split;
    apply Permutation_in;
    [ |apply Permutation_sym];
    assumption.
  }
  unfold mem_pool_with_danglings_inv in *.
  repeat rewrite -> Forall_forall in *.
  repeat split;
  intros;
  repeat rewrite <- H1 in *;
  intuition.
Qed.

Lemma mem_pool_add_dangling : forall pool danglings mem_nodes_l node mem_nodes_r,
  node.(data).(mem_node_flag) = MemNodeFreeFlag ->
  pool.(mem_pool_mem_nodes) = mem_nodes_l ++ mem_nodes_r ->
  mem_pool_with_danglings_inv pool danglings ->
  mem_pool_with_danglings_inv (pool.(update_mem_pool_mem_nodes) (mem_nodes_l ++
                                                                 node ::
                                                                 mem_nodes_r))
                              (node.(ptr) :: danglings).
Proof.
  intros.
  unfold mem_pool_with_danglings_inv in *.
  rewrite -> H0 in *.
  simpl.
  destruct H1 as [? [? ?]].
  repeat rewrite -> Forall_forall in *.
  repeat split;
  intros.
  - destruct (in_dec addr_eq_dec x.(ptr) (node.(ptr) :: danglings)); [intuition| ].
    apply or_assoc.
    right.
    apply H1; [ |assumption].
    apply in_app_iff in H4.
    simpl in H4.
    apply in_app_iff.
    destruct H4 as [?|[?|?]]; auto.
    subst node.
    simpl in n.
    intuition.
  - pose proof (H2 x) ltac:(assumption) as [node_x [? ?]].
    exists node_x.
    rewrite -> in_app_iff in *.
    intuition.
  - simpl in H4.
    destruct H4.
    + exists node.
      intuition.
    + pose proof (H3 x) ltac:(assumption) as [node_x [? [? ?]]].
      exists node_x.
      rewrite -> in_app_iff in *.
      intuition.
Qed.

Lemma mem_pool_del_dangling : forall pool danglings mem_nodes_l node mem_nodes_r,
  pool.(mem_pool_mem_nodes) = mem_nodes_l ++ node :: mem_nodes_r ->
  NoDup (map ptr pool.(mem_pool_mem_nodes)) ->
  NoDup (node.(ptr) :: danglings) ->
  Forall (fun p => ~ In p (concat pool.(mem_pool_free_list))) (node.(ptr) :: danglings) ->
  mem_pool_with_danglings_inv pool (node.(ptr) :: danglings) ->
  mem_pool_with_danglings_inv (pool.(update_mem_pool_mem_nodes) (mem_nodes_l ++ mem_nodes_r))
                              danglings.
Proof.
  intros.
  unfold mem_pool_with_danglings_inv in *.
  rewrite -> H in *.
  simpl.
  destruct H3 as [? [? ?]].
  repeat rewrite -> Forall_forall in *.
  repeat split;
  intros.
  - specialize H3 with x.
    pose proof H3 ltac:(rewrite -> in_app_iff in *; intuition) ltac:(assumption) as H3.
    simpl in H3.
    destruct H3 as [[?|?]|?]; auto.
    rewrite -> map_app in H0.
    simpl in H0.
    apply NoDup_remove_2 in H0.
    apply (in_map ptr) in H6.
    rewrite -> map_app in H6.
    rewrite <- H3 in H6.
    contradiction.
  - pose proof (H4 x) ltac:(assumption) as H4.
    destruct H4 as [node_x [? ?]].
    exists node_x.
    split; [assumption| ].
    apply in_app_iff in H7.
    simpl in H7.
    destruct H7 as [?|[?|?]]; intuition.
    subst node_x.
    subst x.
    pose proof (H2 node.(ptr)) ltac:(intuition) as H2.
    contradiction.
  - pose proof (H5 x) ltac:(intuition) as H5.
    destruct H5 as [node_x [? [? ?]]].
    exists node_x.
    intuition.
    apply in_app_iff in H8.
    destruct H8 as [?|[?|?]]; intuition.
    subst node_x.
    subst x.
    apply NoDup_cons_iff in H1.
    intuition.
Qed.

Lemma mem_pool_attach_dangling : forall pool danglings node,
  In node pool.(mem_pool_mem_nodes) ->
  0 <= free_list_index node.(data) < Zlength pool.(mem_pool_free_list) ->
  NoDup (map ptr pool.(mem_pool_mem_nodes)) ->
  mem_pool_with_danglings_inv pool (node.(ptr) :: danglings) ->
  mem_pool_with_danglings_inv
    (pool.(update_mem_pool_free_list) (free_list_add pool.(mem_pool_free_list)
                                                     node.(ptr) node.(data)))
    danglings.
Proof.
  intros.
  unfold mem_pool_with_danglings_inv in *.
  simpl.
  destruct H2 as [? [? ?]].
  repeat rewrite -> Forall_forall in *.
  repeat split;
  intros.
  - pose proof (H2 x) ltac:(assumption) ltac:(assumption) as H2.
    simpl in H2.
    destruct H2 as [[?|?]|?]; auto.
    + enough (x = node). {
        subst x.
        right.
        unfold free_list_add.
        rewrite -> Znth_replace_Znth_eq by assumption.
        intuition.
      }
      apply in_split in H.
      destruct H as [l1 [l2 ?]].
      rewrite -> H in *.
      apply in_app_iff in H5.
      simpl in H5.
      destruct H5 as [?|[?|?]]; auto;
      rewrite -> map_app in H1;
      simpl in H1;
      apply NoDup_remove_2 in H1;
      rewrite -> in_app_iff in H1;
      apply (in_map ptr) in H5;
      rewrite <- H2 in H5;
      intuition.
    + right.
      generalize dependent x.(ptr).
      apply Forall_forall.
      apply incl_Forall_in_iff.
      apply free_list_add_incl.
  - apply in_concat in H5.
    destruct H5 as [l [? ?]].
    apply in_split in H5.
    destruct H5 as [free_list_l [free_list_r ?]].
    assert (l = Znth (Zlength free_list_l)
                     (free_list_add pool.(mem_pool_free_list) node.(ptr) node.(data))
                     nil). {
      rewrite -> H5.
      rewrite -> app_Znth2 by lia.
      rewrite -> Z.sub_diag.
      rewrite -> Znth0_cons.
      reflexivity.
    }
    subst l.
    apply free_list_add_In in H6.
    destruct H6; eauto.
    enough (In x (concat pool.(mem_pool_free_list))) by auto.
    apply in_concat.
    exists (Znth (Zlength free_list_l) pool.(mem_pool_free_list) nil).
    intuition.
    apply Znth_In.
    apply (f_equal (@Zlength (list _))) in H5.
    unfold free_list_add in H5.
    rewrite -> Zlength_replace_Znth in H5.
    rewrite -> Zlength_app in H5.
    rewrite -> Zlength_cons in H5.
    pose proof (Zlength_nonneg free_list_l).
    pose proof (Zlength_nonneg free_list_r).
    lia.
  - intuition.
Qed.

Lemma mem_pool_detach_free_node : forall pool danglings node,
  node.(data).(mem_node_flag) = MemNodeFreeFlag ->
  In node pool.(mem_pool_mem_nodes) ->
  mem_pool_with_danglings_inv pool danglings ->
  mem_pool_with_danglings_inv
    (pool.(update_mem_pool_free_list) (free_list_del pool.(mem_pool_free_list)
                                                     node.(ptr) node.(data)))
    (node.(ptr) :: danglings).
Proof.
  intros.
  unfold mem_pool_with_danglings_inv in *.
  simpl.
  destruct H1 as [? [? ?]].
  repeat rewrite -> Forall_forall in *.
  repeat split;
  intros.
  - pose proof (H1 x) ltac:(assumption) ltac:(assumption) as H1.
    destruct H1; auto.
    eapply free_list_del_In in H1.
    destruct H1; eauto.
  - enough (In x (concat pool.(mem_pool_free_list))) by auto.
    rewrite -> in_concat in *.
    destruct H4 as [l [? ?]].
    apply in_split in H4.
    destruct H4 as [free_list_l [free_list_r ?]].
    assert (l = Znth (Zlength free_list_l)
                     (free_list_del pool.(mem_pool_free_list) node.(ptr) node.(data))
                     nil). {
      rewrite -> H4.
      rewrite -> app_Znth2 by lia.
      rewrite -> Z.sub_diag.
      rewrite -> Znth0_cons.
      reflexivity.
    }
    exists (Znth (Zlength free_list_l) pool.(mem_pool_free_list) nil).
    split.
    + apply Znth_In.
      apply (f_equal (@Zlength (list _))) in H4.
      unfold free_list_del in H4.
      rewrite -> Zlength_replace_Znth in H4.
      rewrite -> Zlength_app in H4.
      rewrite -> Zlength_cons in H4.
      pose proof (Zlength_nonneg free_list_l).
      pose proof (Zlength_nonneg free_list_r).
      lia.
    + generalize dependent x.
      apply Forall_forall.
      apply incl_Forall_in_iff.
      subst l.
      apply free_list_del_incl.
  - simpl in H4.
    destruct H4;
    eauto.
Qed.

Record LOS_MEM_POOL_STATUS := {
  mem_pool_status_totalUsedSize : Z;
  mem_pool_status_totalFreeSize : Z;
  mem_pool_status_maxFreeNodeSize : Z;
  mem_pool_status_usedNodeNum : Z;
  mem_pool_status_freeNodeNum : Z;
  mem_pool_status_usageWaterLine : Z;
}.

Definition store_mem_pool_status (x: addr) (s: LOS_MEM_POOL_STATUS) : Assertion :=
  [| 0 <= s.(mem_pool_status_maxFreeNodeSize) <= OS_MEM_NODE_MAX_SIZE |] &&
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "totalUsedSize") # UInt |-> s.(mem_pool_status_totalUsedSize) **
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "totalFreeSize") # UInt |-> s.(mem_pool_status_totalFreeSize) **
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "maxFreeNodeSize") # UInt |-> s.(mem_pool_status_maxFreeNodeSize) **
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "usedNodeNum") # UInt |-> s.(mem_pool_status_usedNodeNum) **
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "freeNodeNum") # UInt |-> s.(mem_pool_status_freeNodeNum) **
  &(x # "LOS_MEM_POOL_STATUS" ->ₛ "usageWaterLine") # UInt |-> s.(mem_pool_status_usageWaterLine).
