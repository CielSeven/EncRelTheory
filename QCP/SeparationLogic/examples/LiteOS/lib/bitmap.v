Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.BinPos.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Classical.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import Psatz Zquot.
Require Import compcert.lib.Zbits.
Require Import compcert.lib.Coqlib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.


Definition UINT32_len:=32%nat.

Fixpoint unionLists_aux (a:Z)(continution:list Z->list Z)(l2:list Z):list Z:=
    match l2 with
    |nil => a::(continution nil)
    |b::l2' => 
        match Z_dec a b with
        | inleft (left _) => a::(continution l2)
        | inleft (right _) => b::(unionLists_aux a continution l2')
        | _ => a::(continution l2')
        end
    end.
Fixpoint unionLists(l1 l2:list Z):list Z:= (*两个有序列表的并*)
    match l1 with
    | nil => l2
    | a::l1'=>
        unionLists_aux a (unionLists l1') l2
    end.

Fixpoint interLists_aux (a:Z)(continution:list Z->list Z)(l2:list Z):list Z:=
    match l2 with
    | nil => nil
    | b::l2' => 
        match Z_dec a b with
        | inleft (left _) => (continution l2)
        | inleft (right _) => interLists_aux a continution l2'
        | _ => a::(continution l2')
        end
    end.
Fixpoint interLists(l1 l2:list Z):list Z:= (*两个有序列表的交*)
    match l1 with
    | nil => nil
    | a::l1'=>
        interLists_aux a (interLists l1') l2
    end.
    
Fixpoint isOrder (a:Z)(l:list Z):Prop:= (*表示一个列表是首个元素>=a的严格上升序列，一般用isOrder 0 l来表示一个列表是非负无重复的有序列表*)
    match l with
    |nil => True
    |b::l' => a<=b/\isOrder (b+1) l'
    end.
Definition addList (a:Z)(l:list Z):list Z:=unionLists (a::nil) l. (*添加单个元素*)

Fixpoint removeLists_aux (a:Z)(continution:list Z->list Z)(l2:list Z):list Z:=
    match l2 with
    |nil => nil
    |b::l2' => 
        match Z_dec a b with
        | inleft (left _) => continution l2
        | inleft (right _) => b::(removeLists_aux a continution l2')
        | _ => continution l2'
        end
    end.
Fixpoint removeLists (l1 l2:list Z):list Z:= (*两个有序列表的差，从l2中移除l1包含的所有元素，即l1的补集交l2*)
    match l1 with
    | nil => l2
    | a::l' =>
        removeLists_aux a (removeLists l') l2
    end.
    
Definition delList (a:Z)(l:list Z):list Z:=removeLists (a::nil) l. (*移除单个元素*)

Lemma land_1_odd: forall (x:Z), Z.land x 1=0 <-> Z.odd x=false.
Proof.
intros x.
rewrite <- (Z.bits_inj_iff' (Z.land x 1) 0).
split ; intros.
- specialize (H 0 (ltac:(lia))).
  rewrite Z.land_spec in H.
  simpl in H.
  rewrite andb_true_r in H.
  auto.
- rewrite Z.land_spec.
  destruct n ; simpl in * ; auto.
  + rewrite H. auto.
  + rewrite andb_false_r. auto.
Qed.

Lemma Z_one_bits_range_aux:forall n x i j,
In j (Z_one_bits n x i) -> i <= j < i + Z.of_nat n.
Proof.
induction n; simpl In.
tauto.
intros x i j. rewrite Nat2Z.inj_succ.
assert (In j (Z_one_bits n (Z.div2 x) (i + 1)) -> i <= j < i + Z.succ (Z.of_nat n)).
  intros. exploit IHn; eauto. lia.
destruct (Z.odd x); simpl.
intros [A|B]. subst j. lia. auto.
auto.
Qed.

Lemma land_pos_reduce: forall x y, Pos.land x (y~0) <>N0->Pos.land (Pos.div2 x)y<>N0.
Proof.
intros.
destruct x;
simpl in *;
try lia.
Qed.

Lemma land_pos_Z:forall x y,Z.land (Z.pos x) (Z.pos y)=Z.of_N (Pos.land x y).
unfold Z.land.
auto.
Qed.

Lemma mul_pos_Z:forall x y,Z.land (Z.pos x) (Z.pos y)=Z.of_N (Pos.land x y).
unfold Z.mul.
auto.
Qed.

Lemma shiftl_mul_2:forall x, 2*x=Z.shiftl x 1.
intros.
rewrite Z.mul_comm.
assert(2=2^1)by lia.
rewrite H.
rewrite Z.shiftl_mul_pow2;
lia.
Qed.

Lemma shiftl_double:forall x, Z.double x=Z.shiftl x 1.
intros x.
rewrite Z.double_spec.
rewrite<-shiftl_mul_2.
auto.
Qed.

Lemma shiftl_succ_double:forall x, Z.succ_double x=Z.lor (Z.shiftl x 1) 1.
intros x.
rewrite Z.succ_double_spec.
rewrite<-shiftl_mul_2.
unfold Z.lor.
destruct x;simpl;try lia.
induction p;simpl;auto.
Qed.

Lemma land_shiftl_1:forall x y,Z.land x (Z.shiftl y 1)=Z.shiftl (Z.land (Z.div2 x) y) 1.
intros.
rewrite (Zdecomp x) at 1.
unfold Zshiftin.
destruct (Z.odd x);
try rewrite shiftl_succ_double;
try rewrite shiftl_double.
rewrite Z.land_lor_distr_l.
assert(Z.land 1 (Z.shiftl y 1)=0). {
    rewrite Z.land_comm.
    rewrite land_1_odd.
    rewrite<-shiftl_mul_2.
    rewrite Z.odd_mul.
    simpl.
    auto.
}
rewrite H.
rewrite Z.lor_0_r.
all:rewrite<-Z.shiftl_land;auto.
Qed.

Lemma shiftl_0:forall x,Z.shiftl x 1<>0<->x<>0.
intros.
rewrite<-shiftl_mul_2.
lia.
Qed.

Lemma land_reduce: forall x y, x>=0->y>=0->Z.land x (Z.shiftl y 1)<>0<->Z.land (Z.div2 x)y<>0.
Proof.
intros.
rewrite land_shiftl_1.
apply shiftl_0.
Qed.

Lemma div2_range:forall x y:Z,0<=x<2*y->0<=Z.div2 x<y.
Proof.
intros.
rewrite (Zdiv2_odd_eqn x) in H.
destruct (Z.odd x);
lia.
Qed.

Lemma two_p_shiftl_1:forall q,q>=0->two_p (q+1)=Z.shiftl (two_p q) 1.
Proof.
    intros q H.
    assert(Z.shiftl 1 (q+1)=two_p (q+1)).
    rewrite Zshiftl_mul_two_p;
    lia.
    assert(Z.shiftl 1 q=two_p q).
    rewrite Zshiftl_mul_two_p;
    lia.
    rewrite<-H0.
    rewrite<-H1.
    symmetry.
    apply Z.shiftl_shiftl.
    lia.
Qed.

Lemma Z_one_bits_land: forall (n:nat) (x i p:Z),
0 <= x < two_power_nat n -> 0<=p -> Z.land x (two_p p)<>0
<-> In (i+p) (Z_one_bits n x i). (*证明了Z_one_bits与逻辑与运算的关系，其中Z_one_bits见Zbits.v*)
Proof.
induction n.
-
rewrite two_power_nat_O.
intros.
assert(x=0)by lia.
subst x.
simpl.
intuition.
-
simpl.
intros.
split.
intros J.
destruct (Z_le_gt_dec p 0).
assert(p=0)by lia.
subst p.
simpl in J.
assert(Z.odd x=true). {
    destruct (Z.odd x) eqn:E.
    reflexivity.
    pose proof (proj2 (land_1_odd x) E) as Q.
    lia.
}
rewrite H1 in *.
simpl.
left.
lia.
set (q:=p-1).
assert(p=q+1)by lia.
assert(q>=0)by lia.
rewrite H1 in *.
assert(Z.land (Z.div2 x) (two_p q) <> 0). {
    pose proof (two_p_shiftl_1 q H2)as H3.
    rewrite H3 in J.
    apply land_reduce;
    try lia.
    rewrite two_p_equiv.
    lia.
}
assert(In (i+(q+1)) (Z_one_bits n (Z.div2 x) (i + 1))). {
    assert(i+(q+1)=(i+1)+q) by lia.
    rewrite H4.
    apply IHn;
    try lia.
    rewrite two_power_nat_S in H.
    apply div2_range.
    auto.
}
destruct (Z.odd x);
try right;
auto.

intros J.
destruct (Z_le_gt_dec p 0).
assert(p=0)by lia.
subst p.
destruct (Z.odd x) eqn:K;
unfold two_p.
unfold not.
intros L.
pose proof ((proj1 (land_1_odd x)) L) as M.
rewrite K in M.
discriminate.
pose proof ((Z_one_bits_range_aux n (Z.div2 x)(i+1)(i+0)) J) as L.
lia.
assert(L:Z.land (Z.div2 x) (two_p (p-1))<>0).
{
    apply IHn with (i:=i+1);
    rewrite two_power_nat_S in *;
    try apply div2_range;
    try lia.
    destruct (Z.odd x);
    try destruct J as [J|J];
    try lia;
    assert(K:(i+p)=(i+1)+(p-1)) by lia;
    rewrite K in J;
    auto.
}
destruct (Z.odd x);
try destruct J as [J|J];
try lia;
assert(K:(i+p)=(i+1)+(p-1)) by lia;
rewrite K in J;
assert(p-1>=0)by lia;
pose proof (two_p_shiftl_1 (p-1) H1) as M;
assert(p-1+1=p)by lia;
rewrite H2 in M;
rewrite M;
apply<-land_reduce;
auto;
try lia;
rewrite two_p_equiv;
lia.
Qed.

Lemma isOrder_aux:forall a b (l:list Z),a<=b->isOrder b l->isOrder a l.
Proof.
intros.
destruct l.
simpl.
auto.
simpl in *.
destruct H0 as [P Q].
split.
lia.
auto.
Qed.

Lemma powerserie_ge_O:forall (l:list Z),powerserie l>=0.
Proof.
induction l;simpl;try lia.
assert(two_p a>=0). {
    rewrite two_p_equiv.
    lia.
}
lia.
Qed.

Lemma powerserie_O:forall a (l:list Z),powerserie l=0->a>=0->isOrder a l->l=nil. 
Proof.
induction l;
simpl.
auto.
intros P M [Q R].
assert(two_p a0>0). {
    rewrite two_p_equiv.
    lia.
}
pose proof (powerserie_ge_O l).
lia.
Qed.

Lemma Z_one_bits_Order:forall n x i,i>=0->isOrder i (Z_one_bits n x i).
Proof.
induction n;
intros;
simpl.
auto.
destruct (Z.odd x).
simpl.
split;
try lia.
apply IHn with (i:=i+1).
lia.
assert(isOrder (i+1) (Z_one_bits n (Z.div2 x) (i + 1))). {
    apply IHn.
    lia.
}
apply isOrder_aux with (b:=i+1).
lia.
auto.
Qed.

Lemma odd_two_p:forall (a:Z),Z.odd(two_p a)=true<->a=0.
Proof.
intros.
split.
-
intros H.
destruct a;
try lia.
assert(0<Z.pos p)by lia.
pose proof (two_p_equiv (Z.pos p)) as P.
rewrite P in H.
rewrite Z.odd_pow in H.
simpl in H.
discriminate.
lia.
unfold two_p in H.
simpl in H.
discriminate.
-
intros H.
subst a.
simpl.
auto.
Qed.

Lemma powerserie_aux:forall (l:list Z)i,i>=0->isOrder i l->(exists x,powerserie l=x*two_p i).
intros.
induction l.
exists 0.
auto.
simpl.
simpl in H0.
destruct H0 as [H0 H1].
assert(isOrder i l). {
    apply isOrder_aux with (a+1).
    lia.
    auto.
}
pose proof (IHl H2) as J.
destruct J as [x J].
exists (x+(two_p (a-i))).
assert(two_p a=two_p (a-i)*two_p i). {
    rewrite_all two_p_equiv.
    rewrite<-Z.pow_add_r;
    try lia.
    assert(a=a-i+i)by lia.
    rewrite H3 at 1.
    auto.
}
lia.
Qed.

Lemma powerserie_odd:forall (l:list Z) i x,i>=0->isOrder i l->(powerserie l=x*two_p i)->(Z.odd x=true)<->(exists l',l=i::l').
intros.
split.
-
intros H2.
induction l.
simpl in H1.
assert(0<two_p i). {
    rewrite two_p_equiv.
    lia.
}
assert(x=0)by lia.
subst x.
simpl in H2.
discriminate H2.

exists l.
simpl in H0.
destruct H0 as [P Q].
destruct (Z_le_gt_dec a i).
assert(a=i)by lia.
rewrite H0.
auto.
simpl in H1.
assert(exists x0,powerserie l=x0*(two_p (a+1))). {
    apply powerserie_aux.
    lia.
    auto.
}
destruct H0 as [x0 H0].
rewrite H0 in H1.
simpl in H1.
repeat rewrite two_p_equiv in H1.
set (k:=a-i).
assert(k>0)by lia.
assert(a=k+i)by lia.
rewrite H4 in H1.
assert(2 ^ (k + i) + x0 * 2 ^ (k + i + 1) =(2^k+x0*2^(k+1))*2^i). {
    assert(k+i+1=k+1+i)by lia.
    rewrite H5.
    repeat rewrite Z.pow_add_r with (c:=i);try lia.
}
rewrite H5 in H1.
assert(2 ^ k + x0 * 2 ^ (k + 1)=x). {
    apply Z.mul_reg_r with (p:=2^i);
    auto.
    assert(0<2^i).
    lia.
    lia.
}
assert(Z.odd (2 ^ k + x0 * 2 ^ (k + 1))=false). {
    assert(Z.odd (2^k)=false).
    rewrite Z.odd_pow;try lia;auto.
    assert(Z.odd (x0 * 2 ^ (k + 1))=false).
    rewrite Z.odd_mul.
    assert(Z.odd (2^(k+1))=false).
    rewrite Z.odd_pow;try lia;auto.
    rewrite H8.
    rewrite andb_false_r.
    auto.
    rewrite Z.odd_add.
    rewrite H7.
    rewrite H8.
    auto.
}
rewrite H6 in H7.
rewrite H7 in H2.
discriminate.
-
intros [l' H2].
subst l.
simpl in *.
destruct H0 as [_ H0].
assert(exists x0,powerserie l'=x0*two_p (i+1)). {
    apply powerserie_aux;try lia;auto.
}
destruct H2 as [x0 H2].
rewrite H2 in H1.
repeat rewrite two_p_equiv in H1.
assert(2 ^ i + x0 * 2 ^ (i + 1)=(1+x0*2)*2^i). {
    rewrite Z.pow_add_r;try lia.
}
rewrite H3 in H1.
assert(1+2*x0=x). {
    apply Z.mul_reg_r with (2^i);try lia.
}
subst x.
rewrite Z.odd_add_mul_2.
auto.
Qed.

Lemma Z_one_bits_powerserie_aux: forall n x i,
0 <= i ->
0 <= x < two_power_nat n ->
x * two_p i = powerserie (Z_one_bits n x i).
Proof.
induction n; intros.
  simpl. rewrite two_power_nat_O in H0.
  assert (x = 0) by lia. subst x. lia.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  rewrite (Zdecomp x) in H0. rewrite Zshiftin_spec in H0.
  assert (EQ: Z.div2 x * two_p (i + 1) = powerserie (Z_one_bits n (Z.div2 x) (i + 1))).
    apply IHn. lia.
    destruct (Z.odd x); lia.
  rewrite two_p_is_exp in EQ. change (two_p 1) with 2 in EQ.
  rewrite (Zdecomp x) at 1. rewrite Zshiftin_spec.
  destruct (Z.odd x); simpl powerserie; rewrite <- EQ; ring.
  lia. lia.
  Qed.

Lemma powerserie_complete_aux: forall (n:nat) (x:Z)(i:Z) (l:list Z),
0 <= x < two_power_nat n ->i>=0-> l=Z_one_bits n x i<->(x*(two_p i) = powerserie l/\ isOrder i l). (*Z_one_bits等价于powerserie加上isOrder*)
Proof.
induction n.
-
intros.
unfold two_power_nat in H.
simpl in H.
assert(x=0)by lia.
subst x.
split.
+
simpl.
intros.
subst l.
simpl.
auto.
+
simpl.
intros [P Q].
apply powerserie_O with i;
auto.
-
intros.
split.
+
intros P.
split.
--
rewrite P.
apply Z_one_bits_powerserie_aux;
try lia.
--
rewrite P.
apply Z_one_bits_Order.
auto.
+
intros [P Q].
simpl.
destruct (Z.odd x) eqn:K.
--
destruct l.
simpl in P.
assert(two_p i>0).
rewrite two_p_equiv.
lia.
assert(x=0)by lia.
subst x.
simpl in K.
discriminate.
assert(exists l',z::l=i::l'). {
    apply powerserie_odd with (x:=x);try lia;auto.
}
destruct H1 as [l' H1].
inversion H1.
subst l'.
subst z.
assert(l=Z_one_bits n (Z.div2 x) (i + 1)). {
    apply<-IHn;try lia.
    split.
    simpl in P.
    assert((x-1)*(two_p i)=Z.div2 x*two_p(i+1)).
    rewrite (Zdecomp x) at 1.
    rewrite K.
    unfold Zshiftin.
    rewrite Z.succ_double_spec.
    assert(2 * Z.div2 x + 1 - 1=2*Z.div2 x)by lia.
    rewrite H2.
    rewrite_all two_p_equiv.
    assert(2 ^ (i + 1)=2*2^i).
    rewrite Z.pow_add_r;try lia.
    rewrite H3.
    lia.
    lia.
    simpl in Q.
    destruct Q as [_ Q].
    auto.
    rewrite two_power_nat_S in H.
    apply div2_range.
    auto.
}
rewrite H2.
auto.
--
apply<-IHn;try lia.
split.
assert(x * two_p i=Z.div2 x * two_p (i + 1)). {
    rewrite (Zdecomp x) at 1.
    rewrite K.
    simpl.
    rewrite Z.double_spec.
    repeat rewrite two_p_equiv.
    rewrite Z.pow_add_r;try lia.
}
rewrite<-H1.
auto.
destruct l.
auto.
simpl in Q.
destruct Q as [J Q].
simpl.
destruct (Z_le_gt_dec (i+1) z).
split;
auto.
assert(z=i)by lia.
subst z.
assert(Z.odd x=true). {
    apply <- (powerserie_odd (i::l) i).
    exists l.
    auto.
    lia.
    simpl.
    split;auto.
    lia.
}
rewrite K in H1.
discriminate.
rewrite two_power_nat_S in H.
apply div2_range.
auto.
Qed.

Lemma isOrder_range:forall a b l,(isOrder a l)->(In b l)->(a<=b). (*证明isOrder限制了列表中元素的范围*)
induction l.
-
intros.
simpl in H0.
contradiction.
-
intros.
simpl in *.
destruct H as [H1 H2].
destruct H0.
lia.
apply IHl;auto.
apply isOrder_aux with (b:=a0+1).
lia.
auto.
Qed.

Lemma isOrder_eq:forall l1 l2 a,(isOrder a l1)->(isOrder a l2)->(forall p,a<=p->In p l1<->In p l2)->(l1=l2). (*isOrder限制了列表完全由其中有哪些元素确定*)
induction l1.
-
intros.
simpl in H1.
destruct l2.
auto.
specialize H1 with z.
simpl in H1.
simpl in H0.
intuition.
-
induction l2.
+
intros.
specialize H1 with a.
simpl in H1.
simpl in H.
intuition.
+
intros.
assert(a=a0). {
    destruct (Z_dec a a0) as [[J|J]|J].
    -
    specialize H1 with a.
    simpl in H1.
    assert(In a l2).
    assert(a0 = a \/ In a l2).
    apply H1;
    simpl in H;
    intuition.
    destruct H2 as [H2|H2].
    lia. auto.
    simpl in H0.
    destruct H0 as [_ H0].
    assert(a0+1<=a). {
        apply isOrder_range with l2;
        auto.
    }
    lia.
    -
    specialize H1 with a0.
    simpl in H1.
    assert(In a0 l1).
    assert(a = a0 \/ In a0 l1).
    apply<-H1;
    simpl in H0;
    intuition.
    destruct H2 as [H2|H2].
    lia. auto.
    simpl in H.
    destruct H as [_ H].
    assert(a+1<=a0). {
        apply isOrder_range with l1;
        auto.
    }
    lia.
    -
    auto.
}
subst a0.
assert(l1=l2). {
    simpl in H.
    simpl in H0.
    destruct H0 as [G1 G2].
    destruct H as [K1 K2].
    apply IHl1 with (a+1);auto.
    intros.
    specialize H1 with p.
    simpl in H1.
    assert(a1<=p)by lia.
    assert(a = p \/ In p l1 <-> a = p \/ In p l2). {
        apply H1.
        auto.
    }
    assert(a<>p)by lia.
    intuition.
}
subst l2.
auto.
Qed.

Lemma powerserie_complete:
forall (n:nat)(x:Z)(l:list Z),
isOrder 0 l->0<=x<two_power_nat n->(x=powerserie l)<->(forall p,0<=p->((In p l)<->(Z.land x (two_p p)<>0))). 
(*有两个等价符号挺难描述，就是powerserie等价于“x与l的对应性”，这个对应性是通过forall p来描述的*)
Proof.
intros.
split.
--
intros.
assert(l=Z_one_bits n x 0). {
    apply<-(powerserie_complete_aux n x 0 l).
    split;
    simpl;
    try lia;
    auto.
    lia.
    auto.
}
subst l.
split.
-
intros.
apply<-(Z_one_bits_land n x 0 p).
assert(0+p=p)by lia.
rewrite H4.
auto.
auto.
auto.
-
intros.
assert(0+p=p)by lia.
rewrite<-H4.
apply Z_one_bits_land;auto.
--
intros.
assert(forall p,0<=p->Z.land x (two_p p) <> 0<->In p (Z_one_bits n x 0)). {
    intros.
    assert(p=0+p)by lia.
    rewrite H3 at 2.
    apply Z_one_bits_land;auto.
}
assert(forall p,0<=p->In p l <->In p (Z_one_bits n x 0)). {
    intros.
    rewrite H1;
    auto.
}
assert(l=(Z_one_bits n x 0)). {
    set (l':=(Z_one_bits n x 0)).
    assert(l'=Z_one_bits n x 0)by auto.
    rewrite<-H4 in *.
    assert(isOrder 0 l'). {
        assert((l'=Z_one_bits n x 0)<->(x*(two_p 0)=powerserie l'/\ isOrder 0 l')).
        apply powerserie_complete_aux;auto;try lia.
        pose proof (proj2 ((proj1 H5) H4)).
        auto.
    }
    apply isOrder_eq with (a:=0);auto.
}
subst l.
apply Z_one_bits_powerserie.
auto.
Qed.

Definition bitmap_complete(n:nat)(x:Z)(l:list Z):=
    0<=x<two_power_nat n/\isOrder 0 l/\x=powerserie l.
(*bitmap描述谓词*)


Lemma union_nil_l:forall (l:list Z),unionLists nil l=l. 
(*列表并空列表的简单性质*)
unfold unionLists.
auto.
Qed.

Lemma union_nil_r:forall (l:list Z),unionLists l nil=l.
(*空列表并列表的简单性质*)
induction l.
unfold unionLists_aux.
unfold unionLists.
auto.
simpl.
rewrite IHl.
auto.
Qed.

Lemma isOrder_unionaux:
forall (a:Z)(continution:list Z->list Z)(l:list Z),
(forall l',isOrder (a+1) l'->isOrder (a+1) (continution l'))->
(forall a',a'<=a->isOrder a' l->isOrder a' (unionLists_aux a continution l)).
intros a continution l H.
induction l.
-
simpl.
split;try auto;try lia.
-
intros a' H1 H2.
simpl.
destruct H2 as [H2 H3].
destruct (Z_dec a a0) as [[G|G]|G];
simpl.
+
split;try lia.
apply H.
simpl.
split.
lia.
auto.
+
split;try lia.
apply IHl.
lia.
auto.
+
subst a0.
split;auto.
Qed.

Lemma isOrder_union:
forall (l1 l2:list Z) a,(isOrder a l1)->(isOrder a l2)->isOrder a (unionLists l1 l2).
(*两个有序列表并起来还是有序的*)
intros l1.
induction l1.
-
simpl. auto.
-
intros l2 a0 H.
simpl in *.
destruct H as [H H1].
apply isOrder_unionaux;auto.
Qed.

Lemma union_prop:
forall (l1 l2:list Z)(a:Z),(isOrder 0 l1)->(isOrder 0 l2)->(In a (unionLists l1 l2))<->(In a l1)\/(In a l2).
(*有序列表的并操作是正确的的证明*)
(*这一个是最先证的所以是最丑的*)
assert(forall (l1 l2:list Z)(a:Z),(isOrder 0 l1)->(isOrder 0 l2)->((In a (unionLists l1 l2))<->(In a l1)\/(In a l2))/\(forall a0,In a (unionLists_aux a0 (unionLists l1) l2)<->(In a l1)\/(In a l2)\/a=a0)). {
    induction l1.
    -
    simpl.
    split;split;intros.
    right. auto.
    destruct H1.
    contradiction.
    auto.
    induction l2.
    +
    simpl in *.
    destruct H1.
    right. right.
    auto.
    left. auto.
    +
    assert(isOrder 0 l2). {
        simpl in H0.
        apply isOrder_aux with (a1+1).
        lia.
        destruct H0 as [_ H0].
        auto.
    }
    simpl in H1.
    destruct (Z_dec a0 a1) as [[J|J]|J];
    simpl in *;
    intuition.
    +
    destruct H1 as [H1|[H1|H1]].
    intuition.
    induction l2.
    --
    simpl in H1.
    intuition.
    --
    simpl.
    assert(isOrder 0 l2). {
        simpl in H0.
        apply isOrder_aux with (a1+1).
        lia.
        destruct H0 as [_ H0].
        auto.
    }
    destruct (Z_dec a0 a1) as [[J|J]|J];
    simpl in *;
    intuition.
    --
    induction l2;
    simpl in *.
    intuition.
    assert(isOrder 0 l2). {
        simpl in H0.
        apply isOrder_aux with (a1+1).
        lia.
        destruct H0 as [_ H0].
        auto.
    }
    destruct (Z_dec a0 a1) as [[J|J]|J];
    simpl in *;
    intuition.
    -
    intros l2 a0 H.
    generalize l2 a0.
    assert(isOrder 0 l1). {
        simpl in H.
        apply isOrder_aux with (a+1).
        lia.
        destruct H as [_ H].
        auto.
    }
    induction l0.
    +
    repeat rewrite union_nil_r.
    simpl.
    intros a1 H1.
    pose proof (fun a2=>proj1 (IHl1 nil a2 H0 H1)).
    split.
    intuition.
    intros a2.
    rewrite H2.
    intuition.
    +
    intros a2 J.
    assert(isOrder 0 l0). {
        simpl in J.
        apply isOrder_aux with (a1+1).
        lia.
        destruct J as [_ J].
        auto.
    }
    pose proof (fun a3=>proj1 (IHl1 (a1 :: l0) a3 H0 J)).
    pose proof (fun a3=>proj2 (IHl1 (l0) a3 H0 H1)).
    pose proof (fun a3=>proj1 (IHl0 a3 H1)).
    pose proof (fun a3=>proj2 (IHl0 a3 H1)).
    pose proof (fun a3=>proj1 (IHl1 (l0) a3 H0 H1)).
    split.
    --
    simpl.
    destruct (Z_dec a a1) as [[K|K]|K];
    simpl.
    rewrite H2.
    simpl.
    intuition.
    rewrite H3.
    intuition.
    subst a.
    rewrite H6.
    simpl.
    intuition.
    --
    intros a3.
    simpl (unionLists_aux _ _ (_::_)).
    destruct (Z_dec a3 a1) as[[K|K]|K];
    destruct (Z_dec a a1) as[[Q|Q]|Q];
    simpl In.
    rewrite H2.
    simpl.
    intuition.
    rewrite H3.
    simpl.
    intuition.
    rewrite H6.
    simpl.
    intuition.
    simpl in H5.
    simpl.
    rewrite H5.
    intuition.
    simpl in H5.
    rewrite H5.
    intuition.
    simpl in H5.
    rewrite H5.
    intuition.
    rewrite H3.
    simpl.
    intuition.
    rewrite H3.
    simpl.
    intuition.
    rewrite H3.
    simpl.
    intuition.
}
intros.
apply (proj1 (H l1 l2 a H0 H1)).
Qed.

Lemma isOrder_interaux:
forall (a:Z)(continution:list Z->list Z)(l:list Z),
(forall l',isOrder (a+1) l'->isOrder (a+1) (continution l'))->
(forall a',a'<=a->isOrder a' l->isOrder a' (interLists_aux a continution l)).
intros a continution l H.
induction l.
-
simpl.
split;try auto;try lia.
-
intros a' H1 H2.
simpl.
destruct H2 as [H2 H3].
destruct (Z_dec a a0) as [[G|G]|G];
simpl.
+
assert(isOrder (a + 1) (continution (a0 :: l))).
apply H.
simpl.
split.
lia.
auto.
apply isOrder_aux with (a+1).
lia.
auto.
+
apply IHl.
lia.
apply isOrder_aux with (a0+1).
lia.
auto.
+
subst a0.
split;auto.
Qed.

Lemma isOrder_inter:
forall (l1 l2:list Z) a,(isOrder a l1)->(isOrder a l2)->isOrder a (interLists l1 l2).
(*有序列表的交的有序性*)
intros l1.
induction l1.
-
simpl. auto.
-
intros l2 a0 H.
simpl in *.
destruct H as [H H1].
apply isOrder_interaux;auto.
Qed.

Lemma inter_nil_l:forall l,interLists nil l=nil.
intros. simpl.
auto.
Qed.
(*👆交空列表👇*)
Lemma inter_nil_r:forall l,interLists l nil=nil.
induction l;auto.
Qed.


Lemma inter_prop_aux:
forall (l1:list Z)(a:Z)(continution:list Z->list Z),
isOrder (a+1) l1
->(forall l2 p,isOrder 0 l2->In p (continution l2)<->In p l1/\In p l2)
->(forall l2 p,isOrder 0 l2->In p (interLists_aux a continution l2)<->(a=p\/In p l1)/\In p l2).
intros l1 a continution K H.
induction l2.
-
intros p.
simpl.
intuition.
-
intros p H1.
pose proof (H (a0::l2) p H1).
simpl in H1.
destruct H1 as [H1 H2].
simpl interLists_aux.
assert(isOrder 0 l2)as T.
apply isOrder_aux with (a0+1);auto;lia.
destruct (Z_dec a a0) as [[J|J]|J].
+
rewrite H0.
assert(In p (a0 :: l2)->~(a=p)). {
    unfold not.
    intros.
    simpl in H3.
    destruct H3.
    lia.
    assert(a0+1<=p).
    apply isOrder_range with (l2);auto;lia.
    lia.
}
intuition.
+
assert(isOrder 0 l2).
apply isOrder_aux with (a0+1);auto;lia.
rewrite IHl2;auto.
assert(a0=p->~(In p l1\/a=p)). {
    unfold not.
    intros M1 M2.
    destruct M2.
    assert(a+1<=p).
    apply isOrder_range with l1;auto.
    lia.
    lia.
}
simpl.
intuition.
+
simpl.
rewrite H;auto.
subst a0.
intuition.
Qed.

Lemma inter_prop:
forall (l1 l2:list Z)(a:Z),(isOrder 0 l1)->(isOrder 0 l2)->(In a (interLists l1 l2))<->(In a l1)/\(In a l2).
(*交的正确性证明*)
induction l1.
-
intros.
rewrite inter_nil_l.
simpl.
intuition.
-
intros.
simpl.
simpl in H.
destruct H as [H1 H2].
apply inter_prop_aux;auto.
intros l0 p J.
apply IHl1;auto.
apply isOrder_aux with (a+1);auto;lia.
Qed.

Lemma remove_nil_l:forall l,removeLists nil l=l.
simpl. auto.
Qed.
(*👆空列表差运算👇*)
Lemma remove_nil_r:forall l,removeLists l nil=nil.
induction l;auto.
Qed.

Lemma isOrder_removeaux:
forall (a:Z)(continution:list Z->list Z)(l:list Z),
(forall l',isOrder (a+1) l'->isOrder (a+1) (continution l'))->
(forall a',a'<=a->isOrder a' l->isOrder a' (removeLists_aux a continution l)).
intros a continution l H.
induction l.
-
simpl.
auto.
-
intros.
simpl.
destruct (Z_dec a a0) as [[J|J]|J].
+
apply isOrder_aux with (a+1);try lia.
apply H.
simpl.
simpl in H1.
intuition.
+
simpl.
simpl in H1.
destruct H1 as [H1 H2].
split;try lia.
apply IHl;try lia;auto.
+
subst a0.
apply isOrder_aux with (a+1);try lia.
apply H.
simpl in H1.
intuition.
Qed.

Lemma isOrder_remove:
forall (l1 l2:list Z) a,(isOrder a l1)->(isOrder a l2)->isOrder a (removeLists l1 l2).
(*差的有序性证明*)
induction l1.
-
simpl.
auto.
-
simpl.
intros.
simpl in H.
destruct H as [H H2].
apply isOrder_removeaux;try lia;auto.
Qed.

Lemma remove_prop_aux:
forall (l1:list Z)(a:Z)(continution:list Z->list Z),
isOrder (a+1) l1
->(forall l2 p,isOrder 0 l2->In p (continution l2)<->~In p l1/\In p l2)
->(forall l2 p,isOrder 0 l2->In p (removeLists_aux a continution l2)<->a<>p/\~In p l1/\In p l2).
intros l1 a continution H H0.
induction l2.
-
simpl.
intuition.
-
intros.
simpl.
pose proof (H0 (a0::l2) p H1).
simpl in H1.
destruct H1 as [H1 H3].
assert(isOrder 0 l2). {
    apply isOrder_aux with (a0+1);
    auto.
    lia.
}
pose proof (IHl2 p H4).
pose proof (H0 l2 p H4).
destruct (Z_dec a a0) as [[J|J]|J].
+
rewrite H2.
simpl.
assert(a=p->~(a0 = p \/ In p l2)). {
    intros K.
    unfold not.
    intros [G|G].
    lia.
    assert(a0+1<=p).
    apply isOrder_range with l2;auto.
    lia.
}
intuition.
+
simpl.
rewrite H5.
assert(a0=p->a<>p)by lia.
assert(a0=p->~In p l1). {
    intros K.
    unfold not.
    intros G.
    assert(a+1<=p).
    apply isOrder_range with l1;auto.
    lia.
}
intuition.
+
rewrite H6.
subst a0.
assert(In p l2->a<>p). {
    intros K.
    assert(a+1<=p).
    apply isOrder_range with l2;auto.
    lia.
}
intuition.
Qed.

Lemma remove_prop:
forall (l1 l2:list Z)(a:Z),(isOrder 0 l1)->(isOrder 0 l2)->In a (removeLists l1 l2)<->~In a l1/\In a l2.
(*差的正确性证明*)
induction l1.
-
simpl.
intuition.
-
intros.
simpl.
destruct H as [H1 H2].
assert(~ (a = a0 \/ In a0 l1) /\ In a0 l2<->a<>a0/\~In a0 l1/\In a0 l2)by intuition.
rewrite H.
apply remove_prop_aux;auto.
intros.
apply IHl1;auto.
apply isOrder_aux with (a+1);auto;lia.
Qed.

Lemma succ_double_aux:forall x y,x<y<->2*x+1<2*y. lia. Qed.
Lemma double_aux:forall x y,x<y<->2*x<2*y. lia. Qed.
Lemma lor_pos_aux:forall x y,Z.pos (Pos.lor x y)=Z.lor (Z.pos x) (Z.pos y).
auto. Qed.
Lemma land_pos_aux:forall x y,Z.of_N (Pos.land x y)=Z.land (Z.pos x) (Z.pos y).
auto. Qed.
Lemma Nsucc_double_aux:forall x,Z.of_N(Pos.Nsucc_double x)=2*(Z.of_N x)+1. lia. Qed.
Lemma Ndouble_aux:forall x,Z.of_N(Pos.Ndouble x)=2*Z.of_N (x). lia. Qed.

Lemma lor_close:forall (n:nat)(x1 x2:Z),0<=x1<two_power_nat n->0<=x2<two_power_nat n->0<=Z.lor x1 x2<two_power_nat n.
(*逻辑或的封闭性*)
intros n.
induction n.
-
assert(two_power_nat 0%nat=1)by auto.
rewrite H.
intros.
assert(x1=0)by lia.
assert(x2=0)by lia.
subst x1 x2.
simpl.
lia.
-
intros.
destruct H0 as[G0 G1].
destruct H as[H0 H1].
split.
apply Z.lor_nonneg.
auto.
destruct x1;destruct x2;try lia;
try rewrite Z.lor_0_l;
try rewrite Z.lor_0_r;
auto.
destruct p;destruct p0;
simpl;rewrite two_power_nat_S in *;
try rewrite->Pos2Z.pos_xI in *;
try apply->succ_double_aux;
try rewrite lor_pos_aux;
try apply IHn;
try lia.
rewrite Pos2Z.pos_xO in *.
apply->double_aux.
rewrite lor_pos_aux.
apply IHn;
lia.
Qed.

Lemma land_two_p_aux:forall x y,Z.of_N x=Z.pos y->Z.of_N (Pos.Ndouble x)=Z.pos (y~0).
lia.
Qed.

Lemma land_two_p_aux2:forall x y,Z.of_N(Pos.land x y)=Z.land (Z.pos x)(Z.pos y).
simpl.
auto.
Qed.

Lemma land_two_p_aux3:forall x y,Z.of_N(Pos.ldiff x y)=Z.land (Z.neg (Pos.succ y))(Z.pos x).
intros.
simpl.
rewrite Pos.pred_N_succ.
auto.
Qed.


Lemma land_two_p:forall p x, 0<=p->Z.land x (two_p p)<>0<->Z.land x (two_p p)=two_p p.
(*x逻辑与一个2的幂只有两种结果，要么是0，要么是2的幂*)
intros p x H.
generalize x.
set (r:=Z.to_nat p).
replace p with (Z.of_nat r) in *;try lia.
rewrite<-two_power_nat_two_p.
generalize dependent r.
clear p.
induction r.
-
intros.
unfold two_power_nat.
simpl.
intros.
split;try lia.
destruct x0;simpl;try lia;
destruct p;simpl;try lia.
destruct (Pos.pred_double p);simpl;try lia.
-
intros.
assert(two_power_nat (S r)>0). {
    apply two_power_nat_pos.
}
split;try lia.
intros G.
unfold two_power_nat in *.
simpl (shift_nat (S r) 1) in *.
destruct x0; try lia.
simpl in *.
lia.
+
destruct p;
simpl in G;simpl;
try apply land_two_p_aux;
try rewrite land_two_p_aux2;
try apply IHr;
simpl;
try lia.
+
simpl.
simpl in G.
destruct (Pos.pred_N p).
lia.
destruct p0;
try apply land_two_p_aux;
try rewrite land_two_p_aux3;
try apply IHr;try lia;
simpl;
rewrite Pos.pred_N_succ;
lia.
Qed.

Lemma land_close:forall (n:nat)(x1 x2:Z),0<=x1<two_power_nat n->0<=Z.land x1 x2<two_power_nat n.
(*逻辑与的封闭性*)
intros n.
induction n.
-
assert(two_power_nat 0%nat=1)by auto.
rewrite H.
intros.
assert(x1=0)by lia.
subst x1.
simpl.
lia.
-
intros.
destruct H as[H0 H1].
split.
apply Z.land_nonneg.
auto.
destruct x1;destruct x2;try lia;auto.
rewrite Z.land_0_r. lia.
+
destruct p;destruct p0;simpl;try lia;
try rewrite two_power_nat_S in *;
try rewrite Nsucc_double_aux;
try rewrite Ndouble_aux;
try apply->succ_double_aux;
try apply->double_aux;
try rewrite->Pos2Z.pos_xI in *;
try rewrite land_pos_aux;
try apply IHn;
try lia.
+
destruct p;simpl;destruct (Pos.pred_N p0);
try rewrite two_power_nat_S in *;try lia;
try destruct p1;
try rewrite->Pos2Z.pos_xI in *;
try rewrite Nsucc_double_aux;
try rewrite Ndouble_aux;
try apply->succ_double_aux;
try apply->double_aux;
try rewrite land_two_p_aux3;
try rewrite Z.land_comm;
try apply IHn;
try lia.
destruct p;try lia.
Qed.

Lemma lor_neq_0_iff:forall a b,a<>0\/b<>0<->(Z.lor a b)<>0.
intros.
assert(Z.lor a b = 0 <-> a = 0 /\ b = 0).
apply Z.lor_eq_0_iff.
split.
-
intros.
assert(~(a=0/\b=0))by intuition.
intuition.
-
intros.
assert(~(a=0/\b=0))by intuition.
tauto.
Qed.

Lemma union_complete:
forall (n:nat)(x1 x2:Z)(l1 l2:list Z),
(bitmap_complete n x1 l1)->(bitmap_complete n x2 l2)->(bitmap_complete n (Z.lor x1 x2) (unionLists l1 l2)).
(*逻辑或操作对应了列表的并操作*)
unfold bitmap_complete.
intros.
destruct H as [G1 [G2 G3]].
destruct H0 as [K1 [K2 K3]].
split.
apply lor_close;auto.
split.
apply isOrder_union;auto.
assert(0 <= Z.lor x1 x2 < two_power_nat n).
apply lor_close;auto.
assert(isOrder 0 (unionLists l1 l2)).
apply isOrder_union;auto.
apply<-(powerserie_complete n);auto.
intros.
rewrite union_prop;auto.
assert(In p l1<->Z.land x1 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
assert(In p l2<->Z.land x2 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
rewrite H2.
rewrite H3.
rewrite Z.land_lor_distr_l.
apply lor_neq_0_iff.
Qed.

Lemma land_distr:forall x y z,Z.land (Z.land x y) z=Z.land (Z.land x z) (Z.land y z).
intros.
assert(z=Z.land z z). {
    rewrite Z.land_diag.
    auto.
}
rewrite H at 1.
rewrite Z.land_assoc.
rewrite<-Z.land_assoc with x y z.
rewrite (Z.land_comm y z) at 1.
rewrite Z.land_assoc.
rewrite<-Z.land_assoc with (Z.land x z) y z.
auto.
Qed.


Lemma land_zero_rev:forall x y,Z.land x y<>0->x<>0/\y<>0.
intros x y H.
unfold not.
split;intros P;
rewrite P in H.
rewrite Z.land_0_l in H.
lia.
rewrite Z.land_0_r in H.
lia.
Qed.

Lemma inter_complete:
forall (n:nat)(x1 x2:Z)(l1 l2:list Z),
(bitmap_complete n x1 l1)->(bitmap_complete n x2 l2)->(bitmap_complete n (Z.land x1 x2) (interLists l1 l2)).
(*逻辑与操作对应了列表的交操作*)
unfold bitmap_complete.
intros.
destruct H as [G1 [G2 G3]].
destruct H0 as [K1 [K2 K3]].
split.
apply land_close;auto.
split.
apply isOrder_inter;auto.
assert(0 <= Z.land x1 x2 < two_power_nat n).
apply land_close;auto.
assert(isOrder 0 (interLists l1 l2)).
apply isOrder_inter;auto.
apply<-(powerserie_complete n);auto.
intros.
rewrite inter_prop;auto.
assert(In p l1<->Z.land x1 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
assert(In p l2<->Z.land x2 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
rewrite H2.
rewrite H3.
rewrite land_distr.
split.
-
repeat rewrite land_two_p;auto.
intros [M1 M2].
rewrite M1.
rewrite M2.
rewrite Z.land_diag.
assert(two_p p>0). {
    apply two_p_gt_ZERO.
    auto.
}
lia.
-
intros M.
apply land_zero_rev.
auto.
Qed.

Lemma bitmap_0:forall n,bitmap_complete n 0 nil.
(*0对应nil*)
unfold bitmap_complete.
simpl.
intros n.
pose proof (two_power_nat_pos n).
lia.
Qed.

Lemma bitmap_unit:forall n x,0<=x<Z.of_nat n->bitmap_complete n (two_p x) (x::nil).
(*单个元素x对应2^x*)
unfold bitmap_complete.
intros n x H.
split;try split.
-
rewrite two_p_correct.
apply Z.pow_nonneg.
lia.
-
rewrite two_p_correct.
rewrite two_power_nat_equiv.
apply Z.pow_lt_mono_r;lia.
-
simpl.
lia.
-
simpl.
lia.
Qed.

Lemma bitmap_in:forall n x l,bitmap_complete n x l->(forall p,0<=p->In p l<->(Z.land x (two_p p))<>0).
(*用bitmap_complete再说一遍，bitmap_complete描述了x和l的对应性*)
intros n x l H.
unfold bitmap_complete in H.
destruct H as [H1 [H2 H3]].
apply->(powerserie_complete n);auto.
Qed.

Lemma bitmap_range:forall n x l,bitmap_complete n x l->(forall p,In p l->0<=p<Z.of_nat n).
(*bitmap_complete限制了l中元素的范围*)
intros n x l H.
unfold bitmap_complete in H.
destruct H as [H1 [H2 H3]].
intros p Hp.
apply Z_one_bits_range with x.
assert(l=Z_one_bits n x 0). {
    apply<-powerserie_complete_aux;simpl;auto;try lia;try intuition.
}
rewrite<-H.
auto.
Qed.

Lemma bitmap_unique_1:forall n x l1 l2,bitmap_complete n x l1->bitmap_complete n x l2->l1=l2.
(*bitmap_complete对于同一个x只能有同一个l*)
unfold bitmap_complete.
intros.
destruct H0 as [G0 [G1 G2]].
destruct H as [H0 [H1 H2]].
apply isOrder_eq with 0;auto.
intros p K.
rewrite (bitmap_in n x);try unfold bitmap_complete;auto;try tauto.
rewrite (bitmap_in n x);try unfold bitmap_complete;auto;try tauto.
Qed.


Lemma bitmap_unique_x:forall n x1 x2 l,bitmap_complete n x1 l->bitmap_complete n x2 l->x1=x2.
(*bitmap_complete对于同一个l只能有同一个x*)
unfold bitmap_complete.
intros.
destruct H0 as [G0 [G1 G2]].
destruct H as [H0 [H1 H2]].
subst x1.
subst x2.
auto.
Qed.

Lemma double_eq_aux:forall x y,x=y<->2*x=2*y. lia. Qed.
Lemma succ_double_eq_aux:forall x y,x=y<->2*x+1=2*y+1. lia. Qed.
Lemma ldiff_aux:forall x y,Z.of_N(Pos.ldiff x y)=Z.ldiff (Z.pos x)(Z.pos y). simpl. auto. Qed.

Lemma ldiff_aux2:forall x y,Z.of_N(Pos.land x y)=Z.ldiff (Z.pos x)(Z.neg (Pos.succ y)).
intros.
simpl.
rewrite Pos.pred_N_succ.
auto.
Qed.

Lemma ldiff_land_0:forall x y,Z.land x y=0<->Z.ldiff x y=x.
split.
-
intros H.
assert(Z.lor (Z.ldiff x y) 0 = x). {
    rewrite<-H.
    apply Z.lor_ldiff_and.
}
rewrite Z.lor_0_r in H0.
auto.
-
intros H.
rewrite<-H.
apply Z.land_ldiff.
Qed.


Lemma remove_complete:
forall (n:nat)(x1 x2:Z)(l1 l2:list Z),
(bitmap_complete n x1 l1)->(bitmap_complete n x2 l2)->(bitmap_complete n (Z.land x2 (Z.lnot x1)) (removeLists l1 l2)).
(*a&(~b)操作对应了列表的差操作*)
unfold bitmap_complete.
intros.
destruct H as [G1 [G2 G3]].
destruct H0 as [K1 [K2 K3]].
split.
apply land_close;auto.
split.
apply isOrder_remove;auto.
assert(0 <= Z.land x2 (Z.lnot x1) < two_power_nat n).
apply land_close;auto.
assert(isOrder 0 (removeLists l1 l2)).
apply isOrder_remove;auto.
apply<-(powerserie_complete n);auto.
intros.
rewrite remove_prop;auto.
assert(In p l1<->Z.land x1 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
assert(In p l2<->Z.land x2 (two_p p)<>0). {
    apply (powerserie_complete n);auto.
}
rewrite H2.
rewrite H3.
rewrite land_distr.
assert(two_p p>0). {
    apply two_p_gt_ZERO.
    auto.
}
split.
-
assert(~ Z.land x1 (two_p p) <> 0<->Z.land x1 (two_p p)=0)by tauto.
rewrite H5.
intros [M1 M2].
assert(Z.land (Z.lnot x1) (two_p p)=two_p p). {
    apply land_two_p;auto.
    rewrite Z.land_comm.
    rewrite<-Z.ldiff_land.
    assert(Z.ldiff (two_p p) x1=two_p p).
    apply ldiff_land_0;auto;try lia.
    rewrite Z.land_comm. auto.
    lia.
}
rewrite H6.
rewrite land_two_p in M2;auto.
rewrite M2.
rewrite Z.land_diag.
lia.
-
intros M.
assert(Z.land x2 (two_p p)<>0/\Z.land (Z.lnot x1) (two_p p)<>0).
apply land_zero_rev;
auto.
destruct H5 as [H5 H6].
split;auto.
rewrite land_two_p in H6;auto.
rewrite Z.land_comm in H6.
rewrite<-Z.ldiff_land in H6.
assert(Z.land (two_p p) x1=0). {
    apply<-ldiff_land_0.
    auto.
}
rewrite Z.land_comm.
intuition.
Qed.

Lemma testbit_land:
forall x p,0<=p->Z.testbit x p=true<->Z.land x (Z.shiftl 1 p)<>0.
(*由于大家之前很多谓词用了testbit，所以提供了一个testbit x p与x&(1<<p)!=0的等价性的证明*)
intros.
rewrite Z.testbit_odd.
generalize dependent x.
destruct p.
-
intros x.
unfold Z.shiftr.
unfold Z.shiftl.
simpl.
pose proof (land_1_odd x).
assert(Z.odd x = true<->Z.odd x <> false). {
    destruct (Z.odd x);intuition.
}
tauto.
-
unfold Z.shiftr.
unfold Z.shiftl.
simpl.
induction p using Pos.peano_ind.
+
simpl.
intros x.
assert(Z.odd (Z.div2 x) = true<->Z.land (Z.div2 x) 1<>0). {
    pose proof (land_1_odd (Z.div2 x)).
    assert(Z.odd (Z.div2 x) = false<->Z.odd (Z.div2 x) <>true). {
        destruct (Z.odd (Z.div2 x));
        intuition.
    }
    tauto.
}
rewrite H0.
assert(2=Z.shiftl 1 1)by auto.
rewrite H1.
rewrite land_shiftl_1.
rewrite<-shiftl_mul_2.
lia.
+
intros x.
repeat rewrite Pos.iter_succ.
rewrite shiftl_mul_2.
rewrite land_shiftl_1.
rewrite<-shiftl_mul_2.
assert(forall k,2*k<>0<->k<>0)by lia.
rewrite H0.
rewrite<-IHp;try lia.
rewrite<-Pos.iter_succ_r.
rewrite<-Pos.iter_succ.
intuition.
-
lia.
Qed.