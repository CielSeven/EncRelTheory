# Proving Verification Conditions

We take the verification conditions in T5 as an example to show how to prove VCs in Coq.

To prove separation-logic entailments in Coq, we mainly use tactics for separation logic such as `sep_apply`, `Intros`, `Exists`, `entailer!`, and built-in Coq tactics. Some VCs can be proved directly, and others may need lemmas concerning representation predicates.

## Proof of the first VC

The first VC can be proved directly. To prove

```
sll p l |-- EX l1 l2 : list Z, [|l = rev l1 ++ l2|] && sll 0 l1 ** sll p l2
```

, we should instantiate existential variables `l1` and `l2` with `nil` and `l`, respectively. We use the tactic `Exists nil l`, the separation logic counterpart of `exists`. Then our goal turns to

```
sll p l |-- [|l = rev [] ++ l|] && sll 0 [] ** sll p l
```

We can simplify the goal by unfolding `sll` through the tactic `simpl sll`. Then our goal turns to

```
sll p l |-- [|l = rev [] ++ l|] && ([|0 = NULL|] && emp) ** sll p l
```

, which is trivial. We invoke the automatic solver `entailer!` to finish the proof.

## Proof of a lemma

The following lemma will be used in the proof of the third VC.

```
Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- [| l = nil |] && emp.
Proof.
  intros.
  destruct l; simpl sll.
  + entailer!.
  + Intros.
    tauto.
Qed.
```

The proof uses a common pattern: case analysis on whether `l` is empty. When `l = []`, the entailment holds by definition; when `l` is nonempty, we should prove

```
H: x = NULL
----------------------------
[|x <> NULL|] &&
  (EX y : addr,
     &( x # "list" ->ₛ "data") # Int |-> z **
     &( x # "list" ->ₛ "next") # Ptr |-> y ** 
     sll y l) |--
[|z :: l = []|] && emp
```

We should derive contradiction via `[|x <> NULL|]`. We use the tactic `Intros` to move a Coq proposition in the precondition into the Coq context, which turns the goal to

```
H: x = NULL
H0: x <> NULL
----------------------------
EX y : addr,
  &( x # "list" ->ₛ "data") # Int |-> z **
  &( x # "list" ->ₛ "next") # Ptr |-> y ** 
  sll y l |--
[|z :: l = []|] && emp
```

## Proof of the third VC

To prove

```
[|v = 0|] && [|l = rev l1 ++ l2|] && sll w l1 ** sll v l2 |-- sll w (rev l)
```

we first invoke `Intros`.

```
H: v = 0
H0: l = rev l1 ++ l2
----------------------------
sll w l1 ** sll v l2 |-- sll w (rev l)
```

Then we use the previous lemma by the tactic `sep_apply (sll_zero v l2)`. The current goal turns to

```
H: v = 0
H0: l = rev l1 ++ l2
----------------------------
sll w l1 ** ([|l2 = []|] && emp) |-- sll w (rev l)
```

and we have a side condition

```
H: v = 0
H0: l = rev l1 ++ l2
----------------------------
v = 0
```

which are both easy.
