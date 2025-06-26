# Function Call

## Symbolic execution of function calls

We want to explain how we symbolically execute a function call. Consider the `reverse` function.

```c
struct list * reverse(struct list *p)
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/;
```

We call `reverse` as in the following.

```c
...
/*@ Assert 
    data_at(&q, q_v) * sll(q_v, l0) */
q = reverse(q);
...
```

The symbolic execution process is illustrated in the following.

![img1](T8_img1.svg)

Our tool will
1. Automatically (we shall explain how this is done) instantiate the logical variable `l` in the specification with `l0`;
2. Automatically separate the memory part of the program state into two parts: (1) one that matches the precondition (lets call it pre_mem) and (2) the rest of it (called the *frame*). In this case they are `sll(q_v, l0)` and `data_at(&q, q_v)`, respectively;
3. Append fresh existential variables in the postcondition;
4. Replace pre_mem with the postcondition (replace `sll(q_v, l0)` with `sll(ret, rev(l0))`) while keeping the frame intact;
5. Set the value store on address `%q` to the return value `ret`.

The example is special in that we do not have logical propositions in the pre- and postcondition. If we have them in the precondition, we require (in the VC) that they are implied; if we have them in the postcondition, we add them along with existential variables.

## Verifying the precondition

We explain how the tool ensures that the precondition of a function holds. Consider the following pieces of C code:

```c
int length(struct list *p)
/*@ With (l: list Z)
    Require Zlength(l) <= INT_MAX && sll(p, l)
    Ensure __return == Zlength(l) && sll(p@pre, l)
*/;
```

```c
...
/*@ Assert
    Zlength(cons(0, l0)) <= 100 && 
    data_at(&x, 0) * data_at(&q, q_v) * sll(q_v, l0) */
x = length(q);
...
```

We instantiate logical variables and separate the memory by consecutively rewrite the entailment `P |-- Q` based on patterns seen on both sides. The rewriting rules (which we call *strategies*) are specified by the user. We will explain how to write yours in T7; For now, let us see how the rewriting works.

```
Zlength(cons(0, l0)) <= 100 && data_at(&x, 0) * data_at(&q, q_v) * sll(q_v, l0)
|--
exists l,
Zlength(l) <= INT_MAX && sll(q_v, l)
```

According to strategies in `common.strategies` and `sll.strategies`, the tool first instantiates `l` on the right-hand side with `l0`.

```
Zlength(cons(0, l0)) <= 100 && data_at(&x, 0) * data_at(&q, q_v) * sll(q_v, l0)
|--
Zlength(l0) <= INT_MAX && sll(q_v, l0)
```

Then it cancels `sll(q_v, l0)` on both sides.

```
Zlength(cons(0, l0)) <= 100 && data_at(&x, 0) * data_at(&q, q_v)
|--
Zlength(l0) <= INT_MAX
```

Now there is nothing about memory on the right-hand side. The left-hand side is the frame (as you can imagine, the frame might not be directly presented in the original assertion, but instead transformed from part of it). We do not know exactly what pre_mem is, but it does not matter as we can finish by appending the left-hand side with the postcondition.

```
exists ret,
Zlength(cons(0, l0)) <= 100 && ret == Zlength(l0) &&
data_at(&x, ret) * data_at(&q, q_v) * sll(q_v, l0)
```

At this stage, since we have our new program state, we can continue symbolic execution. To ensure correctness, we also require (as a VC) logical propositions left can be proved.

```
Zlength(cons(0, l0)) <= 100 && data_at(&x, 0) * data_at(&q, q_v) * sll(q_v, l0)
|--
Zlength(l0) <= INT_MAX
```

Note that this time the left-hand side is the original program state.

## The `where` clause

Sometimes our tool cannot instantiate variables correctly. We can instantiate some of them manually using the `where` clause:

```c
function_call(...) /*@ where para0 = var0, para1 = var1 */;
```

For example, we can rewrite the call in the previous section to

```c
...
/*@ Assert 
    data_at(&q, q_v) * sll(q_v, l0) */
  q = reverse(q) /*@ where l = l0 */;
...
```

We can also specify (implicit) type arguments:

```c
function_call(...) /*@ where para0 = var0, para1 = var1; typePara0 = type0, typePara1 = type1 */;
```

For example, consider a polymorphic version of `reverse`.

```c
struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
```

```c
...
/*@ Assert 
    data_at(&q, q_v) * sll(q_v, l0) */
  q = reverse(q) /*@ where l = l0, storeA = storeInt; A = Z */;
...
```

## Multiple specifications

Sometimes we want a function to have multiple specifications, each representing different abstraction levels or different input cases. For example, for a function `insertion_sort` we want to verify that it implements some function `coq_insertion_sort` in Coq.

```c
struct list * insertion_sort(struct list * x)
  /*@ With l
      Require sll(x, l)
      Ensure sll(__return, coq_insertion_sort(l))
   */;
```

As a user of the function, we also want a specification directly specifying its behaviour.

```c
struct list * insertion_sort(struct list * x)
  /*@ With l
      Require sll(x, l)
      Ensure exists l0,
               Permutation(l, l0) && increasing(l0) &&
               sll(__return, l0)
   */;
```

Our tool supports multiple specifications.

```c
struct list * insertion_sort(struct list * x)
  /*@ high_level_spec <= low_level_spec
      With l
      Require sll(x, l)
      Ensure exists l0,
               Permutation(l, l0) && increasing(l0) &&
               sll(__return, l0)
   */;

struct list * insertion_sort(struct list * x)
  /*@ low_level_spec
      With l
      Require sll(x, l)
      Ensure sll(__return, coq_insertion_sort(l))
   */
{
  ...
}
```

Here `low_level_spec` and `high_level_spec` are names of specifications. `low_level_spec` is used to verify the function body; `high_level_spec` is derivable from `low_level_spec` (`high_level_spec <= low_level_spec`). We stipulate that only one specification is directly verified against the function body, while others should be derivable from it.

We use the following syntax to specify the specification to use.

```c
y = insertion_sort(x) /*@ where (high_level_spec) l = l */;
```

We talked about derivation between specifications. They are separation-logic entailments (again) which look like the following.

```coq
Definition insertion_sort_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (l: (list Z)) ,
  (sll x_pre l )
|--
EX (l_2: (list Z)) ,
  ((sll x_pre l_2 ))
  **
  ((EX retval_2,
  (sll retval_2 (coq_insertion_sort l_2) ))
  -*
  (EX l0 retval,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll retval l0 )))
.
```

Here `-*` is the *magic wand*. `P -* Q` means that the memory, when appended with another portion of memory that satisfying `P`, will satisfy `Q`. The entailment corresponding to "`low_level` derives `high_level`" has the following pattern:

```
high_pre |-- low_pre ** (low_post -* high_post) 
```

To see why it makes sense, consider some memory satisfying `high_pre`. Then by the previous entailment, it also satisfies `low_pre ** (low_post -* high_post)`. After a function call, `low_pre` is substituted for `low_post`: `low_post ** (low_post -* high_post)`, which implies `high_post` trivially.

A proof of specification derivation typically involves the following property of `-*`.

```coq
Theorem derivable1_wand_sepcon_adjoint:
  forall x y z: Assertion, 
    x ** y |-- z <-> x |-- y -* z.
```

In the previous example, after `pre_process`, `Exists l`, and `entailer!`, we have the proof goal

```
emp 
|--
((EX retval_2,
  (sll retval_2 (coq_insertion_sort l) ))
  -*
  (EX l0 retval,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll retval l0 )))
```

Applying `derivable1_wand_sepcon_adjoint` results in

```
emp ** (EX retval_2,
  (sll retval_2 (coq_insertion_sort l) ))
|--
(EX l0 retval,
  [| (Permutation l l0 ) |] 
  &&  [| (increasing l0 ) |]
  &&  (sll retval l0 ))
```

which is familiar.

## Conclusion

Roughly speaking, when symbolically executing a function call, we
- make sure the function precondition holds. That is
  - Instantiate the logical variables;
  - Automatically separate the memory part of the program state into two parts: (1) one that matches the precondition (lets call it pre_mem) and (2) the rest of it (called the *frame*);
  - Require (as a VC) that logical propositions after rewriting can be proved.
- generate the assertion after the function call. That is
  - Append fresh existential variables in the postcondition;
  - Append logical propositions in the postcondition;
  - Replace pre_mem with the postcondition  while keeping the frame intact;
  - Set the value store on address `%q` to the return value `ret`;
  - Set the value of the call expression to the return value.

Note that
- If our tool cannot clear the memory part of the right-hand side, symbolic execution fails. It can be solved by instantiating variables manually and/or by adding more strategies.
- A function can have multiple specifications. Only one specification is directly verified against the function body, while others should be derivable from it. The `where` clause can specify the specification to use at call site.
