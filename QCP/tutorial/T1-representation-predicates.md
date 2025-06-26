# Define a Representation Predicate

To verify a program with our tool, we should first formalize how data structures are stored in memory. Predicates that characterize the shape of data structures in memory are called *representation predicates*. We show how to define such a predicate for singly linked lists in the following.

## Example: singly linked lists

The following defines the "singly linked list" data structure in C.

```c
struct list {
 int data;
 struct list *next;
};
```

Its corresponding representation predicate defined in Coq is shown next.

```Coq
Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | z :: l0 => [| x <> NULL |] &&
                 EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> z ** 
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.
```

Informally, `sll x l` is an `Assertion` stating that `x` is the address of the head of a list storing integers in `l`. Here `Assertion` is the type of C memory predicates. They

- can describe what is stored in memory;
- can**not** contain information of local variables;
- can contain information of global variables;
- can talk about types defined by `struct`, `union`, and `typedef`;
- can reach the granularity of bytes.

Syntax (or notations) are explained as follows.

- If `x` is an Coq term of type `addr`, then `x # "list"` denotes a pointer to C type `(struct) list` with the same value as `x` (`(struct list *) x` in C);
- If `p` denotes a pointer to `struct A`, then `p ->ₛ "data"` denotes the member `data` (in `A`) that `p` points to (`p -> data` in C);
- If `x` is a left value (with similar syntax restrictions as in C), then `&x` denotes its address;
- If `p` denotes a pointer or `p` has type `addr`, then `p # Int |-> v` means that the address `p` stores the 4-byte integer `v`;
- If `p` denotes a pointer or `p` has type `addr`, then `p # Prt |-> v` means that the address `p` stores the pointer `v`.

- `emp` means there is nothing in memory;
- `EX` is existential quantification;
- `&&` is conjunction;
- `**` is separation conjunction;
- `[| .. |]` embeds a Coq, or memory-unrelated, proposition.

Consider the memory layout

```
0x0040  0
0x0044  0x0100
0x0100  1
0x0104  0x0108
0x0108  2
0x010c  0x0000
```

and assume `x = 0x0040` and `y = 0x100`. Then we have the tables

| Coq term                   | Coq type    | C counterpart  | value     |
|:---------------------------|:------------|:---------------|:----------|
| `x`                        | `addr`      | `x`            | 0x0040    |
| `x # "list"`               | right value | `x`            | 0x0040    |
| `x # "list" ->ₛ "data"`    | left value  | `x -> data`    | undefined |
| `x # "list" ->ₛ "next"`    | left value  | `x -> next`    | undefined |
| `&(x # "list" ->ₛ "data")` | right value | `&(x -> data)` | 0x0040    |
| `&(x # "list" ->ₛ "next")` | right value | `&(x -> next)` | 0x0044    |

| Coq term                                                                                                                | Coq type    | True/False |
|:------------------------------------------------------------------------------------------------------------------------|:------------|:-----------|
| `&(x # "list" ->ₛ "data") # Int \|-> 0`                                                                                 | `Assertion` | False \*   |
| `&(x # "list" ->ₛ "data") # Int \|-> 1`                                                                                 | `Assertion` | False      |
| `&(x # "list" ->ₛ "data") # Int \|-> 0 && <br> &(x # "list" ->ₛ "data") # Int \|-> 0`<br>(such duplication never holds) | `Assertion` | False \*   |
| `&(x # "list" ->ₛ "data") # Int \|-> 0 ** <br> &(x # "list" ->ₛ "data") # Int \|-> 0`                                   | `Assertion` | False      |
| `&(x # "list" ->ₛ "data") # Int \|-> 0 ** <br> &(x # "list" ->ₛ "next") # Ptr \|-> y`                                   | `Assertion` | False \*   |
| `sll x [0; 1; 2]`                                                                                                       | `Assertion` | True       |

Here "False" marked by \* means that the assertion is true on some portion of the memory.

## New predicates based on old ones

We can reuse defined predicates when defining new ones. For example, the following predicate `sllb` characterize a second-order pointer to a list.

```
Definition sllb (x: addr) (l: list Z): Assertion :=
  EX y: addr, x # Ptr |-> y ** sll y l.
```
