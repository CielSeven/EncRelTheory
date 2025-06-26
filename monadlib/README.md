# A Library for Monadic Programs

This repository contains the Coq development for state relation monad. It aims to provide a formal framework for naturally specifying and verifying algorithms. Its stateless and errorful variants -- set monad and monad with error -- are also included.

For more information, feel free to check out the paper ["A Formal Framework for Naturally Specifying and Verifying Sequential Algorithms"](https://arxiv.org/abs/2504.19852).

## Requirements

- Coq = 8.15.2
- [sets](https://bitbucket.org/qinxiang-SJTU/sets/src/539782edb2d8691ebfdb0a76bdcafac4c9d16f7e/): library for set theory 
- [fixedpoints](https://bitbucket.org/qinxiang-SJTU/fixedpoints/): library for order theory and fixed points

You need to specify the folder path to `sets` and `fixedpoints` in a file `CONFIGURE` which is used by `Makefile`. 

## Code Structure

```
.
├── SetMonad      # Set Monad
│   ├── Monad.v        # Monad definitions and notations
│   ├── SetBasic.v     # Constructors and properties
│   ├── FixpointLib.v  # Lemmas and tactics for fixpoint theorem and loop unfold
│   └── SetHoare.v     # Hoare logic and tactics
├── StateRelMonad    # State Relation Monad
│   ├── StateRelBasic.v    # Constructors and properties
│   ├── StateRelHoare.v    # Hoare logic and tactics
│   ├── FixpointLib.v      # Lemmas and tactics for fixpoint theorem and loop unfold
│   └── safeexec_lib.v     # library for relational Hoare Logic
└── MonadErr          # State Relation Monad with Error Handling
    ├── MonadErrBasic.v    # Basic constructors and properties
    ├── MonadErrLoop.v     # Loop constructors and properties & fixpoint lemmas
    ├── MonadErrHoare.v    # Hoare logic and tactics
    └── monadsafe_lib.v    # library for relational Hoare Logic
```

## State Relation Monad

We model a program as a *state relation monad*, defined as a ternary relation over $\tt{\Sigma \times A \times \Sigma}$, where $\tt{\Sigma}$ is the type of the program state and $\tt{A}$ is the type of the return value. This relation encodes the denotational semantics of a nondeterministic program $c$, $(s_1, r, s_2) \in c$ means that, starting from the state $s_1$, program $c$ may terminate at $s_2$ and return $r$.


### Operators 

0. remember to import notations before definitions:
   
   ```Coq
   Import MonadNotation.
   Local Open Scope monad.
   ```

1. <span style="color:green"> ret </span> $a$  ： always yields the singleton set of the transition whose output is $a$ without changing the state.

$$ (s_1, r, s_2) \in \texttt{ret}(a)  \iff r = a \ \land \ s_1 = s_2 $$

2. <span style="color:green"> bind </span> $m$ $f$  ： composes all transitions of $m$ with a function $g$ to generate new transitions. It can be denoted as `x <- m ;; f x`.

$$(s_1, b, s_3) \in \texttt{bind}(c, f) \iff 
       \exists\  a \ s_2, \  (s_1, a, s_2) \in c \ \land \ (s_2, b, s_3) \in f(a)$$ 

3. <span style="color:green"> assume </span> $P$ (or <span style="color:green"> test </span> $P$) ：succeeds and returns the unit value tt  without changing the state if and only if the predicate $P$ (on program states) holds.
   
4. <span style="color:green"> assume!! </span> $P$ (or <span style="color:green"> testpure </span> $P$) ：succeeds and returns the unit value tt  without changing the state if and only if the <span style="color:red"> pure </span> condition $P$ holds. 
   
$$\forall P:\mathtt{\Sigma \to} \texttt{Prop},\ (s_1, \texttt{tt}, s_2) \in \texttt{assume}(P) \iff P(s_1) \land s_1 = s_2$$

5. <span style="color:green"> choice </span> $m_1$ $m_2$  ：a nondeterministic choice between two monads.

   $$\texttt{choice}(f, g) := f \cup g$$

#### An example
Below is an example of state relation monad program that computes hailstone numbers.
```coq
Example hailstone: Z -> program unit Z :=
  repeat_break
  (fun (x: Z) =>
    choice
      (assume!! (x <= 1);; break x)
      (choice
        (assume!! (exists k, x = 2 * k);;
        continue (x / 2))
        (assume!! (exists k, k <> 0 /\ x = 2 * k + 1);;
        continue (3 * x + 1)))).
```

---



### Equivalence of state relation monads *"=="*
*==* of state relation monads is defined as equivalence on sets, i.e. mutual inclusion.

##### combine ret with bind :

   1. bind (ret x) m == m x  
   2. bind m (ret x) == m.

   ```Coq
   Lemma bind_ret_left : forall {A B : Type} x (m : A -> program Σ B),
     bind (ret x) m == m x.
   Lemma bind_ret_right  : forall {A : Type} (m : program Σ A),
     x <- m ;; ret x == m.
   ```

##### bind associativity :

   - x <- (y <- c0;; c1 y);; c2 x == y <- c0;; x <- c1 y;; c2 x

   ```Coq
   Lemma bind_assoc {A B C: Type}: 
   forall (c0: program Σ A) (c1: A -> program Σ B) (c2: B -> program Σ C),
      bind (bind c0 c1) c2 == bind c0 (fun x => bind (c1 x) c2).
   ```

##### choice community: 

   1. choice c0 c1 == choice c1 c0

   ```Coq
   Lemma choice_comm {A: Type}:
    forall (c0 c1: program Σ A),
      choice c0 c1 == choice c1 c0.
   ```


##### combine choice with bind : distributive law

   1. x <- (choice c0 c1);; c2 x == choice (x <- c0;; c2 x) (x <- c1;; c2 x)
   2. x <- c0 ;; (choice (c1 x) (c2 x)) == choice (bind c0 c1) (bind c0 c2)

   ```Coq
   Lemma bind_choice_equiv {A B: Type}: 
    forall (c0 c1: program Σ A) (c2: A -> program Σ B),
      x <- (choice c0 c1);; c2 x == choice (x <- c0;; c2 x) (x <- c1;; c2 x).
   Lemma choice_bind_equiv {A B: Type}: 
    forall (c0: program Σ A) (c1 c2: A -> program Σ B),
      x <- c0 ;; (choice (c1 x) (c2 x)) == choice (bind c0 c1) (bind c0 c2).
   ```
##### others see Section monad_equiv_lemmas.

## Common Tactics

Monad related:

- `unfold_monad`: unfold definitions of `ret` and `bind`.
- `monad_law`: apply monad laws to simply a monad.
- `monad_equiv`: try to prove two monads are equivalent.

Hoare logic related:

- `hoare_bind H`: use `H` as the strongest postcondition to proceed.
- `hoare_conj`: split the conjunction in the postcondition of target Hoare triple.
- `hoare_step`: use Hoare rules to proceed for one step.
- `hoare_auto`: use Hoare rules to proceed as far as possible.

Fixpoint related:

- `mono_cont_auto`: automatically prove some monad program is monotone and continuous.
