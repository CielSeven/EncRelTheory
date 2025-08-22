# Core formalization cross-reference table (in Directory `EncRelSeq/`)

| Definition / Theorem | Paper | File | Name of formalization | Notation in Rocq |
|----------------------|-------|------|------------------------|------------------|
| Assertion lifting | p. 3, Def. 2 | Basics/relasrt.v | Definition `lift` <br> Definition `Aspec` <br> Definition `Alst` <br> Definition `Ahst` | $\uparrow P$ <br> $[ c ]_h$ <br> $\lfloor{P} \rfloor$ <br> $\lceil{P}\rceil$ |
| Validity of standard Hoare triples | p. 3, Def. 3 | Basics/hoarelogic.v | Definition `valid_triple` | $\vdash_{\forall} \{\{ P \}\} \ c\ \{\{ Q \}\}$ |
| Configuration refinement | p. 9, Def. 7 | Basics/relhoarelogic.v | Definition `config_refinement` | $g_1 \hookrightarrow g_2$ |
| Validity of relaxed relational triples | p. 10, Def. 9 | Basics/relhoarelogic.v | Definition `valid_RelTriples` | $\vdash \langle P\rangle \ c\ \langle Q \rangle$ |
| Decomposition theorem | p. 10, Theo. 11 | Basics/relhoarelogic.v | Theorem `configrefine_decompose` |  |
| Assertion encoding | p. 12, Def. 15 | Basics/encdefs.v | Definition `encode_asrt` | [\| P \|] (X) |
| Correctness theorem | p. 12, Theo. 4 | Basics/encrel.v | Theorem `encoding_correctness` | |
| Encoded assertion transformation | p. 13 (a–d) | Basics/encdefs.v | Lemma `encode_exp_equiv` <br> Lemma `encode_prop_andp` <br> Lemma `encode_alst_and` <br> Lemma `encode_orp` | |
| Execution predicate | p. 14, Def. 18 | Basics/encdefs.v | Definition `Exec` | |
| Encoded decomposed relational triples |  | Basics/enc_rules.v | Lemma `reltriple_triple_equiv` | |
| Encoded relational proof rules | Sec. 6 | Basics/enc_rules.v | Lemma `high_focus_as_conseqpre` <br> Lemma `low_focus_as_seq` <br> Lemma `comp_fc_as_conseq` <br> Lemma `comp_refine_as_conseq` <br> Lemma `comp_fc_as_conseq_convenient` | |
| Execution predicate proof rules | Fig. 10 | Basics/safeexec_lib.v | | |

---

# Case Studies (Directory `Examples/`)

We provide four case studies that reside in the `Examples/` directory:

## 1. BST (Binary Search Tree) Insertion
- `f_tree_ins` (C-style program): `Examples/impexample/CBSTInsert.v`  
- `insert` (monadic version): `Examples/monadexample/bst.v`  
- `insert_triplesat`: proves refinement of C-style program to monadic version  
- `insert_triplesat_functional_correctness`: proves functional correctness by composing refinement and correctness of the monadic version  



## 2. Mergesort
- `f_merge_sort` (C-style program): `Examples/impexample/Cmergesort.v`  
- `mergesortrec` (monadic version): `monadlib/Examples/mergesort.v`  
- `mergesort_triplesat`: proves refinement  
- `mergesort_triplesat_fc`: proves functional correctness  



## 3. DFS (Depth-First Search)
- `f_dfs_rec` (C-style program): `Examples/impexample/CGraphDFS.v`  
- `DFS` (monadic version): `Examples/monadexample/dfs.v`  
- `dfs_rec_triplesat`: proves refinement  
- `dfs_rec_triplesat_functional_correctness`: proves functional correctness  



## 4. KMP (Knuth–Morris–Pratt)
- `f_constr` (C-style program): `Examples/impEexample/Ckmp.v`  
- `constr_loop` (monadic version): `monadlib/Examples/kmp.v`  
- `constr_triplesat`: proves refinement  
- `constr_triplesat_functional_correctness`: proves functional correctness, showing that the resulting `next` array satisfies the prefix-suffix invariant required by the KMP string matching algorithm  