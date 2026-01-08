# Encoding the ∀∃ Relational Hoare Logic into Standard Hoare Logic

This repository provides a machine-checked Rocq formalization of our encoding theory, along with verified case studies demonstrating how standard Hoare logic can verify program refinements using the `Exec` predicate.

## 📂 Repository Structure

- `EncRelSeq/`: Formal definitions of (standard and relational) Hoare triples, encoding functions, and key theorems.

- `Language/`: A demo C-like imperative language equipped with separation logic and proof tactics (e.g., `forward_simpl`)

- `Examples/`: Case studies including:
  - `monadexample/`: monadic programs and its functional correctness proofs
  - `impexample/`: C programs and its proofs
  - `impEexample/`: C programs (with UB errors handling) and its proofs
  - `QCPexample/`: examples and VCs based tool QCP.
- `monadlib/`: a library for monads with support for deriving `Exec` predicates.

- `fixpoints/`: Fixpoint combinator library used for loops and recursion.

- `QCP/`: A standard Hoare logic tool
  - `linux-binary/`: Precompiled QCP binaries
  - `QCP_examples/`: Annotated C programs
  - `SeparationLogic/`: Rocq backend to check QCP-generated VCs
  - `tutorial/`: Step-by-step QCP usage guide

## ✅ Main Theorems

| Content | Theorems |
|------|---------|
| ∀∃ relational Hoare triples can be encoded into standard Hoare logic| `encoding_correctness` |
| Relational proof rules map to standard ones |  `high_focus_as_conseqpre` `low_focus_as_seq` `comp_fc_as_conseq` `comp_refine_as_conseq` |

## 🚀 Getting Started

### Prerequisites

- [Rocq (Coq) Platform 8.20](https://rocq-prover.org/)
- `make`

### Build Instructions (≈30 minutes)

1. **Clone the repository**
    ```bash
    git clone https://github.com/CielSeven/EncRelTheory.git
    cd EncRelTheory/
    ```
2. **Configure Makefile**
    ```make
    COQBIN=        # Path to your Coq binaries, or leave empty if 'coqc' is in your PATH
    SymExec_DIR=   # Set to QCP/win-binary/ on Windows, QCP/linux-binary/ on Linux, or QCP/mac-arm64-binary/ on MacOS
    SYM_SUF=       # Set to .exe on Windows; leave empty on Linux and MacOS
    SUF=           # Set to .exe on Windows; leave empty on Linux and MacOS
    ```
3. **Build the separation logic backend**
   ```bash
   cd QCP/SeparationLogic/unifysl/
   make depend
   make -j5
   cd ../../..
   ```
4. **Build the entire project**
    ```bash
    make depend
    make -j5
    ```
5. **Generate `_CoqProject`**
   ```bash
   make _CoqProject
   ```
### Optional Builds

- Only encoding theory:
  ```bash
  make enctheory -j5
  ```

- Demo language examples:
  ```bash
  make encexample -j5
  ```

- QCP-based examples:
  ```bash
  make qcpexample -j5
  ```

- Other QCP examples (non-relational):
  ```bash
  make qcpfullexample -j5
  ```

- Test with QCP:
  we provide an example file `test.c` that can be used to experiment with QCP. Run 
  ```bash
  make testgen
  ```
  to generate VCs, then prove the unsolved goals in test_proof_manual.v using Rocq manually.

