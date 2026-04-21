# A Constructive Proof of Rice's Theorem via Hilbert's Tenth Problem

**Author:** Jonathan Brossard (`brossardj@acm.org`)  
**ORCID:** [0009-0004-8031-1438](https://orcid.org/0009-0004-8031-1438)

This repository contains the full source for the paper *"A Constructive Proof
of Rice's Theorem via Hilbert's Tenth Problem"*, including the mechanically
verified Rocq formalization and a concrete C witness to the theorem.

## Summary

Classical proofs of Rice's theorem invoke the law of excluded middle (LEM)
twice: once via diagonalization, and once via the case split P(⊥) ∨ ¬P(⊥).
This paper replaces both with a direct reduction from Hilbert's Tenth Problem
(MRDP theorem), using a two-witness construction that is valid in intuitionistic
logic without any classical reasoning.

The proof is mechanically verified by Rocq (Coq). The single axiom used is
`H10C_SAT_undec` — the undecidability of H10C constraints, imported from
`coq-library-undecidability`. `Rice_Theorem` and `Halting_Problem` are
`Closed under the global context`.

## Repository Contents

| File | Description |
|---|---|
| `rice.tex` | LaTeX source (LMCS format, requires `lmcs.cls`) |
| `rice.bib` | BibTeX bibliography (15 entries, DOIs included) |
| `rice.v` | Rocq proof source — compile with `coqc rice.v` |
| `lmcs.cls` | LMCS style file (see note below) |
| `alphaurl.bst` | BibTeX style for LMCS format |
| `undecidable.c` | Concrete C witness to Rice's theorem |
| `Makefile` | Build system |
| `Dockerfile` | Reproducible build environment (Ubuntu 24.04) |

## Quick Start

### With Docker (recommended — fully reproducible)

```bash
make docker         # build the image: installs all dependencies, verifies
                    # the Rocq proof, compiles rice.pdf, builds undecidable
make docker-run     # run the container and copy outputs to ./out/
make docker-rocq    # re-run the Rocq proof inside a fresh container
make docker-clean   # remove the image and ./out/
```

**What each target does:**

- `make docker` — runs `docker build`. All build steps execute inside
  Ubuntu 24.04: apt installs, `coqc rice.v` (proof verified), `pdflatex`
  (PDF compiled), `gcc` (C witness built). A successful build guarantees
  all three artifacts are correct.
- `make docker-run` — runs the container and copies `rice.pdf`, `rice.vo`,
  and `undecidable` to `./out/` on the host.
- `make docker-rocq` — runs `coqc rice.v` in a fresh container instance,
  printing the Coq version and confirming the single axiom. Useful for
  demonstrating proof validity to a third party without relying on the
  cached build.
- `make docker-clean` — removes the `rice-constructive` image and `./out/`.

Output files after `make docker-run`:
```
out/rice.pdf        — paper, LMCS format
out/rice.vo         — compiled Rocq object (proof accepted)
out/undecidable     — C binary: concrete undecidable analysis target
```

Note: `lmcs.cls` is downloaded from `lmcs.episciences.org` at build time.
Docker build requires internet access. For offline builds, place `lmcs.cls`
in the build context and replace the `wget` line in the Dockerfile with
`COPY lmcs.cls ./`.

### Without Docker (Ubuntu/Debian)

**Install dependencies:**

```bash
sudo apt install coq texlive-latex-extra texlive-bibtex-extra \
                 texlive-fonts-recommended texlive-science libgmp-dev
```

**Download the LMCS style file** (required for `rice.pdf`):

```bash
wget https://lmcs.episciences.org/public/lmcs.cls
```

**Build:**

```bash
make all        # PDF + Rocq proof + C binary
make pdf        # rice.pdf only (requires lmcs.cls)
make rocq       # verify Rocq proof only
make c          # build undecidable only
make run        # build and run both modes of undecidable.c
```

## Dependencies

### Rocq (Coq)

- **Version:** 8.18 or later (tested on 8.18 and 8.20)
- **Install:** `sudo apt install coq`
- **Packages used:** `Arith List Bool Lia ZArith` (all in the standard library)
- **No external libraries required**

The proof uses only these tactics: `intros`, `induction`, `destruct`,
`rewrite`, `lia`, `apply`, `exact`, `injection`, `reflexivity`, `case_eq`,
`simpl`, `pose proof`. All have been stable since Coq 8.10.

### GMP (GNU Multiple Precision)

- **Required for** `undecidable.c` — provides unbounded integer arithmetic
- **Install:** `sudo apt install libgmp-dev`
- **Why required:** The Rocq proof reasons over infinite `nat`. The inner
  tuple counter `n` inside `find_sol_one()` uses GMP `mpz_t` as a
  correctness requirement: a fixed-width counter would exhaust its range in
  finite time, making the inner search trivially terminating and invalidating
  the formal claim. The outer target counter `k` uses `uint64_t` (max
  2⁶⁴−1); this is sufficient in practice because the program stalls at the
  first open value of the sum-of-three-cubes conjecture and never approaches
  2⁶⁴−1. See the comment in `undecidable.c` and Remark 9.1 in the paper
  for the full rationale.

### LaTeX

- `pdflatex` (TeX Live 2023 or later)
- `bibtex`
- `texlive-latex-extra` (for `listings`, `booktabs`, `enumitem`)
- `texlive-bibtex-extra` (for `alphaurl.bst`, required by LMCS format)
- `texlive-fonts-recommended`

### LMCS Style File

`lmcs.cls` is not bundled in this repository as it is maintained separately
by the LMCS layout editors. Download the latest version before building
`rice.pdf`:

```bash
wget https://lmcs.episciences.org/public/lmcs.cls
```

## Makefile Targets

```
make all          build PDF + verify Rocq proofs + build C binary (default)
make pdf          build rice.pdf (requires lmcs.cls)
make rocq         verify Rocq proofs
make c            build undecidable C binary
make run          build and run both modes of undecidable.c
make check        alias for rocq
make install      install all dependencies via apt
make axioms       print axioms used by the proof
make clean        remove auxiliary files + C binary (never touches source)
make distclean    clean + remove .pdf and .vo
make help         show status of all dependencies
make docker       build Docker image (fully reproducible)
make docker-run   build image and copy outputs to ./out/
make docker-rocq  run Rocq proof verification inside Docker
make docker-clean remove Docker image and ./out/
```

## Proof Structure

The Rocq formalization in `rice.v` is organized as follows:

1. **Diophantine infrastructure** — k-ary Cantor encoding, polynomial
   evaluation, `check_solution`, `is_solvable`, `is_unsolvable`
2. **Computation model** — step-indexed programs (`nat → nat → option nat`),
   observational equivalence (`obs_equiv`)
3. **Search dynamics** — `find_sol` with monotonicity lemmas
   (`find_sol_step`, `find_sol_stable`, `find_sol_bound`, `find_sol_at_n`,
   `find_sol_unsolvable`)
4. **Semantic properties** — `SemanticProperty` record, `NonTrivial` record
5. **Two-witness construction** — `S_D` definition,
   `S_D_solvable_equiv`, `S_D_unsolvable_equiv`
6. **H10C undecidability axiom** — `H10C_SAT_undec` (the single external axiom,
   from `coq-library-undecidability`). `Rice_Theorem` and `Halting_Problem`
   are `Closed under the global context`.
7. **Main theorem** — `Rice_Theorem`

## Verifying the Proof

```bash
coqc rice.v
```

Exit code 0 means all goals are closed. To inspect the single axiom:

```bash
grep "Hypothesis\|Axiom" rice.v
```

Expected output:
```
  (* H10C_SAT_undec: sole external axiom, from coq-library-undecidability *)
  Axiom H10C_SAT_undec :
```

## Cybersecurity Relevance

Rice's theorem is the formal foundation for why fully automatic semantic
vulnerability detection is impossible in general. The constructive version
strengthens this: the undecidability holds in intuitionistic logic, meaning
it cannot be evaded by restricting the computational model. It is grounded
in the undecidability of Diophantine arithmetic — the same reason no
algorithm can decide integer solutions to polynomial equations.

For PSIRTs, vulnerability researchers, and tool vendors: this is the
formal basis for why any claim of "complete" static analysis is false.
Bounded analysis (as implemented in
[WCC](https://github.com/endrazine/wcc)) is not a limitation — it is the
principled response to a provable ceiling.

## Citation

```bibtex
@article{brossard2026rice,
  author  = {Jonathan Brossard},
  title   = {A Constructive Proof of {R}ice's Theorem
             via {H}ilbert's Tenth Problem},
  journal = {Logical Methods in Computer Science},
  year    = {2026},
  note    = {Submitted. Preprint: arXiv:2604.16477}
}
```

## License

The Rocq proof (`rice.v`), LaTeX source (`rice.tex`, `rice.bib`), and C
witness (`undecidable.c`) are released under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

`lmcs.cls` and `alphaurl.bst` are not authored by this repository and
retain their respective licenses.

---

## A Concrete Undecidable Analysis Target

The file `undecidable.c` is a **single C program whose termination is
provably undecidable by static analysis**. It is a direct C translation
of the `find_sol` function from `rice.v`, and its undecidability is a
consequence of `Theorem Rice_Theorem`.

### Build and run

```bash
gcc -O2 undecidable.c -o undecidable -lgmp

./undecidable decidable     # terminates immediately (equation is solvable)
./undecidable undecidable   # stalls at the first open case of an open conjecture
```

### What the two modes do

Both modes implement the same algorithm — the `find_sol` construction from
`rice.v` — differing only in which Diophantine equation they search:

**Mode 1 (`decidable`)** searches for integer solutions to `x² - y² - z² = 1`.
This is solvable (solution: x=1, y=0, z=0), so the program terminates
immediately. A correct static analyzer must say "terminates."

**Mode 2 (`undecidable`)** searches sequentially, for k = 0, 1, 2, … up to
2⁶⁴−1 (skipping k ≡ 4 or 5 mod 9, which are provably impossible as sums of
three cubes), for integer solutions to `x³ + y³ + z³ = k`. It advances to
k+1 as soon as a solution for the current k is found. This program
terminates if and only if every eligible integer is a sum of three integer
cubes — an open conjecture in number theory as of 2026. Unlike a search for
a single fixed target, this formulation is robust: resolving any individual
k merely advances the search, and the termination question is equivalent to
the full conjecture. The outer target counter `k` uses `uint64_t` (see the
code comment and Remark 9.1 in the paper for the rationale); the inner tuple
counter `n` uses GMP `mpz_t` as a correctness requirement.

### The formal claim

```
Theorem Rice_Theorem (in rice.v):
  No computable function can correctly decide, for all programs of this
  form, whether they terminate.
```

More precisely: termination of `find_sol(D)` is equivalent to solvability
of D. Since solvability of arbitrary Diophantine equations is undecidable
(MRDP theorem, mechanized in Rocq at
https://github.com/uds-psl/coq-library-undecidability), termination of
the program family is undecidable.

**This is not a limitation of current tools.** It is a theorem. Any static
analyzer that claims to decide termination for all programs of this form
either:
- Is wrong on some input (by the Rice/MRDP argument), or
- Runs forever on some inputs (which is not a decision procedure).

### Connection to the Rocq proof

The C function `find_sol_one()` in `undecidable.c` mirrors the Rocq definition:

```rocq
Fixpoint find_sol (ar : nat) (p : Poly) (fuel : nat) : option nat
```

The Rocq proof constructs two programs `S_D^0` and `S_D^1` that call
`find_sol` and behave differently depending on whether `D` is solvable.
The C program is a concrete witness to this construction. Any static
analyzer deciding the semantic property "terminates" for this family would,
by the proof's construction, decide Diophantine solvability — contradicting
`H10C_SAT_undec`.

### Why this matters for cybersecurity

Static analyzers used for vulnerability detection — SAST tools, taint
analyzers, model checkers — all decide semantic properties of programs.
Rice's theorem implies that **any non-trivial semantic property** has this
undecidable structure. The programs above are not pathological adversarial
inputs. They are straightforward integer loops. The undecidability is
intrinsic to what static analysis asks, not to how the programs are written.

The constructive proof in `rice.v` strengthens this: the undecidability
holds even in intuitionistic logic, meaning it cannot be evaded by
restricting to weaker computational models. The obstacle is Diophantine
arithmetic — present in any model expressive enough to run real programs.
