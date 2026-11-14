# Birkhoff problem: Lean certificate

This repository contains a Lean 4 formalization, using mathlib, of the finite algebra and embedding computations used in the paper for ring lengths $n=2,3,4,5,6$. The cases share definitions of cyclic-module objects, commuting-square morphisms, endomorphism algebras, quivers, and relations.

## Verified statements

[Statements.lean](Statements.lean) is the entry point for the mathematical claims.

- **C2:** For each length from 2 to 6, the specified vertex and arrow matrices define a surjective algebra homomorphism from the path algebra to the computed quotient endomorphism algebra. The listed relations vanish, and the presented algebra and the target have the same stated finite dimension.
- **C3:** For the additional objects requiring a separate check beyond the paper's C1 construction, the ordinary endomorphism rings are local. The additional matrices are also proved to define embeddings. These checks concern one object at length 4 and twelve at length 5; the additional families at lengths 2 and 3 are empty. No C3 assertion is made for length 6.

The C2 datasets have the following sizes:

| Ring length | Objects | Arrows | Listed relations | Algebra dimension |
|---:|---:|---:|---:|---:|
| 2 | 3 | 2 | 0 | 6 |
| 3 | 5 | 4 | 0 | 15 |
| 4 | 9 | 9 | 1 | 44 |
| 5 | 18 | 23 | 10 | 179 |
| 6 | 47 | 75 | 47 | 1708 |

The corresponding public theorems are `n2_C2` through `n6_C2` and `n2_C3` through `n5_C3`.

## Mathematical setup and scope

Objects and morphisms are described by matrices between finite direct sums of cyclic modules $R/(\pi^l)$. The hypotheses `RingParameters` specify a commutative ring $R$, a residue field $k$, an element $\pi$, and a surjective residue map $\rho : R \to k$, with $\pi^n=0$, $\ker\rho=\pi R$, and $\mathrm{Ann}(\pi^{n-l})=\pi^lR$ for $0\leq l\leq n$. No coefficient-field embedding $k\hookrightarrow R$ is assumed.

For C2, Lean constructs an algebraic quotient of commuting-square matrices: two representatives are identified when $\pi^{n-1}$ annihilates the difference of their ambient module maps. Its algebra structure and matrix realization are verified. The categorical ideal quotient itself, and the identification of this algebra with the relevant endomorphism algebra in that category, are not formalized. Those identifications, the interpretation of the supplied formulas as Auslander–Reiten translates, and the classification argument belong to the paper.

## Repository layout

- [Statements.lean](Statements.lean): common assertions and public case theorems.
- [Cases/](Cases/): data and proofs for lengths 2–6. The `Data`, `Quiver`, and `Dataset` files specify the objects, arrows, relations, and their assembly; `Additional` files supply the extra embeddings.
- [Shared/](Shared/): common ring hypotheses, matrix morphisms, ordinary endomorphism rings, the annihilation quotient, and path algebras.
- `Proofs/` directories: supporting algebra and finite computations, split into smaller modules where needed.
- [Audit.lean](Audit.lean): axiom-dependency checks.
- [verify.py](verify.py): compilation and audit driver.

In the input tables, an entry `(c,e)` represents $c\pi^e$; rows are target coordinates and columns are source coordinates. A length-zero summand is the zero module. Paths list arrows in traversal order, so `[a,b]` evaluates as `φ(b) * φ(a)`. Internal object and arrow indices are zero-based; the stored object labels retain the paper's notation.

## Running the verification

Install Git, Python **3.11 or newer**, and Lean through [elan](https://lean-lang.org/install/manual/). The Lean version is fixed by [lean-toolchain](lean-toolchain); the mathlib revision and dependencies are specified in the Lake configuration and manifest.

The commands below work in macOS, Linux, or Windows with WSL. Run them from the repository root:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake update &&
lake exe cache get &&
python3 verify.py --jobs 1
```

If `lake` is still not found, complete the elan installation and reopen the terminal.

The verifier compiles every project module, checks the source inventory and dependency graph, rejects proof admissions and unsupported proof shortcuts, and audits the reported axioms. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A successful run ends with `PASS: … modules; … audited declarations.` The larger computations can take substantial time, and progress is printed when each module finishes. `--jobs 1` limits simultaneous compilation; more jobs may help on a machine with sufficient memory.

To continue an interrupted run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 verify.py --jobs 1 --resume
```

Resume mode reuses recorded checks only after validating the relevant hashes and toolchain. Without `--resume`, the verifier recompiles all project modules.

Compiler logs, saved progress, and the final `result.json` report are written to `.verification/`. Lake stores dependencies and build files in `.lake/`. Both directories are generated locally and need not be included in the repository. `lake build` also compiles the public entry points; the Python verifier performs the additional inventory and axiom checks.

