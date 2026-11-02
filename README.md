# Uniserial computations

Lean verification of finite matrix and quiver computations for ring lengths 2–6. Every case uses the same elementary definitions of objects, morphisms, annihilation quotients, path algebras, and relations.

## Mathematical statements

Start with **`Statements.lean`**. It defines the common assertions `C2` and `C3` and proves their instances for the explicit datasets.

| Length | C2 objects | Quiver arrows | Listed relations | Algebra dimension | Additional C3 objects |
|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 2 | 0 | 6 | 0 |
| 3 | 5 | 4 | 0 | 15 | 0 |
| 4 | 9 | 9 | 1 | 44 | 1 |
| 5 | 18 | 23 | 10 | 179 | 12 |
| 6 | 47 | 75 | 47 | 1708 | — |

`n2_C2` through `n6_C2` assert that an algebra homomorphism from the specified path algebra to the quotient endomorphism algebra has the listed vertex and arrow images, annihilates the specified two-sided relation ideal, and is surjective. Both algebras are finite dimensional, with the dimension shown above. The presented algebra is constructed by imposing those same relations using `RingQuot`.

`n2_C3` through `n5_C3` assert `IsLocalRing` for the individual quotient endomorphism rings of the additional listed objects. The additional families for lengths 2 and 3 are empty. There is no C3 assertion for length 6.

## Reading the formalization

- **`Statements.lean`** contains the public mathematical claims and short invocations of their proofs.
- **`Cases/N2/Case2Data.lean`**, and the corresponding files for lengths 3–6, list the object labels, cyclic summand lengths, and embedding matrices.
- **`Case2Quiver.lean`** and its counterparts list the quivers, signed relations, and arrow matrices. **`Case2Dataset.lean`** and its counterparts assemble the inputs; the **`Additional`** files list the C3 inputs where applicable.
- **`Shared/`** defines the common mathematical objects. In particular, `UniformObjects.lean` defines the ring hypotheses and commuting-square matrices; `UniformQuotient.lean` constructs the actual quotient and its algebra structure; `UniformPaths.lean` defines the path algebra and relation ideal.
- **`Proofs/` directories** contain the supporting algebra and finite computations. Their internal matrix models are connected by proved equivalences to the common quotient used in the public statements. Large finite computations are split into smaller modules to limit compiler memory use.
- **`Audit.lean`** checks the axiom dependencies of the public theorems and the principal quotient constructions.

Human review should check the claims, their common definitions, and the concrete input tables against the intended mathematics. Lean checks that the proofs establish those formal claims; it does not determine whether the chosen inputs or claims express the intended problem.

The scalar hypotheses are explicit in `RingParameters`: a commutative ring `R`, a field `k`, a positive length `n`, an element `π` with `π^n = 0`, and a surjective ring homomorphism `ρ : R →+* k` with kernel `πR`. For each `l ≤ n`, the annihilator of `π^(n-l)` is required to be `π^l R`. No embedding of `k` into `R` is assumed. The quotient's scalar action is induced by `ρ`; multiplication by `π` is proved to vanish there.

Rows of matrices are target coordinates and columns are source coordinates. An embedding entry `(c,e)` denotes `c * π^e`; a summand of length zero is zero. Arrow lists in paths use traversal order, so `[a,b]` evaluates as `φ(b) * φ(a)`. Object indices and arrow indices are zero-based.

The formalization verifies the listed elementary computations. It does not prove a classification of indecomposables, identify a matrix formula with Auslander–Reiten translation, or establish a categorical factorization criterion. The prescribed annihilation condition defines the quotient.

## Verification

Requirements: Lean managed by `elan`, Git, and Python 3.11 or newer. The exact Lean version is pinned in `lean-toolchain`; the mathlib revision and its dependencies are pinned in the Lake configuration and manifest.

From this directory, run:

```sh
lake update
lake exe cache get
python3 verify.py --jobs 2
```

The verifier compiles every project module in dependency order, checks that all included Lean files belong to the public theorem dependency graph, rejects proof admissions and unsupported proof escapes, and audits the reported axioms. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Results and compiler logs are written under `.verification/`.

For an interrupted run, use:

```sh
python3 verify.py --jobs 2 --resume
```

Resume mode checks recorded source and compiled-file hashes and invalidates changed modules and their dependents. Without `--resume`, every project module is recompiled. The larger cases can take substantial time and memory; use `--jobs 1` if needed. `lake build` also compiles the public entry points, while the Python verifier additionally enforces the source inventory and axiom audit.

The distribution contains the required Lean sources, this README, and the build and verification configuration. Generated build files and caches are not included.
