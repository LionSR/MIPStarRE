# MIPStarRE

Formalization project for mathematics around $\mathrm{MIP}^*=\mathrm{RE}$.

## Active paper track

The current active proof-following track is:

- arXiv:2009.12982, *Quantum soundness of the classical low individual degree test*

Inside the repo, the working paper source for this track is the modular mirror:

- `references/ldt-paper/`

The older 2111 tensor-code track is **preserved**, but it is no longer the active source of truth.

## Current source of truth

For the active LDT track, use these files in this order:

1. `references/ldt-paper/` — in-repo TeX source mirror for the paper
2. `blueprint/src/` — active dependency-tracked blueprint
3. `MIPStarRE/Paper2009LDT/` — Lean naming/matching scaffold
4. `docs/20260320_ldt_source_map.md` — current source-file / theorem-ownership map
5. `docs/20260320_ldt_blueprint_dependency_review.md` — dated dependency-review snapshot for context, not the canonical source of truth

The current blueprint is organized by **theorem ownership and proof dependency**, not by raw TeX input order.

## Current repository state

The repo now contains three distinct layers.

### 1. Active LDT blueprint

- `blueprint/src/content.tex` is now a router.
- The active chapter files live under `blueprint/src/chapter/`.
- The blueprint targets the low-individual-degree paper and links to declarations in `MIPStarRE.Paper2009LDT.*`.

### 2. Active Lean matching scaffold

- `MIPStarRE/Paper2009LDT/` contains section-by-section Lean files for Sections 3--12.
- This is currently a **matching scaffold**:
  - lightweight paper-local definitions,
  - theorem statements present,
  - proofs mostly `by sorry`.
- The purpose of this layer is to stabilize declaration names and match the blueprint before proof filling.

### 3. Preserved legacy material

- `blueprint/legacy/content_2111_strict_20260320.tex`
- `blueprint/legacy/references_2111_strict_20260320.bib`
- `MIPStarRE/Paper2111/`
- archived 2111 notes under `docs/`, including `docs/20260308_strict_2111_roadmap.md`, `docs/20260308_strict_2111_effort_estimate.md`, `docs/20260308_lean_quantuminfo_reuse_2111.md`, and `docs/20260307_mathlib_api_2111.md`

These preserve the earlier 2111 work and should not be treated as the active track.

## Recommended proof-filling order

The source-file order is not the proof-dependency order. The recommended implementation order is:

1. Sections 3--4: test setup and preliminaries
2. Section 5: making measurements projective
3. Sections 7--8: expansion and global variance
4. Section 9: self-improvement
5. Sections 10--11: commutativity
6. Section 12: pasting
7. Section 6: main induction wrapper

This is the order suggested by the rebuilt blueprint and the independent dependency review.

## Dependency picture

A first dependency audit is recorded in:

- `docs/20260320_ldt_blueprint_dependency_review.md`

Short version:

### Likely already supported reasonably well by Mathlib
- finite-dimensional complex matrices
- Hermitian / PSD operators
- trace identities
- Hermitian spectral theorem
- positive square roots / continuous functional calculus
- finite fields, Frobenius, trace
- additive characters / finite-field Fourier ingredients
- some scalar probability and binomial concentration tools

### Likely requiring thin local wrappers
- paper-specific measurement postprocessing and completion
- the relations $\simeq_\delta$, $\approx_\delta$, and strong self-consistency
- hypercube operator normalization
- sandwiched-product constructions and completed families like $\widehat G$
- operator-polynomial notation used in pasting

### Likely requiring substantial local development
- POVM / Naimark infrastructure
- the SVD-based orthonormalization chain in Section 5
- SDP duality / complementary slackness in Section 9
- weighted hypercube spectral package in the paper's normalization
- matrix Chernoff in Section 12
- the paper's exact Schwartz--Zippel wrappers

## Important architectural note

The current `Paper2009LDT` Lean files are a **bridge layer**, not yet the final semantic foundation.

The likely long-term direction is to rebase the semantic development onto the existing honest matrix/measurement layer already in the repo:

- `MIPStarRE/Quantum/FiniteMatrix.lean`
- `MIPStarRE/Quantum/Measurement.lean`
- `MIPStarRE/Quantum/OutcomeFamily.lean`

So the present scaffold should be read as:

- blueprint-matching names first,
- semantic rebase next,
- proofs after that.

## Repository layout

- `MIPStarRE/Quantum/` — reusable matrix / measurement infrastructure
- `MIPStarRE/Codes/` — coding-theoretic infrastructure
- `MIPStarRE/Games/` — game/test geometry and related scaffolding
- `MIPStarRE/Paper2009LDT/` — active paper-local scaffold for the LDT paper
- `MIPStarRE/Paper2111/` — preserved older 2111 track
- `blueprint/` — active blueprint and legacy blueprint snapshots
- `docs/` — source maps, dependency reviews, and planning notes
- `references/` — in-repo paper sources and bibliographic material

## Build

From the repo root:

```bash
lake exe cache get
lake build
```

Blueprint commands are run from the repo root with the local Python tool path available, e.g.

```bash
PATH="$HOME/Library/Python/3.9/bin:$PATH" leanblueprint pdf
PATH="$HOME/Library/Python/3.9/bin:$PATH" leanblueprint web
```

## Current status summary

- active blueprint rebuilt for the LDT paper
- `Paper2009LDT` Lean scaffold added
- blueprint-to-Lean naming pass completed
- `lake build` passes
- next major step: semantic rebase of Sections 3--4, then dependency-ordered proof filling
