# MIPStarRE

Formalization project for the mathematics around $\mathrm{MIP}^*=\mathrm{RE}$, currently focused on a **strict proof-following formalization of arXiv:2111.08131** (*Quantum Soundness of Testing Tensor Codes*).

## Current source of truth

The canonical roadmap for the strict branch is:

- `blueprint/src/content.tex`

For arXiv:2111.08131 the main strict targets are:

- `thm:main` (Theorem 4.1): the synchronous / tracial soundness theorem,
- `thm:main-bipartite` (Theorem 4.7): the later two-prover extension.

The strict branch follows the paper's ambient setting:

- a von Neumann algebra,
- a normal tracial state,
- and projective measurements valued in that algebra.

A finite-dimensional matrix pilot may still be useful as reference material, but it is **not** the source of truth for the strict branch.

## Repository status

The repository currently contains a mixture of:

- **strict assets that should survive** into the paper-faithful development,
- and **legacy pilot scaffolding** from an earlier finite-dimensional warm-up.

The main reusable assets already present are:

- `MIPStarRE/Quantum/OutcomeFamily.lean` for answer relabeling / data-processing bookkeeping,
- `MIPStarRE/Codes/LinearCode.lean` for code uniqueness and interpolation interfaces,
- `MIPStarRE/Games/TensorCodeTest.lean` for grid and axis-parallel-line geometry,
- `blueprint/` for the strict dependency-tracked theorem DAG.

Files such as `Quantum/FiniteMatrix.lean` and the current matrix-based `Quantum/Measurement.lean` should be treated as **legacy pilot references**, not as the strict ambient layer.

## Repository layout

- `MIPStarRE/Quantum/` — reusable measurement bookkeeping and related infrastructure.
- `MIPStarRE/Codes/` — code and tensor-code infrastructure.
- `MIPStarRE/Games/` — tensor-code-test geometry and strategy interfaces.
- `MIPStarRE/Paper2111/` — paper-specific theorem nodes and section skeletons for arXiv:2111.08131.
- `blueprint/` — strict Lean blueprint and dependency-tracked notes.
- `docs/` — estimates, audits, and planning notes.
- `references/` — bibliographic or source-tracking material.

## Immediate strict milestones

1. Choose the ambient von Neumann / normal tracial model for the strict branch.
2. Rebuild the measurement layer abstractly in that setting.
3. Finish the missing tensor-code layer.
4. Formalize `def:tracial-strat` and `def:tracial-good`.
5. Formalize Appendix A and the spectral-gap bridge used by `lem:variance`.
6. Introduce precise external interfaces for `de2021orthogonalization` and `vidick2021almost`.

## Getting started

```bash
lake exe cache get
lake build
```

## GitHub configuration

After creating the repository on GitHub, enable:

1. **Actions → General → Allow GitHub Actions to create and approve pull requests**
2. **Pages → Source → GitHub Actions**
