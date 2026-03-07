# MIPStarRE

Formalization project for the mathematics around $\mathrm{MIP}^*=\mathrm{RE}$, starting with arXiv:2111.08131, *Quantum Soundness of Testing Tensor Codes*.

## Current strategy

The first milestone is a **finite-dimensional pilot formalization** of the reusable infrastructure behind the tensor code test:

- quantum measurements and submeasurements,
- consistency and closeness relations,
- linear and tensor codes,
- the tensor code test interface,
- the expander-graph averaging lemma,
- and a theorem skeleton for the hard self-improvement and pasting sections.

This keeps the early project focused on reusable components that will scale toward the larger $\mathrm{MIP}^*=\mathrm{RE}$ formalization.

## Repository layout

- `MIPStarRE/Quantum/` — quantum and operator-theoretic infrastructure.
- `MIPStarRE/Codes/` — coding-theoretic definitions and lemmas.
- `MIPStarRE/Games/` — nonlocal-game and test interfaces.
- `MIPStarRE/Paper2111/` — paper-specific statements and proof skeletons.
- `blueprint/` — Lean blueprint and dependency-tracked notes.
- `docs/` — planning notes and roadmaps.
- `references/` — bibliographic or source-tracking material for papers.

## Getting started

```bash
lake exe cache get
lake build
```

## GitHub configuration

After creating the repository on GitHub, enable:

1. **Actions → General → Allow GitHub Actions to create and approve pull requests**
2. **Pages → Source → GitHub Actions**
