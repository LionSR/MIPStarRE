# MIPStarRE

[![Lean Action CI](https://github.com/LionSR/MIPStarRE/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LionSR/MIPStarRE/actions/workflows/lean_action_ci.yml)
![sorries](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/sorries.json)
![axioms](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/axioms.json)
![Lean](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/lean.json)
![Mathlib](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/mathlib.json)
![blueprint: no \leanok](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/blueprint_no_leanok.json)
![blueprint: not ready](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/blueprint_not_ready.json)

Formalization project for mathematics around $\mathrm{MIP}^*=\mathrm{RE}$.

## Active paper track

The current active proof-following track is:

- arXiv:2009.12982, *Quantum soundness of the classical low individual degree test* (LDT).

The in-repo paper source mirror lives at `references/ldt-paper/`.

The older 2111 tensor-code track is **preserved** as a blueprint snapshot only (see `blueprint/legacy/`) and is no longer the active source of truth.

## Source-of-truth order (LDT)

When working on the active track, consult these locations in this order:

1. **`references/ldt-paper/`** — in-repo TeX source mirror for the paper. This is the mathematical ground truth.
2. **`blueprint/src/chapter/`** — active, dependency-tracked LaTeX blueprint with Lean cross-references (`\lean{}`, `\leanok`).
3. **`MIPStarRE/`** — Lean scaffold that matches the blueprint. Declarations in `MIPStarRE.LDT.*` are cross-referenced from the blueprint.

Supporting notes:

- `audits/2026-03-20_ldt-source-map.md` — source-file / theorem-ownership map
- `audits/2026-03-20_ldt-blueprint-dependency-review.md` — dated dependency-review snapshot (context, not canonical)

The blueprint is organized by **theorem ownership and proof dependency**, not by raw TeX input order.

## Repository layout

```
MIPStarRE/
├── Quantum/               # Reusable matrix / measurement infrastructure
│   ├── FiniteMatrix.lean
│   └── Measurement.lean
└── LDT/                   # Low individual degree test (12 submodules)
    ├── Basic/
    ├── Test/
    ├── Preliminaries/
    ├── MakingMeasurementsProjective/
    ├── MainInductionStep/
    ├── ExpansionHypercubeGraph/
    ├── GlobalVariance/
    ├── SelfImprovement/
    ├── CommutativityPoints/
    ├── Commutativity/
    └── Pasting/
```

Each LDT submodule typically contains `Defs.lean` and `Theorems.lean`. The root module `MIPStarRE.lean` re-exports `MIPStarRE.Quantum` and `MIPStarRE.LDT`.

Top-level directories:

- `MIPStarRE/` — Lean source (see above)
- `blueprint/src/` — active LDT blueprint (chapters under `blueprint/src/chapter/`)
- `blueprint/legacy/` — preserved 2111 blueprint snapshots
- `references/ldt-paper/` — in-repo TeX source for the LDT paper
- `docs/` — contributor guides, style, naming, proof integrity, CI notes
- `audits/` — dated chapter-by-chapter dependency-scouting reports

## Recommended proof-filling order

The source-file order is not the proof-dependency order. The recommended implementation order is:

1. Sections 3–4: test setup and preliminaries
2. Section 5: making measurements projective
3. Sections 7–8: expansion and global variance
4. Section 9: self-improvement
5. Sections 10–11: commutativity
6. Section 12: pasting
7. Section 6: main induction wrapper

## Build

**Toolchain**: See `lean-toolchain` and `lakefile.toml` for the pinned Lean and Mathlib versions.

From the repo root:

```bash
# First-time setup: fetch the Mathlib cache, then build
lake exe cache get
lake build

# Type-check a single file (fastest iteration loop)
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean

# Check declarations referenced from the blueprint
lake exe checkdecls blueprint/lean_decls
```

Blueprint commands (from the repo root, with `leanblueprint` on your `PATH`):

```bash
leanblueprint pdf    # PDF output
leanblueprint web    # HTML output
```

## Contributing

Start with [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) for PR/issue conventions and the review checklist. Key references:

Mathlib-derived references:

| File | Purpose |
|------|---------|
| `docs/style.md` | Mathlib code style (line length, indentation, tactic formatting) |
| `docs/naming.md` | Mathlib naming conventions (70+ rules, symbol dictionary) |
| `docs/doc.md` | Mathlib documentation standards (module headers, docstrings) |
| `docs/pr-review.md` | Mathlib PR review guide |

MIPStarRE-local references:

| File | Purpose |
|------|---------|
| `docs/CONTRIBUTING.md` | PR format, issue templates, label taxonomy, review checklist |
| `docs/PROOF_INTEGRITY.md` | Blocker / warning patterns for proof correctness |
| `docs/mathematical_language.md` | Project-local mathematical language rules for Lean names and documentation |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/ci-automation.md` | CI/CD workflow details |
| `audits/` | Chapter-by-chapter Mathlib dependency scouting reports |

When adding or completing a declaration, update the corresponding blueprint entry in `blueprint/src/chapter/`: add `\lean{DeclName}` and `\leanok` for new results, or `\leanok` on `\begin{proof}` for newly proven results.
