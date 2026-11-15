# MIPStarRE

[![PR CI](https://github.com/LionSR/MIPStarRE/actions/workflows/pr-ci.yml/badge.svg)](https://github.com/LionSR/MIPStarRE/actions/workflows/pr-ci.yml)
[![Compile blueprint](https://github.com/LionSR/MIPStarRE/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/MIPStarRE/actions/workflows/blueprint.yml)
![sorries](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/sorries.json)
![axioms](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/axioms.json)
![Lean](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/lean.json)
![Mathlib](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/mathlib.json)
![blueprint: no \leanok](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/blueprint_no_leanok.json)
![blueprint: not ready](https://img.shields.io/endpoint?url=https://sirui-lu.com/MIPStarRE/badges/blueprint_not_ready.json)

<p align="center">
  <a href="https://sirui-lu.com/MIPStarRE/blueprint/">Blueprint</a> ·
  <a href="https://sirui-lu.com/MIPStarRE/docs/">Documentation</a> ·
  <a href="https://sirui-lu.com/MIPStarRE/paper-gaps/">Paper-gap notes</a>
</p>

Formalization project for mathematics around $\mathrm{MIP}^*=\mathrm{RE}$.

## Active paper track

The current active proof-following track is:

- arXiv:2009.12982, *Quantum soundness of the classical low individual degree test* (LDT).

The in-repo paper source mirror lives at `references/ldt-paper/`.

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
│   ├── FiniteHilbert.lean
│   ├── FiniteMatrix.lean
│   ├── Measurement.lean
│   └── ProjectorONB.lean
└── LDT/                   # Low individual degree test (12 submodules)
    ├── Basic/             # Parameters, operators, distributions, submeasurements
    ├── Test/              # Test definitions & main theorem
    ├── Preliminaries/
    ├── MakingMeasurementsProjective/
    ├── MainInductionStep/
    ├── ExpansionHypercubeGraph/
    ├── GlobalVariance/
    ├── SelfImprovement/
    ├── CommutativityPoints/
    ├── Commutativity/
    ├── Pasting/
    └── Tactic/            # Project-local tactics & simp sets
```

Each LDT submodule typically contains `Defs.lean` and `Theorems.lean` (larger
submodules split these across subdirectories). The root module `MIPStarRE.lean`
re-exports `MIPStarRE.Quantum` and `MIPStarRE.LDT`.

Top-level directories:

- `MIPStarRE/` — Lean source (see above)
- `blueprint/src/` — active LDT blueprint (chapters under `blueprint/src/chapter/`)
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

## For reviewers

This repository accompanies the paper *Long-horizon autoformalization of a core theorem underlying MIP\*=RE* ([arXiv:2609.19814](https://arxiv.org/abs/2609.19814)).

**Requirements.** Lean 4, installed with [elan](https://lean-lang.org/install/), and git. The Lean and Mathlib versions pinned in `lean-toolchain` and `lakefile.toml` (v4.35.0-rc2; v4.31.0 at the paper snapshot) are fetched automatically. Linux or macOS, no special hardware, about 10 GB of free disk space. CI runs on GitHub-hosted Ubuntu 24.04 runners; the times below were measured on macOS 26 with an Apple M4 Pro (12 cores, 48 GB of memory).

**Install and build.** The two commands under [Build](#build): `lake exe cache get` downloads the dependencies and the prebuilt Mathlib (about 5 minutes), and `lake build` checks every proof in the library (about 8 minutes; 15 to 20 minutes on the CI runners).

**Demo: the main theorem.** After the build:

```bash
lake build MIPStarRE.LDT.Test.AxiomAudit    # about 10 seconds
printf 'import MIPStarRE.LDT.Test.MainTheorem.MainFormal\n#print axioms MIPStarRE.LDT.Test.mainFormal\n' > Check.lean
lake env lean Check.lean                     # about 20 seconds
```

The first command ends with `Build completed successfully`; it fails if an audited declaration depends on `sorry` or on a non-standard axiom. The second prints

```
'MIPStarRE.LDT.Test.mainFormal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Paper snapshot.** The measurements reported in the paper refer to commit `b39705bfd` (24 June 2026). Check it out and run the same build commands.

**Independent check.** [LDT-comparator](https://github.com/LionSR/LDT-comparator) re-checks the main theorem against a self-contained statement with the Lean comparator and a second kernel (`./verify.sh`, on Linux).

**Use.** To build on the library, add this repository as a Lake dependency and `import MIPStarRE`. To apply the workflow to another paper, start from [oh-my-formalization](https://github.com/LionSR/oh-my-formalization). The workflow's own code is in `.github/workflows/` (review, repair, and issue automation) and `scripts/` (integrity checks).

## Contributing

Start with [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) for PR/issue conventions and the review checklist. Key references:

Shared Mathlib-style conventions (style, naming, documentation, PR review,
proof integrity, prose) live in the `lean-conventions` skill of
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills),
auto-installed for Claude Code via `.claude/settings.json` (other agents:
clone the repository and symlink the skill directories into the agent's
skill location, as described in its README).

MIPStarRE-local references:

| File | Purpose |
|------|---------|
| `docs/CONTRIBUTING.md` | PR format, issue templates, label taxonomy, review checklist |
| `docs/project_conventions.md` | MIPStarRE-local addenda to the shared conventions (linter warnings, source-faithfulness review, proof integrity) |
| `docs/mathematical_language.md` | Project-local mathematical language rules for Lean names and documentation |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/ci-automation.md` | CI/CD workflow details |
| `audits/` | Chapter-by-chapter Mathlib dependency scouting reports |

When adding or completing a declaration, update the corresponding blueprint entry in `blueprint/src/chapter/`: add `\lean{DeclName}` and `\leanok` for new results, or `\leanok` on `\begin{proof}` for newly proven results.
