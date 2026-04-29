# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formalization of MIP\*=RE mathematics (arXiv:2009.12982) in Lean 4 with Mathlib. The active track is **"Quantum soundness of the classical low individual degree test"** (LDT). A legacy 2111 tensor track exists under `blueprint/legacy/` — do not modify it.

## Build Commands

```bash
# First-time setup: fetch Mathlib cache then build
lake exe cache get && lake build

# Build the full project
lake build

# Type-check a single file (fastest iteration loop)
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean

# Check for sorry/axiom in a file
rg -n "sorry|axiom" MIPStarRE/LDT/SelfImprovement/Defs.lean || true

# Build the LaTeX blueprint
leanblueprint pdf    # PDF output
leanblueprint web    # HTML output

# Run declaration checker
lake exe checkdecls
```

**Toolchain**: Lean 4.28.0 + Mathlib v4.28.0 (pinned in `lean-toolchain` and `lakefile.toml`).

## Architecture

```
MIPStarRE/
├── Quantum/               # Reusable matrix/measurement infrastructure
│   ├── FiniteMatrix.lean  # Op d, normalizedTrace, tauNormSq, IsProj, SpectralTruncation
│   └── Measurement.lean   # POVM, measurement types
└── LDT/                   # Low individual degree test (13 submodules)
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
    └── Pasting/
```

Each LDT submodule typically has `Defs.lean` and `Theorems.lean` files. Root imports flow: `MIPStarRE.lean` → `Quantum` + `LDT` → all submodules.

## Canonical Source Hierarchy

1. `references/ldt-paper/` — TeX source of the paper (the ground truth for mathematical content)
2. `blueprint/src/chapter/` — active LaTeX blueprint with Lean cross-references (`\lean{}`, `\leanok`)
3. `MIPStarRE/` — Lean scaffold matching the blueprint
4. `audits/2026-03-20_ldt-source-map.md` — theorem ownership map

**Always read the paper source** (`references/ldt-paper/*.tex`) before formalizing or proving a statement. The paper contains the precise mathematical definitions, theorem statements, and proof strategies that the Lean code must faithfully represent. Cross-reference with the blueprint to understand what has already been formalized.

**When stuck on a sorry site or proof**, go back to the original paper TeX source. The paper proofs contain the exact mathematical argument, intermediate steps, and inequalities needed. If you cannot close a sorry, read the corresponding section in `references/ldt-paper/*.tex` — the answer is almost always there. Do not guess or try random tactics without first understanding the paper's proof strategy.

When formalizing a statement from the blueprint, add `\lean{LeanDeclName}` and `\leanok` tags to the corresponding `blueprint/src/chapter/*.tex` file.

## Proof-Filling Order

Sections must be filled in this dependency order: 3–4 → 5 → 7–8 → 9 → 10–11 → 12 → 6.

## Code Style (Key Rules)

- **Line length**: max 100 characters
- **Naming**: `snake_case` for theorems/proofs, `UpperCamelCase` for types/structures/classes, `lowerCamelCase` for functions/terms. American English spelling.
- **Project-specific variables**: `q` (alphabet size), `n`/`m` (dimensions), `σ` (strategies), `P` (projective measurements), `G` (graphs)
- **Module docstring**: every `.lean` file needs `/-! # Title ... ## References ... -/` after imports
- **Docstrings**: required on every `def`, `structure`, `class`, and significant `theorem`
- **`by` placement**: at end of preceding line (`... := by`), never on its own line
- **Indentation**: 2 spaces for proof body; 4 spaces for continuation of theorem statement
- Follow Mathlib conventions throughout — see `docs/naming.md` and `docs/style.md` for full details

## Proof Integrity

Before merging, all of these are **blockers** (see `docs/PROOF_INTEGRITY.md`):
- No unexplained `sorry` or `admit`
- No `native_decide`, `unsafeCast`, `unsafeCoerce`, `lcProof`, `ofReduceBool`, `ofReduceNat`
- No unjustified `axiom` declarations
- No circular reasoning or castle-in-the-air proofs ungrounded in Mathlib
- Scaffolding must be compatible with Mathlib types — ask: "Can a real proof be built on this?"

## PR Conventions

- **Title format**: `type(scope): short description` (e.g., `feat(LDT/SelfImprovement): add induction step`)
- **Types**: `feat`, `fix`, `refactor`, `docs`, `ci`, `chore`
- **Scope**: shortened module path without `MIPStarRE/` prefix
- **Body**: must have Motivation / Description / Testing sections (template auto-fills)
- **Footer**: `Addresses #N` (keeps issue open) or `Closes #N`
- **Commit messages**: imperative mood, under 72 chars

## Documentation References

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
| `docs/PROOF_INTEGRITY.md` | Blocker/warning patterns for proof correctness |
| `docs/mathematical_language.md` | Project-local mathematical language rules for Lean names and documentation |
| `docs/pr_review_management.md` | Review thread workflow and bot integration |
| `docs/blueprint_style_guide.md` | LaTeX blueprint notation and section conventions |
| `docs/ci-automation.md` | CI/CD workflow details (Claude, Codex, GitHub Actions) |
| `audits/` | Chapter-by-chapter Mathlib dependency scouting reports |

Consult the relevant doc before contributing to that area. The `docs/CONTRIBUTING.md` file is the primary entry point.

## Lean Options (from lakefile.toml)

```
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```

`relaxedAutoImplicit = false` means all variables must be explicitly declared — Lean will not auto-introduce implicit variables.

## Mathlib Integration

The project depends heavily on Mathlib for finite-dimensional complex matrices, Hermitian/PSD operators, and spectral theory. When proving lemmas:
- Scout Mathlib first (`exact?`, `apply?`, `#find?`, grep Mathlib source)
- Reuse existing Mathlib lemmas rather than reproving
- Prefer Mathlib types over custom definitions
- See `audits/` for chapter-by-chapter Mathlib dependency analysis
