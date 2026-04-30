# AGENTS.md

Instructions for coding agents working in `MIPStarRE`. This is the **single
source of truth** for agent conventions. Claude Code agents should also read
`CLAUDE.md` for Claude-specific notes.

## Project Overview

This repository is a Lean 4 + Mathlib formalization project for mathematics
around $MIP^* = RE$ (arXiv:2009.12982). The active formalization track is the
**low individual degree test (LDT)** paper — *Quantum soundness of the
classical low individual degree test*.

Key locations:

- `references/ldt-paper/` — in-repo TeX source mirror; the mathematical
  ground truth
- `blueprint/src/` — active LaTeX blueprint with Lean cross-references
  (`\lean{}`, `\leanok`)
- `MIPStarRE/` — Lean codebase matching the blueprint
- `audits/` — dated audit reports, scouting notes, and repair plans

A legacy 2111 tensor track exists under `blueprint/legacy/` — do not modify it.

**Canonical source hierarchy** (use in this order):

1. `references/ldt-paper/` — TeX source of the paper
2. `blueprint/src/chapter/` — active LaTeX blueprint
3. `MIPStarRE/` — Lean scaffold

Always read the paper source before formalizing or proving a statement. The
paper contains the precise mathematical definitions, theorem statements, and
proof strategies that the Lean code must faithfully represent. When stuck on a
sorry site or proof, go back to the original paper TeX source — the answer is
almost always there. Do not guess or try random tactics without first
understanding the paper's proof strategy.

## Repository Layout

```
MIPStarRE/
├── Quantum/               # Reusable matrix / measurement infrastructure
│   ├── FiniteMatrix.lean  # Op d, normalizedTrace, tauNormSq, IsProj, ...
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

Each LDT submodule typically has `Defs.lean` and `Theorems.lean`. Root imports
flow: `MIPStarRE.lean` → `Quantum` + `LDT` → all submodules.

## Quick Start — Build and Check Commands

Run commands from the repository root unless noted otherwise.

### First-time setup

```bash
lake exe cache get
lake build
```

### Full project build (CI-equivalent)

```bash
lake build
```

### Fast single-file type-check (default iteration loop)

```bash
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean
```

### Check for proof holes in one file

```bash
rg -n "sorry|axiom" MIPStarRE/LDT/SelfImprovement/Defs.lean || true
```

### Check for proof holes in the whole project

```bash
rg -n "sorry|axiom" MIPStarRE
```

### Declaration checker

```bash
lake exe checkdecls blueprint/lean_decls
```

Use this when blueprint declaration lists need to match Lean declarations.

### Blueprint build

```bash
leanblueprint pdf    # PDF output
leanblueprint web    # HTML output (use as default for quick checks)
```

In CI, blueprint linting effectively runs `leanblueprint web` from `blueprint/`.

### What counts as a single test

This repository does not have a conventional unit-test suite. The closest
single-test commands are:

- **Lean work**: `lake env lean path/to/File.lean` and
  `rg -n "sorry|axiom" path/to/File.lean || true`
- **Blueprint work**: `leanblueprint web`
- **Whole-repo verification**: `lake build` and
  `lake exe checkdecls blueprint/lean_decls`

### Recommended validation sequence

For a Lean file change:

1. Type-check the edited file with `lake env lean ...`
2. Scan that file for `sorry|axiom`
3. If the change affects imports or shared declarations, run `lake build`

For blueprint changes:

1. Run `leanblueprint web`
2. If declaration links changed, run `lake exe checkdecls blueprint/lean_decls`

## Toolchain

- **Lean**: v4.28.0 (from `lean-toolchain`)
- **Mathlib**: v4.28.0 (from `lakefile.toml`)

Important `lakefile.toml` options:

- `relaxedAutoImplicit = false` — declare all variables explicitly
- `pp.unicode.fun = true`
- `weak.linter.mathlibStandardSet = true`
- `maxSynthPendingDepth = 3`

## Proof-Filling Order

Sections must be filled in this dependency order:

1. Sections 3–4: test setup and preliminaries
2. Section 5: making measurements projective
3. Sections 7–8: expansion and global variance
4. Section 9: self-improvement
5. Sections 10–11: commutativity
6. Section 12: pasting
7. Section 6: main induction wrapper

Do not start from the final theorem and guess intermediate facts.

## Code Conventions

### Imports

- Keep imports at the top of the file
- One import per line
- Follow existing local import style
- Prefer the smallest correct import set, but do not churn imports unnecessarily
- Preserve barrel-file structure: `MIPStarRE.lean`, `MIPStarRE/LDT.lean`
- Before adding a new import, check whether the needed declaration already
  comes from an existing local barrel import

### File structure

Every `.lean` file must have:

1. imports
2. a module docstring starting with `/-!` (title, main definitions, references)
3. namespace / opens / variables
4. declarations

### Formatting

- **Line length**: max 100 characters
- **Spacing**: spaces around `:` and `:=`
- **`by` placement**: at end of the preceding line (`... := by`), never on its
  own line
- **Indentation**: 2 spaces for proof body; 4 spaces for continuation of
  theorem statement
- **Top-level commands**: flush-left
- Avoid orphaned parentheses. Prefer readable multiline formatting over dense
  tactic blocks.

### Naming conventions

Follow Mathlib naming plus project-local conventions:

- Theorems / proofs / proposition-valued terms: `snake_case`
- Structures / inductives / classes / Prop names / Type names: `UpperCamelCase`
- Functions / non-Prop terms: `lowerCamelCase`
- Use American English spelling in declaration names

Project-preferred variable names:

- `q` — alphabet size / finite field order
- `n`, `m` — dimensions
- `σ` — strategies
- `P` — projective measurements
- `G` — graphs (hypercube expansion)

For full details, see `docs/naming.md` and `docs/style.md`.

### Types and signatures

- Give explicit types for declaration arguments
- Give explicit return types for definitions
- Do not rely on auto-implicit variables (forbidden by `relaxedAutoImplicit`)
- Prefer existing project structures and Mathlib-compatible types over ad hoc
  wrappers
- Be skeptical of scaffolding that compiles but cannot support real proofs later

### Documentation

Required:

- **Module docstrings** for every file — `/-! # Title ... ## References ... -/`
- **Docstrings** on every `def`, `structure`, `class`, and significant `theorem`
- Mathematical prose in Lean docstrings and comments should follow
  `docs/mathematical_language.md`

When formalizing a statement from the blueprint, add corresponding `\lean{...}`
and `\leanok` tags in the relevant `blueprint/src/chapter/*.tex` file.

## Proof Engineering

### Search before proving

- Prefer existing Mathlib lemmas
- Reuse local API from `Quantum/` and `LDT/Basic/`
- Use file-local helper lemmas only when they genuinely reduce duplication
- Scout Mathlib first: `exact?`, `apply?`, `#find?`, grep Mathlib source
- See `audits/` for chapter-by-chapter Mathlib dependency analysis

### Mathlib integration

The project depends heavily on Mathlib for finite-dimensional complex matrices,
Hermitian/PSD operators, and spectral theory. When proving lemmas:

- Reuse existing Mathlib lemmas rather than reproving
- Prefer Mathlib types over custom definitions
- Do not re-declare standard Mathlib lemmas (e.g., custom matrix transpose
  lemmas when `Matrix.transpose_*` exists)

### Validation ladder

1. `lake env lean path/to/File.lean`
2. `lake build`

Do not jump straight to full builds for every small edit.

### Lean-specific advice

- Prefer small, composable lemmas over giant fragile proofs
- Reuse `SubMeas`, `Measurement`, tensor-placement, PSD, and trace lemmas
  already in the repo
- Check `docs/api_surface.md` for useful obligation-closing lemmas
- If changing statements, confirm against paper and blueprint first
- Never add axioms or weaken statements without explicit justification

## Mathematical Documentation Style

Write repository prose for mathematicians and mathematical physicists. Prefer a
clear, precise, and unhurried expository style: introduce the object under
discussion, state the mathematical relation being used, distinguish hypotheses
from conclusions, and avoid informal process language when a standard
mathematical phrase is available.

When writing docstrings, audit notes, PR descriptions, or blueprint-adjacent
comments, use terminology from the standard mathematical literature, the LDT
paper, and the local formalization. Do not invent slang or private shorthand for
mathematical objects. The goal is prose that a third-party reader can understand
without having read the agent conversation that produced the change.

### Paper-gap notes

For documentation of discrepancies between the cited paper, the blueprint, and
Lean, follow `docs/paper-gaps/policy.tex`. In particular, such notes should be
mathematical prose for mathematicians and mathematical physicists who have not
read the issue discussion: introduce notation, state the cited assertion,
isolate the calculation or logical obstruction, compare with the blueprint and
Lean statement, and give a clear verdict. If Lean uses a Mathlib result or
construction not present in the cited argument, explain that replacement
pedagogically before naming the formal declaration. If the cited assertion is
false and a counterexample is available, explain the counterexample in prose and
use any Lean declaration only as verification.

## Proof Integrity

### Blockers (must be resolved before merge)

See `docs/PROOF_INTEGRITY.md` for the full catalog.

**Direct proof holes**: `sorry`, `admit`

**Kernel / type system bypasses**: `native_decide`, `unsafeCast`, `unsafeCoerce`,
`lcProof`, `ofReduceBool`, `ofReduceNat`

**Axiom smuggling**: unjustified `axiom` declarations

**Circular reasoning**: proofs that assume the statement being proved as a local
hypothesis, or helper lemmas that essentially restate the main goal.

**Castle-in-the-air (ungrounded proofs)**: custom re-declarations of standard
Mathlib lemmas; `axiom` or `sorry`-based helpers for facts already in Mathlib;
chains of custom lemmas that never bottom out in Mathlib or Lean core.

**Scaffolding that blocks real formalization**: definitions or theorem statements
that do not faithfully represent the actual mathematics, making them impossible
to connect to real Mathlib-based proofs. Ask: *Can a real proof be built on top
of this?*

### Warnings

Placeholder tactics (`exact?`, `apply?`, `library_search`) should be replaced
with concrete results. Debug artifacts (`dbg_trace`, `#check`, `#eval`,
`#print`) should be removed from proof files. See `docs/PROOF_INTEGRITY.md` for
the full warning catalog.

### Anti-patterns

Subtler proof-evasion patterns that pass kernel-level checks yet still fail to
prove the claimed mathematics are catalogued in `docs/anti_patterns.md`:
conclusion-shaped hypotheses, definitional sleight-of-hand, zero-fallback
branches, trivial default witnesses, Mathlib-bypass castles, and external
`*Statement` smuggles. Reviewers should consult this file alongside
`docs/PROOF_INTEGRITY.md`.

## PR and Commit Conventions

### PR title format

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Bug fix (broken proof, wrong identifier, etc.)    |
| `refactor` | Restructuring without changing API surface        |
| `docs`     | Documentation or blueprint changes only           |
| `style`    | Formatting, naming, or docstring cleanup only     |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `LDT/SelfImprovement`, `Quantum`,
`blueprint`, etc. Omit the `MIPStarRE/` prefix.

### PR body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed. Cite the issue and paper/blueprint location.

### Description
- State precisely what changed.

### Testing
- What was verified and how (e.g., `lake build`, `rg -n "sorry|axiom"`).

---
Addresses #N
```

Use `Addresses #N` (keeps the issue open) or `Closes #N` (auto-closes on merge).

### Commit messages

- **Imperative mood** in the subject line ("Add", not "Added")
- Subject under 72 characters
- When squash-merging, the commit message should match the PR title format

## Review Process

Every PR touching Lean code should be reviewed against these criteria:

1. **Proof correctness** — No unexplained `sorry`. No `axiom` unless discussed.
2. **Mathlib style** — Follow `docs/naming.md` and `docs/doc.md`.
3. **Paper terminology** — Public Lean names and documentation should use
   terminology from the paper and blueprint. See `docs/mathematical_language.md`.
4. **Linter hygiene** — Fix warnings, don't mask them with broad
   `set_option linter.<name> false` blocks.
5. **Type safety** — No universe mismatches, coercion problems.
6. **Performance** — Avoid expensive tactics on large types.
7. **Modularity** — Are new lemmas general enough to be reused?
8. **Documentation** — Every new `def` and major `theorem` must have a docstring.
9. **Blueprint sync and paper origin** — Add `\lean{}` and `\leanok` tags for
   formalized statements. Record formalization-only auxiliary lemmas explicitly.
10. **Scaffolding integrity** — Verify scaffolding aligns with Mathlib.
11. **Proof-evasion anti-patterns** — Review against `docs/anti_patterns.md`.

For full details, see `docs/CONTRIBUTING.md` and `docs/pr-review.md`.

## Blueprint and Documentation Work

If modifying blueprint material:

- Keep chapter structure under `blueprint/src/chapter/`
- Ensure `leanblueprint web` succeeds
- Keep Lean declaration references valid
- Sync theorem labels with Lean names
- Add `\lean{LeanDeclName}` and `\leanok` tags for formalized statements

For blueprint style conventions, see `docs/blueprint_style_guide.md`.

## Agent Rule Sources

Checked in this repository snapshot:

- No `.cursorrules`
- No `.cursor/rules/`
- No `.github/copilot-instructions.md`

Use this file together with:

| File | Purpose |
|------|---------|
| `CLAUDE.md` | Claude Code-specific notes (minimal pointer to this file) |
| `docs/CONTRIBUTING.md` | PR format, issue templates, label taxonomy, review checklist |
| `docs/PROOF_INTEGRITY.md` | Blocker / warning patterns for proof correctness |
| `docs/anti_patterns.md` | Subtler proof-evasion patterns |
| `docs/style.md` | Mathlib code style (line length, indentation, tactic formatting) |
| `docs/naming.md` | Mathlib naming conventions |
| `docs/doc.md` | Mathlib documentation standards |
| `docs/mathematical_language.md` | Project-local terminology rules |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/api_surface.md` | Useful obligation-closing lemmas for `SubMeas` |
| `docs/paper-gaps/policy.tex` | Paper-gap documentation conventions |
| `docs/ci-automation.md` | CI/CD workflow details |
| `docs/pr-review.md` | Mathlib PR review guide |
| `docs/pr_review_management.md` | Review thread workflow and bot integration |
| `audits/` | Chapter-by-chapter scouting reports |
| Pinned memories (external agent tooling) | Agent session memory maintained by the agent runtime; not a directory in the repository checkout. Pinned memories contain accumulated project lessons |

## Practical Defaults for Agents

When editing Lean code:

1. Read the paper source
2. Read the target Lean file and nearby supporting files
3. Type-check the single file
4. Scan for `sorry|axiom`
5. Run `lake build` only when the local change is stable

When editing blueprint files:

1. Read the matching paper source and chapter file
2. Update Lean links carefully
3. Run `leanblueprint web`

Prefer minimal, dependency-aware changes that preserve the project's theorem
structure.
