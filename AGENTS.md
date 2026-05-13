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

## Faithful Formalization Policy

A declaration is a formalization of a paper theorem only when its public Lean
statement matches the cited paper statement, up to faithful formal encoding.
Changing a Lean theorem away from the corresponding statement in
`references/ldt-paper/` is strongly discouraged and should occur only when a
faithful formal encoding or a documented mathematical necessity requires it.
This applies to every declaration advertised as a formalization of a paper
result, not only to theorems currently undergoing repair.  The check is on the
hypotheses as well as the conclusion.  A theorem whose
conclusion has the right shape but whose assumptions include an extra
load-bearing bridge input or hypotheses bundle is a conditional theorem, not
the paper theorem.
The project goal is to eliminate such conditional bridges, not to normalize
them as permanent infrastructure.

If the only available Lean theorem has extra assumptions, the blueprint must
not mark the source-labelled paper entry as matched by that theorem.  Either
leave the source-labelled entry without `\leanok`, or state the restricted or
conditional result as a separate Lean-only blueprint entry whose hypotheses are
displayed explicitly.  A scope-restricted theorem may be marked `\leanok` only
against a blueprint statement that explicitly states the restriction; it must
not be presented as the unrestricted source theorem.

This rule applies especially to declarations named after paper labels such as
`mainFormal`, `selfImprovement`, `mainInduction`, or other theorem names linked
from the blueprint by `\lean{...}` and `\leanok`.

Before editing any theorem tagged with a paper label (`thm:*`, `lem:*`,
`prop:*`):

1. Read the corresponding statement in `references/ldt-paper/`.
2. Preserve the public Lean theorem statement, except for hypotheses that are
   genuinely part of the faithful encoding of the paper's domain.
3. Do not add bridge inputs, residual packages, repair hypotheses, producer
   assumptions, generic hypotheses or assumptions bundles, or arbitrary
   implication hypotheses to the paper theorem.
4. If a missing intermediate fact is needed, first state that fact as a named
   lemma or theorem to be proved from the paper hypotheses.
5. Do not add a conditional helper merely to keep a file compiling.  A
   conditional helper may remain temporarily only when the proof content it
   preserves is mathematically useful, the source-faithful theorem remains
   visible, and the helper has a paper-gap note, a named construction theorem
   or proof-obligation target, and an explicit discharge or deletion plan.  Its
   name must show that it is conditional without making the assumption look like
   an acceptable source hypothesis, for example
   `mainFormal_ofInternalObligations`, `selfImprovementFromObligations`, or a
   name ending in `_ofObligations`.
6. Do not point a source-labelled blueprint theorem to the conditional helper
   with `\leanok`.

When reviewing an existing bridge, residual, repair, producer, or package
hypothesis, first try to recover any genuine proof content from its construction
and turn that content into a source-faithful lemma.  If the bridge does not
actually follow from the paper hypotheses, do not preserve the paper theorem as
a strengthened statement.  Restore the paper-aligned theorem statement and leave
the missing proof obligation explicit, even if that means reintroducing a
tracked `sorry` during a repair PR.

Some side conditions are not deviations: positivity needed to define a
division, nonemptiness of a finite type, decidability instances, field-model
instances, and similar boundary hypotheses may be faithful encodings of
assumptions that the paper leaves implicit.  These should still be reviewed and
documented if they are mathematically load-bearing.  The forbidden pattern is
different: moving an unproved step of the proof into the theorem statement, such
as a `BridgeHypotheses`, `Input`, `Residual`, `Package`, `RepairInput`,
`Producer`, generic `Hypotheses`, or generic `Assumptions` assumption that the
paper theorem does not assume.  These assumptions
should not be introduced merely to keep a file compiling or to avoid a `sorry`;
they require explicit mathematical justification and a planned discharge.

For the current LDT final theorem, `mainFormal` is reserved for the statement of
`\Cref{thm:main-formal}`: from a projective strategy passing the low individual
degree test, it produces the three final consistency conclusions.  A theorem
with an extra hypothesis such as
`hbaseBridge : ... → MainFormalRepairedBridgeHypotheses ...` is temporary
scaffolding at best; it must not be the declaration advertised as
`thm:main-formal`.  The corresponding paper-aligned version should remain
visible, even if its proof is temporarily unfinished during repair.

Every agent changing a paper-labelled theorem must finish with a statement
integrity audit:

- paper assumptions;
- Lean assumptions;
- paper conclusion;
- Lean conclusion;
- verdict: exact, faithful boundary hypotheses, extra assumptions, weakened
  conclusion, or strengthened conclusion.

### Paper-realignment mode

When a theorem, definition, or hypothesis field has already drifted away from
`references/ldt-paper/`, a repair PR may temporarily reintroduce `sorry` in
order to restore the source-faithful statement.  In this mode, statement
faithfulness is the first invariant: keeping a divergent proof intact merely to
avoid `sorry` preserves a theorem that the paper does not state.

Paper-realignment mode is narrow.  It applies only to edits whose purpose is to
remove wrong hypotheses, delete divergent fields, restore a paper theorem
statement, or replace a conditional theorem by a paper-facing statement plus a
named proof obligation.  Such a PR must:

1. cite the paper passage by label or line range in the relevant docstring;
2. cite the paper-gap note or tracking issue that records the divergence;
3. identify every introduced or retained `sorry` and the construction theorem,
   proof-obligation theorem, or source-faithful lemma expected to discharge it;
4. avoid unrelated refactors, notation changes, or proof-engineering churn.

During paper realignment, every restated definition, hypothesis field, or
paper-facing theorem must have a docstring that lets a reviewer tell whether
the statement is present in the paper or is a Lean-only proof obligation.  A
name such as `Bridge`, `Residual`, `Repair`, `Package`, `Input`, or `Producer`
is not by itself a mathematical source citation.

### Unfaithful dependency markers

A theorem or lemma is **unfaithful** when its proof relies on a hypothesis,
helper, bridge, residual, repair input, or conditional theorem that is known not
to follow from the cited paper statement.  This includes the case where the
public theorem statement is source-shaped but the proof calls a conditional
helper whose load-bearing hypothesis is not yet derived from the paper
hypotheses.

Such a declaration must carry a docstring section beginning with
`**Unfaithful:**`.  The marker must name the load-bearing deviation, cite the
paper-gap note or issue that documents it, and state the planned discharge.  A
minimal form is:

```text
**Unfaithful:** This proof currently relies on `<hypothesis or helper>`,
which is not derived from `<paper label or line range>`.  Documented in
`docs/paper-gaps/<note>.tex` or issue `#N`.  Elimination: prove
`<construction theorem>` from the paper hypotheses.
```

The marker propagates through dependencies: a theorem whose proof transitively
uses an unfaithful declaration is itself unfaithful until the dependency is
replaced by a source-faithful proof.  Remove the marker only when the cited
deviation has been discharged.

Not every discrepancy requires the full `**Unfaithful:**` marker.  If the paper
has a local typo, a documented numerical strengthening, or a genuine scope
restriction, use a lighter docstring marker such as `**Local fix:**` or
`**Scope restriction:**`, citing the relevant paper-gap note.  These lighter
markers are for mathematically correct local corrections; `**Unfaithful:**` is
reserved for load-bearing assumptions or proof steps still missing from the
paper hypotheses.

## Code Conventions

### Imports

- Keep imports at the top of the file
- One import per line
- Follow existing local import style
- Prefer the smallest correct import set, but do not churn imports unnecessarily
- Preserve re-export-file structure: `MIPStarRE.lean`, `MIPStarRE/LDT.lean`
- Before adding a new import, check whether the needed declaration already
  comes from an existing local re-export import

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

For a pedagogical register of external lemmas not explained in the paper,
see `docs/external-lemmas-pedagogy.md`. This includes Schwartz–Zippel,
Fourier orthogonality, Cauchy–Schwarz for approximate measurements, CFC,
and external result statements (Polishchuk–Spielman, Raz–Safra).

For the policy on temporary conditional scaffolding and blueprint
synchronization, see `docs/formalization-patterns.md`.

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

For the proof-gap terminology used to distinguish source theorems, internal
proof obligations, and conditional helpers, follow
`docs/paper-gaps/proof-gap-protocol.tex`.  For documentation of discrepancies
between the cited paper, the blueprint, and Lean, follow
`docs/paper-gaps/policy.tex`. In particular, such notes should be
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
   formalized statements only when the Lean statement matches the source.
   Record formalization-only auxiliary lemmas explicitly.
10. **Scaffolding integrity** — Verify scaffolding aligns with Mathlib.
11. **Statement drift** — Compare source-labelled theorem statements with the
   paper and flag new hypotheses, weakened conclusions, changed quantifier
   order, altered error parameters, or bridge/residual packages moving toward
   a paper theorem.
12. **Proof-evasion anti-patterns** — Review against `docs/anti_patterns.md`.

For full details, see `docs/CONTRIBUTING.md` and `docs/pr-review.md`.

## Blueprint and Documentation Work

If modifying blueprint material:

- Keep chapter structure under `blueprint/src/chapter/`
- Ensure `leanblueprint web` succeeds
- Keep Lean declaration references valid
- Sync theorem labels with Lean names
- Add `\lean{LeanDeclName}` and `\leanok` tags for formalized statements

For blueprint style conventions, see `docs/blueprint_style_guide.md`.

For temporary conditional scaffolding and the `\lean{}`/`\leanok` tagging
strategy, see `docs/formalization-patterns.md`.

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
| `docs/proof_frontier_review.md` | Review checklist for construction theorems and residual inputs |
| `docs/style.md` | Mathlib code style (line length, indentation, tactic formatting) |
| `docs/naming.md` | Mathlib naming conventions |
| `docs/doc.md` | Mathlib documentation standards |
| `docs/mathematical_language.md` | Project-local terminology rules |
| `docs/blueprint_style_guide.md` | Blueprint notation and section conventions |
| `docs/api_surface.md` | Useful obligation-closing lemmas for `SubMeas` |
| `docs/paper-gaps/policy.tex` | Paper-gap documentation conventions |
| `docs/paper-gaps/proof-gap-protocol.tex` | Protocol distinguishing source theorems, proof obligations, and conditional helpers |
| `docs/formalization-patterns.md` | Conditional scaffolding, blueprint sync, split imports, and bridge records |
| `docs/external-lemmas-pedagogy.md` | Pedagogical notes on Mathlib and external lemmas |
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
