# Formalization Patterns

Key design patterns used in the MIPStarRE Lean formalization to bridge the
gap between paper-level mathematics and a compilable Lean proof.

This document is intended for contributors who need to understand *why* the
Lean code is structured as it is, and for reviewers who need to recognize
these patterns when reading PRs.  It complements the individual chapter audits
in `audits/` and the proof-integrity rules in `docs/PROOF_INTEGRITY.md`.

## Table of Contents

1. [Extra-hypothesis-then-discharge](#pattern-1-extra-hypothesis-then-discharge)
2. [Blueprint–Lean synchronization](#pattern-2-blueprintlean-synchronization)
3. [Split-module architecture](#pattern-3-split-module-architecture)
4. [Barrel re-export pattern](#pattern-4-barrel-re-export-pattern)
5. [Bridge-package pattern](#pattern-5-bridge-package-pattern)
6. [Paper-gap documentation pattern](#pattern-6-paper-gap-documentation-pattern)

---

## Pattern 1: Extra-hypothesis-then-discharge

### The pattern

An individual lemma is proved with explicit extra hypotheses that are not
part of the paper's statement of that lemma, but which the paper's proof
*of* that lemma assumes from earlier steps (or from theorems not yet
formalized).  These hypotheses are threaded as explicit arguments to the
lemma.  At the final assembly point — typically `mainFormal` in
`MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` — all the explicit
hypotheses are collected and discharged (or planned to be discharged).

### Why this pattern

| Benefit | Explanation |
|---------|-------------|
| **Modularity** | Each lemma carries exactly the assumptions it genuinely needs from upstream.  No hidden global state. |
| **Parallelism** | Different submodules can be proved independently; the only coupling is the explicit hypothesis type they require, which is defined in a shared `Statements.lean` file and can be refactored later. |
| **Compilation speed** | Lean only needs to elaborate the lemma file plus its minimal dependency set.  The full barrel-of-barrels at `MainFormal.lean` can wait. |
| **Auditability** | Every unformalized dependency is visible as an explicit argument in the lemma signature, not hidden in a `sorry` buried in a proof block.  Tools like `#check` can list them. |
| **Incremental closure** | When a new producer theorem is proved, the hypothesis it satisfies can simply be removed from the caller's signature.  The refactoring is local. |

### How it works

1. **Hypothesis is named.**  A `structure` or `Prop`-valued abbreviation
   bundles the assumptions needed by a lemma but not yet produced by
   earlier statements.  Example from
   `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`:

   ```lean
   abbrev OrthonormalizationInput (params : Parameters) [FieldModel params.q]
       (strategy : SymStrat params ι) (eps delta : Error) :=
     ∀ {Hhat : SubMeas (Polynomial params) ι},
       BipartiteSSCRel strategy.state (uniformDistribution Unit)
         (constSubMeasFamily Hhat)
         (selfImprovementHelperError params eps delta) →
       MakingMeasurementsProjective.OrthonormalizationInput strategy.state Hhat
         (selfImprovementHelperError params eps delta)
   ```

   This `abbrev` says: "The self-improvement theorem needs an
   orthonormalization bridge.  For any helper submeasurement `Hhat` that
   is strongly self-consistent, we need a spectral-truncation and
   locality-preserving repair witness."

2. **Lemma takes the hypothesis as an argument.**  A lemma like
   `selfImprovementInInductionSection` in
   `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean`
   takes `OrthonormalizationInput` (and analogous hypothesis bundles) as
   explicit arguments:

   ```lean
   theorem selfImprovementInInductionSection
       (params : Parameters)
       [FieldModel params.q]
       (strategy : SymStrat params ι)
       (eps delta gamma nu : Error)
       (hhelperStrongSelfConsistency : ...)
       (horthonormalization :
         SelfImprovement.OrthonormalizationInput params strategy eps delta)
       (hfinalFields : SelfImprovement.FinalFieldsInput params strategy eps delta nu)
       ...
       (G : SubMeas (Polynomial params) ι) ... : ...
   ```

3. **Hypothesis propagates upstream.**  The consumer of
   `selfImprovementInInductionSection` — typically a
   `MainInductionStep` wrapper — must itself expose the same hypothesis
   or close it with a producer.

4. **Final closure at assembly.**  The theorem `mainFormal` in
   `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` takes a single
   `hbaseBridge` hypothesis that wraps all remaining unformalized
   assumptions:

   ```lean
   theorem mainFormal
       (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} ...
       (hbaseBridge : (scalars : MainFormalCascadeScalars params eps k) →
         ∀ (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k),
         MainFormalRepairedBridgeHypotheses params strategy eps k hpass scalars roleResidual) :
       ∃ G_A G_B : ProjMeas (Polynomial params) ι, ... := ...
   ```

   There is exactly one `sorry` remaining in this file (line 611),
   corresponding to the successor-case schematic assembly that still
   awaits per-slice induction packages.  Once those are supplied, the
   final hypothesis bundle can be replaced by a `theorem` with zero
   extra hypotheses.

### Known instances

| Instance | Where defined | What it bundles |
|----------|---------------|-----------------|
| `SelfImprovement.OrthonormalizationInput` | `SelfImprovement/Theorems/Statements.lean` | Spectral-truncation and locality-preserving repair witnesses for `Hhat` |
| `SelfImprovement.FinalFieldsInput` | `SelfImprovement/Theorems/Statements.lean` | Completeness, point-consistency, self-closeness, projective-residual estimate |
| `SelfImprovement.HelperStrongSelfConsistencyInput` | `SelfImprovement/Theorems/Statements.lean` | The helper `Hhat` is strongly self-consistent |
| `SelfImprovement.SelfImprovementBridgeInputs` | `SelfImprovement/Theorems/Statements.lean` | All three above, bundled as a single structure |
| `MainFormalBaseBridgeHypotheses` | `Test/MainTheorem/MainFormal.lean` | Orthonormalization inputs + match-mass preservation for the base case |
| `MainFormalRepairedBridgeHypotheses` | `Test/MainTheorem/MainFormal.lean` | Ditto for the repaired base-case route |
| `MainFormalBaseProjectiveCompletionHypotheses` | `Test/MainTheorem/MainFormal.lean` | Bridges + distinguished outcomes + match-mass preservation |
| `MainFormalPostRolePackageDiagonalOrthonormalizationInput` | `Test/MainTheorem/OrthonormalizationData.lean` | Spectral-truncation and repair for unsymmetrized POVMs |
| `MakingMeasurementsProjective.OrthonormalizationInput` | `MakingMeasurementsProjective/Statements.lean` | Spectral truncation + repair witnesses for the orthonormalization lemma |
| `LdPastingContext` | `Pasting/Defs/Context.lean` | All auxiliary hypotheses for `ldPasting` (good, scalar bounds, complete, consistent, self-consistent, bounded) |

### The remaining `sorry` in `MainFormal.lean` (line 611)

The single remaining `sorry` in the codebase (as of 2026-05-07)
corresponds to the successor branch of `mainFormal`.  The TODO comments
list three items:

1. A `MainFormalRolePackageBranchResidual` constructed from
   predecessor/successor induction data,
2. Line-130 orthonormalization inputs (`MainFormalPostRolePackageDiagonalOrthonormalizationInput`),
3. Completion input derived from `completingToMeasurement`.

These are all **data-construction** obligations, not proof-theory gaps.
Once the per-slice self-improvement producers and recursive induction
packages are threaded through, the `sorry` becomes a one-line call to an
existing checked lemma (`mainFormal_ofRoleResidualAndRepairedBridge`).

This is the essence of the pattern: the `sorry` is not "we don't know how
to prove the theorem", it is "we haven't yet written the constructor that
assembles the intermediate data from the upstream pieces we already have."

### Distinction from anti-patterns

This pattern is **not** conclusion-shaped-hypothesis smuggling (anti-pattern
A1 in `docs/anti_patterns.md`).  The key distinction:

- **A1**: The hypothesis *is* the theorem's conclusion (or an `∃` that
  directly produces it), and the proof body is a one-line `rcases`/`exact`.
- **Extra-hypothesis pattern**: The hypothesis names an *intermediate*
  mathematical fact that the paper's proof also uses (e.g., "Hhat has
  spectral truncation data"), and the lemma does nontrivial work with it
  (proving error bounds, threading through the rest of the argument, etc.).

Bridge packages that are markers for still-unproved intermediate facts
(such as `SelfImprovementBridgeInputs`) are acceptable scaffolding under
this pattern.  They should carry a tracker reference (usually an issue
like #931 or #422) and their fields should be the *assumptions* of the
paper's proof, not the *conclusion* of the theorem.

---

## Pattern 2: Blueprint–Lean synchronization

### The three tags

The blueprint (under `blueprint/src/chapter/`) uses three LaTeX commands
to link to Lean:

| Tag | Meaning | Example |
|-----|---------|---------|
| `\lean{Name}` | The corresponding Lean declaration exists | `\lean{MIPStarRE.LDT.Test.mainFormal}` |
| `\leanok` (statement-level) | The Lean declaration compiles; confirms statement synchronization, not proof closure | `\leanok` |
| `\leanok` (proof-level) | The proof block is fully formalized — the theorem or lemma has a complete sorry-free proof | `\lean{...}` plus `\leanok` inside `\begin{proof}` |
| `\uses{label}` | The statement or proof block depends on the cited result | `\uses{thm:orthonormalization, prop:completing-to-measurement}` |

### Why some nodes show white in the dep graph

The dependency graph at
`https://LionSR.github.io/MIPStarRE/blueprint/dep_graph_document.html`
color-codes theorem nodes:

- **Green**: proof-level `\leanok` is present (the proof block is fully formalized)
- **White** (or white-border): `\lean{}` exists but proof-level `\leanok` is absent; may carry a statement-level `\leanok` during staged development
- **Gray**: No `\lean{}` tag

As of the session 49 audit (2026-05-07), the web dependency graph was
built from an **older** `web.paux` file.  Almost all the nodes that
appeared non-green there (Ch09 pasting lemmas, Ch10 induction helpers)
already have `\leanok` in the current blueprint source files.  The web
build needs regeneration.

### Deliberate absence of `\leanok`

Some nodes have `\lean{}` but deliberately omit `\leanok`:

- **`thm:orthonormalization`** (ch04): The Lean statement carries extra
  hypotheses (`OrthonormalizationInput`) that are not yet discharged by
  all callers.  Until the full hypothesis chain is closed at
  `mainFormal`, `\leanok` is withheld.

- **`thm:naimark`** (ch04): The Lean declaration records questionwise
  local dilations, not the full tensor-product correlation statement in
  the paper.  The comment in the blueprint explicitly says "no \leanok
  is claimed."

- **`thm:main-formal`** (ch02): The 1 `sorry` in `MainFormal.lean` means
  the proof chain is not yet closed.

### The `\uses{}` convention

`\uses{}` should appear:

- On **statement blocks** (theorem/lemma/definition environments): only
  to record *mathematical* dependencies — other definitions or theorems
  whose statements are used in *stating* the current result (not in
  proving it).
- On **proof blocks** (`\begin{proof}`): to record which lemmas are
  invoked in the proof.  This is the natural home for lemma-citation
  chains.

A common mistake is placing proof-only `\uses{}` on statement blocks.
For the checklist item in the review:
`docs/blueprint_style_guide.md` covers this in the section on
`\uses{}` placement.

### Blueprint rebuild workflow

```bash
cd blueprint
leanblueprint web   # generates the HTML with dep graph
```

The CI linting step effectively runs `leanblueprint web` from the
`blueprint/` directory.  After adding or removing `\leanok` tags,
always run this locally to verify the graph updates.

---

## Pattern 3: Split-module architecture

### Directory structure

The Lean codebase is organized into per-chapter subdirectories under
`MIPStarRE/LDT/`, each with its own internal structure:

```
MIPStarRE/LDT/
├── Basic/                    # Parameters, operators, submeasurements, distributions
├── Test/                     # Test definitions, main theorem, error cascade
├── Preliminaries/            # Polynomials, finite fields, Cauchy–Schwarz, Fourier
├── MakingMeasurementsProjective/   # Orthonormalization, projective completion
├── MainInductionStep/        # Section 6 induction wrapper
├── ExpansionHypercubeGraph/  # Section 7–8 expansion, global variance
├── SelfImprovement/          # Section 9 self-improvement
├── CommutativityPoints/      # Section 10 commutativity setup
├── Commutativity/            # Section 11 commutativity bounds
└── Pasting/                  # Section 12 pasting
```

### Subdirectory layout convention

Each subdirectory follows a consistent internal layout:

```
SubModule/
├── Defs.lean        # New structures, type abbreviations, error-term definitions
├── Statements.lean   # Statement-level types (hypothesis bundles, conclusion shapes)
├── Theorems.lean     # Barrel re-export
└── Theorems/
    ├── Core.lean     # Main proof of the chapter's theorem
    ├── ...           # Supporting proof leaves
    └── Results.lean  # Barrel for the proof leaves
```

Some larger chapters (like `Pasting/` and `SelfImprovement/`) have more
internal subdivisions (e.g., `Pasting/Bernoulli/`, `Pasting/Sandwich/`,
`SelfImprovement/Theorems/Results/`).  The outer `Theorems.lean` barrel
imports all the proof leaves.

### Why split instead of monolithic files?

| Reason | Details |
|--------|---------|
| **Compilation parallelism** | Lean's per-file compilation is single-threaded per file; smaller files mean faster individual type-checking loops |
| **Dependency isolation** | A proof leaf in `Pasting/Sandwich/` only depends on `Pasting/Defs.lean` and `Pasting/Statements.lean`, not on the entire pasting proof chain |
| **Edit locality** | Changing a helper in `SelfImprovement/Theorems/Results/AddInUStep12.lean` does not re-elaborate `AddInUStep34AndTransfer.lean` unless the helper's type changed |
| **Reviewability** | A 200-line proof leaf is easier to review than a 4000-line monolithic proof block |
| **Parallel agent work** | Different agents can work on different proof leaves concurrently without merge conflicts |

### When *not* to split further

Don't split a file just to have one theorem per file.  A single file
containing 3–5 related lemmas that share helper definitions and proof
structure is better than 5 files each with one lemma and duplicate
helper material.

### Barrel files

See [Pattern 4: Barrel re-export pattern](#pattern-4-barrel-re-export-pattern)
below.

---

## Pattern 4: Barrel re-export pattern

Each subdirectory with multiple internal proof leaves has a root-level
barrel file (e.g., `Theorems.lean`) that imports all the leaves:

```lean
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationInputConstructors
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Results
```

The barrel file itself contains no new declarations — it is purely a
re-export convenience so downstream consumers can write
`import MIPStarRE.LDT.SelfImprovement.Theorems` instead of importing
each leaf individually.

The top-level barrel is `MIPStarRE.lean`, which imports all
subdirectories.  `MIPStarRE/LDT.lean` imports all LDT subdirectories.

**When to add to a barrel file**: When a new proof leaf is added to a
subdirectory's `Theorems/` subdirectory, add its import to the barrel.

**When not to add**: If a leaf is only used by one other leaf (internal
helper), don't add it to the barrel — let the consumer import it
directly so its API surface doesn't leak.

---

## Pattern 5: Bridge-package pattern

A bridge package is a `structure` whose fields are **proof obligations**
that have not yet been discharged locally but are required by the
downstream theorem.

### Example

From `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`:

```lean
structure SelfImprovementBridgeInputs (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta nu : Error) where
  helperStrongSelfConsistency :
    HelperStrongSelfConsistencyInput params strategy eps delta
  orthonormalization :
    OrthonormalizationInput params strategy eps delta
  finalFields :
    FinalFieldsInput params strategy eps delta nu
```

A caller that needs the self-improvement theorem can take
`(h : SelfImprovementBridgeInputs params strategy eps delta nu)` as a
hypothesis and project the needed field inside the proof body.  This
keeps the lemma signatures compact while naming all the tracked gaps.

### Rules

1. **Every bridge field must have a producer theorem somewhere**, or a
   tracking issue (#931, #422, etc.) explaining when it will be produced.
2. **Docstrings must name the tracking issue and paper source.**
3. **Fields must be the *assumptions* of the paper's proof, not the
   *conclusion* of the theorem** (see A1 anti-pattern in
   `docs/anti_patterns.md`).
4. **When all fields are produced**, the bridge package should be
   replaced by a `theorem` that calls the same proof but with zero
   bridge arguments.

### Related patterns

- `docs/anti_patterns.md` — A1 (conclusion-shaped hypothesis), A4
  (trivial default witnesses), A6 (external `*Statement` smuggles)
- Issue [#449] — hypothesis-smuggle ledger
- Issue [#451] — bridge-package producer catalogue

---

## Pattern 6: Paper-gap documentation pattern

When the Lean formalization intentionally diverges from the paper
statement (corrected constant, different proof route, Mathlib-provided
lemma that replaces a paper step), document the divergence in
`docs/paper-gaps/` as a LaTeX note.

These notes follow a standard structure defined in
`docs/paper-gaps/policy.tex`:

1. **At a glance**: difficulty, Mathlib surface, key APIs
2. **Key theorem forms**: what the paper states vs what Lean proves
3. **Proof analysis**: where the gap occurs and how Lean fills it
4. **Verdict**: whether the divergence is fatal, cosmetic, or tracked

Each note is independent LaTeX and should be readable by a mathematician
or mathematical physicist who has not followed the issue discussion.

Paper-gap notes that reference Mathlib results should state the Mathlib
result in ordinary mathematical language, explain how it is specialized
to the notation of the paper, and compare its hypotheses and conclusion
with the step it replaces.

---

## See also

- `docs/PROOF_INTEGRITY.md` — kernel-level proof integrity rules
- `docs/anti_patterns.md` — catalog of proof-evasion anti-patterns
- `docs/CONTRIBUTING.md` — overall contributor workflow
- `docs/blueprint_style_guide.md` — blueprint notation conventions
- `docs/paper-gaps/policy.tex` — paper-gap documentation standards
- `audits/` — chapter-by-chapter scouting reports
- Issue [#449] — hypothesis-smuggle ledger
- Issue [#451] — bridge-package producer catalogue
- Issue [#931] — main-induction input gap tracker
- Issue [#422] — main-formal assembly gap tracker

[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#931]: https://github.com/LionSR/MIPStarRE/issues/931
[#422]: https://github.com/LionSR/MIPStarRE/issues/422