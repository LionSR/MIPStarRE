# Formalization Patterns

Key design patterns used in the MIPStarRE Lean formalization to bridge the
gap between paper-level mathematics and a compilable Lean proof.

This document is intended for contributors who need to understand *why* the
Lean code is structured as it is, and for reviewers who need to recognize
these patterns when reading PRs.  It complements the individual chapter audits
in `audits/` and the proof-integrity rules in `docs/PROOF_INTEGRITY.md`.

## Table of Contents

1. [Source-faithful statements and internal proof obligations](#pattern-1-source-faithful-statements-and-internal-proof-obligations)
2. [Blueprint–Lean synchronization](#pattern-2-blueprintlean-synchronization)
3. [Split-module architecture](#pattern-3-split-module-architecture)
4. [Compatibility re-export pattern](#pattern-4-compatibility-re-export-pattern)
5. [Temporary obligation-structure pattern](#pattern-5-temporary-obligation-structure-pattern)
6. [Paper-gap documentation pattern](#pattern-6-paper-gap-documentation-pattern)

---

## Pattern 1: Source-faithful statements and internal proof obligations

### The rule

A declaration advertised as the formalization of a paper theorem, lemma,
proposition, or corollary must state the paper result, up to faithful formal
encoding of the mathematical domain.  Its public hypotheses and conclusion are
both part of the statement.  Adding a load-bearing bridge, residual, repair,
obligation-structure input, hypotheses bundle, or assumptions bundle not present
in the cited statement changes the theorem into a conditional helper.

The project therefore distinguishes three objects.

| Object | Public statement | Blueprint status |
|--------|------------------|------------------|
| Paper theorem | Matches the cited result in `references/ldt-paper/` | May be linked by source-labelled `\lean{}`; statement-level `\leanok` only when the statement matches |
| Internal proof obligation | Proves a missing intermediate mathematical input from paper hypotheses | May contain a tracked `sorry` while the proof is open |
| Conditional helper | Quarantines an unproved intermediate obligation | Not a paper theorem; no source-labelled `\leanok` |

It is never allowed to change the public statement of a declaration advertised
as the formalization of a source-labelled paper theorem.  At the final assembly
point, the paper theorem must either discharge the extra hypotheses internally,
or remain as the paper-aligned statement with an unfinished proof while the
conditional helper is given a different name.

The preferred way to expose unfinished work is a named internal theorem or
definition with a precise paper-origin docstring and, if necessary, a tracked
`sorry`.  This makes the proof frontier visible without weakening the statement
of a source-labelled theorem.

### Why legacy scaffolding may remain temporarily

| Temporary reason | Explanation |
|------------------|-------------|
| **Localizing an obstruction** | A conditional helper can isolate the exact missing mathematical input while the obligation discharger is being proved. |
| **Recovering useful proof content** | The proof body may contain genuine estimates or constructions that should be extracted into source-faithful lemmas. |
| **Auditability** | An explicit temporary hypothesis is easier to find than an implicit assumption hidden in prose, provided it is named as proof debt. |

These reasons do not justify strengthening a paper theorem.  They only explain
why a short-lived helper declaration may exist while its remaining hypotheses
are being actively removed.

### How to proceed when a proof needs an extra input

1. **Check the source statement.**  Read the corresponding TeX in
   `references/ldt-paper/` before changing a theorem linked from the blueprint.
2. **Keep the paper-facing declaration source-faithful.**  Boundary hypotheses
   such as positivity, nonemptiness, decidability, field-model instances, or
   type-class assumptions may be faithful encodings when they are needed to
   state the mathematics in Lean.  Proof data such as `BridgeInputs`,
   `RepairInput`, `Residual`, `Package`, generic `Hypotheses`, or generic
   `Assumptions` is different: it is not a paper assumption unless the cited
   statement says so.
3. **Name the missing intermediate result.**  If the proof uses a mathematical
   fact not yet formalized, state it as a separate proof obligation.  A
   temporary `sorry` in this declaration is preferable to adding the obligation as
   a hypothesis on the paper theorem.
4. **Use conditional helpers only as quarantine.**  A helper such as
   `mainFormal_ofInternalObligations` or `selfImprovement_assumingBridgeInputs`
   is allowed only to preserve downstream proof content while the missing
   obligation discharger is being proved.  It must have a conditional name, a tracked
   removal target, and no source-labelled blueprint `\leanok`.  The
   paper-facing declaration must remain source-faithful.
5. **Audit the final statement.**  Every PR touching a source-labelled theorem
   should compare paper assumptions and Lean assumptions, paper conclusion and
   Lean conclusion, and report whether the Lean statement is exact, has only
   faithful boundary hypotheses, or has extra assumptions.

If a paper-facing declaration is temporarily proved by calling a conditional
helper whose load-bearing input has not yet been produced from the paper
hypotheses, the proof frontier must be marked explicitly.  The declaration
should carry an `**Unfaithful:**` docstring section naming the non-paper
dependency, citing the paper-gap note or tracking issue, and identifying the
internal theorem that will remove the dependency.  A named proof obligation
with a tracked `sorry` is preferred whenever possible, because it makes the
missing mathematical assertion visible without adding it to the paper theorem
statement.

### Conditional helper shape

1. **Hypothesis is named as debt.**  A `structure` or `Prop`-valued
   abbreviation bundles assumptions needed by a conditional helper but not yet
   produced by earlier statements.  Example from
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

   This `abbrev` says: "The conditional self-improvement helper needs an
   orthonormalization bridge.  For any helper submeasurement `Hhat` that
   is strongly self-consistent, we need a spectral-truncation and
   locality-preserving repair witness."

2. **Only a quarantined conditional helper takes the hypothesis as an argument.**  A helper like
   `selfImprovementInInductionSection` in
   `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementBridge/Core.lean`
   takes `OrthonormalizationInput` and analogous proof-obligation structures as
   explicit arguments.  This is not the paper theorem; it is the temporary
   surface where the remaining obligations are isolated:

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

3. **Propagation is a warning sign.**  The consumer of
   `selfImprovementInInductionSection` — typically a
   `MainInductionStep` wrapper — should close the hypothesis with an internal
   theorem as soon as possible.  If the hypothesis propagates upward toward a
   paper-labelled theorem, the PR should stop and either prove the obligation or
   restore the paper theorem with an explicit unfinished proof.

4. **Final closure at the source theorem.**  The theorem `mainFormal` in
   `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` is reserved for the
   paper-shaped statement.  The top-level assembly theorem
   `mainFormal_ofInternalObligations` has the same public hypotheses and
   conclusion; the remaining work is isolated in internal obligation declarations
   such as `mainFormalBaseBranchCompletionObligations_ofBaseCase` and
   `mainFormalSuccessorProjectiveCompletionObligation`, rather than
   assumed as theorem parameters.

   The paper-labelled `mainFormal` should have the hypotheses of the paper
   theorem: a projective strategy passing the low individual degree test, the
   stated parameter bounds, and the faithful formalization of the ambient
   domains.  Bridge, residual, repair, and proof-obligation inputs must be
   produced inside its proof rather than added to its statement.

### Existing bridge-like declarations

Several older declarations still name proof obligations explicitly.  They are
transitional proof debt, not a pattern to extend to paper theorem statements.
When such a declaration remains useful, its role should be one of the following:

| Declaration | Status to maintain |
|-------------|--------------------|
| `SelfImprovement.OrthonormalizationInput` | Conditional input for the Section 5 orthonormalization construction; discharge through internal proof obligations such as the QXP repair witness |
| `SelfImprovement.FinalFieldsInput` | Conditional input for final Section 9 estimates; replace at the paper theorem boundary by source-faithful statements or named internal proof obligations |
| `SelfImprovement.HelperStrongSelfConsistencyInput` | Conditional input for helper strong self-consistency estimates; keep tracked until produced |
| `SelfImprovement.SelfImprovementObligations` | Historical bundle of the preceding inputs; do not introduce as a hypothesis on a paper-labelled theorem |
| `MainFormalBaseCompletionObligations` | Base-case assembly obligations; do not expose on `mainFormal`, which is reserved for `thm:main-formal` |
| `MainFormalBaseProjectiveCompletionObligations` | Completion obligations; do not move them into a paper-facing theorem statement |
| `MainFormalPostRolePackageDiagonalOrthonormalizationResidual` | Internal residual produced from line-130 cross consistency; do not replace it by an orthonormalization-input hypothesis on `mainFormal` |
| `MakingMeasurementsProjective.OrthonormalizationInput` | Conditional input for the orthonormalization proof; keep visibly distinct from source-faithful paper statements |
| `LdPastingContext` | Faithfulness-sensitive context for `ldPasting`; audit each field against the Section 12 hypotheses and boundary conditions |

### The remaining proof obligations in `MainFormal.lean`

The direct tracked `sorry` sites in `MainFormal.lean` record two remaining
construction obligations:

1. The successor projective-completion obligation.  It must construct the
   predecessor/successor role residual, obtain the line-130 orthonormalization
   residual from cross consistency, and supply the completion data used after
   `completingToMeasurement`.
2. The base-case match-mass completion obligation, whose target is
   `MainFormalBaseBranchCompletionObligations` for the checked base-case role
   residual.

These are data-construction obligations.  Once the per-slice self-improvement
proof obligations and recursive induction data are threaded through, the
paper-labelled theorem should call the internal-obligation assembly without
adding obligations to the theorem statement.

This is the intended cleanup direction: use the conditional helper only to
identify reusable proof content, then prove the internal obligations or restore the
paper-aligned theorem with the remaining obligation visible.

### Distinction from anti-patterns

This rule addresses the same risk as conclusion-shaped-hypothesis smuggling
(anti-pattern A1 in `docs/anti_patterns.md`), but it is stricter for
paper-labelled declarations:

- A conclusion-shaped hypothesis is always unacceptable.
- A genuine intermediate fact may appear only in a separately named conditional
  helper while its obligation discharger is being proved.
- That same intermediate fact is still unacceptable as an added hypothesis on
  the public statement of the paper theorem, unless it is a faithful encoding
  of a hypothesis present in the cited source.

Obligation structures that are markers for still-unproved intermediate facts
(such as `SelfImprovementObligations`) are proof debt under this pattern.  They
should carry a tracker reference (usually an issue like #931 or #422), and their
fields should be the *assumptions* of the paper's proof, not the *conclusion* of
the theorem.

They are permitted only as temporary hypotheses of conditional helpers or
intermediate construction theorems.  If such an obligation structure appears in
the public signature of a source-labelled theorem, the theorem has become
conditional and should not be treated as the paper theorem until the structure is
produced internally or the statement is restored with the missing proof
obligation explicit.

---

## Pattern 2: Blueprint–Lean synchronization

### The three tags

The blueprint (under `blueprint/src/chapter/`) uses three LaTeX commands
to link to Lean:

| Tag | Meaning | Example |
|-----|---------|---------|
| `\lean{Name}` | The corresponding Lean declaration exists | `\lean{MIPStarRE.LDT.Test.mainFormal}` |
| `\leanok` (statement-level) | The Lean declaration compiles and its statement matches the source or blueprint statement; it does not certify proof closure | `\leanok` |
| `\leanok` (proof-level) | The proof block is fully formalized — the theorem or lemma has a complete sorry-free proof | `\lean{...}` plus `\leanok` inside `\begin{proof}` |
| `\uses{label}` | The statement or proof block depends on the cited result | `\uses{thm:orthonormalization, prop:completing-to-measurement}` |

Do not use statement-level `\leanok` for a source-labelled theorem whose Lean
declaration is conditional on bridge, residual, repair, proof-obligation input,
generic hypotheses bundle, or generic assumptions bundle
data not present in the source.

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

### Deliberate withholding of `\leanok`

Some nodes have `\lean{}` but deliberately omit either statement-level or
proof-level `\leanok`:

- **`thm:orthonormalization`** (ch04): The Lean statement carries extra
  hypotheses (`OrthonormalizationInput`) that are not yet discharged by
  all callers.  Until the full hypothesis chain is closed at
  `mainFormal`, `\leanok` is withheld.

- **`thm:naimark`** (ch04): The Lean declaration records questionwise
  local dilations, not the full tensor-product correlation statement in
  the paper.  The comment in the blueprint explicitly says "no \leanok
  is claimed."

- **`thm:main-formal`** (ch02): The blueprint links to
  `MIPStarRE.LDT.Test.mainFormal`, the intended Lean transcription of the
  theorem statement.  The tracked `sorry` sites in `MainFormal.lean` mean the
  proof chain is not yet closed, so `\leanok` is deliberately withheld for this
  theorem until the repaired-hypotheses and successor-residual obligations are
  discharged.

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
├── GlobalVariance/           # Section 8.5 (and related global variance machinery)
├── SelfImprovement/          # Section 9 self-improvement
├── CommutativityPoints/      # Section 10 commutativity setup
├── Tactic/                   # Section 10 proof orchestration utilities
├── Commutativity/            # Section 11 commutativity bounds
└── Pasting/                  # Section 12 pasting
```

### Subdirectory layout convention

Each subdirectory follows a consistent internal layout:

```
SubModule/
├── Defs.lean        # New structures, type abbreviations, error-term definitions
├── Statements.lean   # Statement-level types (hypothesis bundles, conclusion shapes)
├── Theorems.lean     # Compatibility re-export
└── Theorems/
    ├── Core.lean     # Main proof of the chapter's theorem
    ├── ...           # Supporting proof leaves
    └── Results.lean  # Re-export file for the proof leaves
```

Some larger chapters (like `Pasting/` and `SelfImprovement/`) have more
internal subdivisions (e.g., `Pasting/Bernoulli/`, `Pasting/Sandwich/`,
`SelfImprovement/Theorems/Results/`).  The outer `Theorems.lean`
compatibility module imports all the proof leaves.

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

When splitting does happen, the new leaves, declarations, and module
names must follow the mathematical naming norm in
`docs/mathematical_language.md`: name the mathematical boundary, not
the paper line number, workflow step, or implementation phase.

### Re-export files

See [Pattern 4: Compatibility re-export pattern](#pattern-4-compatibility-re-export-pattern)
below.

---

## Pattern 4: Compatibility re-export pattern

Each subdirectory with multiple internal proof leaves has a root-level
re-export file (e.g., `Theorems.lean`) that imports all the leaves:

```lean
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationInputConstructors
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Results
```

The compatibility module file itself contains no new declarations — it is purely a
re-export convenience so downstream consumers can write
`import MIPStarRE.LDT.SelfImprovement.Theorems` instead of importing
each leaf individually.

The top-level re-export file is `MIPStarRE.lean`, which imports all
subdirectories.  `MIPStarRE/LDT.lean` imports all LDT subdirectories.

**When to add to a re-export file**: When a new proof leaf is added to a
subdirectory's `Theorems/` subdirectory, add its import to the compatibility module.

**When not to add**: If a leaf is only used by one other leaf (internal
helper), don't add it to the compatibility module — let the consumer import it
directly so its API surface doesn't leak.

---

## Pattern 5: Temporary obligation-structure pattern

An obligation structure is a `structure` whose fields are **proof obligations** that
have not yet been discharged locally.  It is temporary proof debt.  Do not add a
new obligation structure unless a direct source-faithful proof route has first been
attempted and the remaining obstruction is documented.

### Example

From `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`:

```lean
structure SelfImprovementObligations (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta nu : Error) where
  helperStrongSelfConsistency :
    HelperStrongSelfConsistencyInput params strategy eps delta
  orthonormalization :
    OrthonormalizationInput params strategy eps delta
  finalFields :
    FinalFieldsInput params strategy eps delta nu
```

A separately named conditional helper may take
`(h : SelfImprovementObligations params strategy eps delta nu)` as a
hypothesis and project the needed field inside the proof body.  This does not
prove the corresponding paper theorem.  The structure should be eliminated by
internal theorems, or the source-labelled theorem should be restored with the
remaining proof obligation visible.

### Rules

1. **Every obligation field must have a theorem that produces it somewhere**, or a
   tracking issue (#931, #422, etc.) explaining when it will be produced.
2. **Docstrings must name the tracking issue and paper source.**
3. **Fields must be the *assumptions* of the paper's proof, not the
   *conclusion* of the theorem** (see A1 anti-pattern in
   `docs/anti_patterns.md`).
4. **An obligation structure must not enter a source-labelled theorem statement.**
5. **When all fields are produced**, the obligation structure should be replaced by a
   theorem that calls the same proof without non-paper obligations.

### Related patterns

- `docs/anti_patterns.md` — A1 (conclusion-shaped hypothesis), A4
  (trivial default witnesses), A6 (external `*Statement` smuggles)
- Issue [#449] — hypothesis-smuggle ledger
- Issue [#451] — historical bridge-hypothesis catalogue

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
- `docs/mathematical_language.md` — naming norm and shared-helper rules
- `docs/blueprint_style_guide.md` — blueprint notation conventions
- `docs/paper-gaps/policy.tex` — paper-gap documentation standards
- `audits/` — chapter-by-chapter scouting reports
- Issue [#449] — hypothesis-smuggle ledger
- Issue [#451] — historical bridge-hypothesis catalogue
- Issue [#931] — main-induction input gap tracker
- Issue [#422] — main-formal assembly gap tracker

[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#931]: https://github.com/LionSR/MIPStarRE/issues/931
[#422]: https://github.com/LionSR/MIPStarRE/issues/422
