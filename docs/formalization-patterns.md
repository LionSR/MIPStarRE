# Formalization Patterns

Key design patterns used in the MIPStarRE Lean formalization to bridge the
gap between paper-level mathematics and a compilable Lean proof.

This document is intended for contributors who need to understand *why* the
Lean code is structured as it is, and for reviewers who need to recognize
these patterns when reading PRs.  It complements the individual chapter audits
in `audits/`, the proof-integrity rules in `docs/PROOF_INTEGRITY.md`, and the
proof-gap protocol in `docs/paper-gaps/proof-gap-protocol.tex`.

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

A declaration presented as the formalization of a paper theorem, lemma,
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

It is never allowed to change the public statement of a declaration presented
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
4. **Do not introduce conditional helpers by default.**  A helper such as
   `mainFormal_ofProjectiveCompletionTransportWitness` is a quarantine device, not a
   normal formalization pattern.  It may remain temporarily only when it
   preserves substantial proof content that cannot yet be connected to the paper
   hypotheses, has a tracked discharge or deletion target, and has no
   source-labelled blueprint `\leanok`.  If the helper would merely package
   missing work as an extra hypothesis, restore the theorem with the paper
   statement and leave a tracked `sorry` instead.
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

### Conditional helper boundary

1. **Prefer a source theorem with a tracked `sorry`.**  If a proof requires a
   construction that is not yet available from the paper hypotheses, the first
   repair is to restore the source theorem statement and leave the missing proof
   open.  Do not introduce a new `Input`, `Obligation`, `Residual`, `Repair`,
   `Producer`, or `Package` merely to avoid that `sorry`.

2. **Do not bundle several missing theorem-level steps into one hypothesis.**
   The former Section 9 bundle `SelfImprovementObligations` and the helper
   `selfImprovementFromObligations` were removed because they bundled
   helper strong self-consistency, orthonormalization, and final-field transport
   into a single route to the full self-improvement conclusion.  The correct
   boundary is now the theorem `selfImprovement`, whose missing
   proof is an explicit `sorry`.

   The former induction-section helper
   `selfImprovementInInductionSection_ofObligations` was removed because it
   encouraged propagation of the Section 9 bundle into the Section 6 successor
   constructors.  Those constructors now call the theorem
   `selfImprovementInInductionSection` directly; its current proof gap is the
   correct place for the missing work.

3. **Propagation is a warning sign.**  The consumer of
   `selfImprovementInInductionSection` — typically a
   `MainInductionStep` theorem — should close the hypothesis with an internal
   theorem as soon as possible.  If the hypothesis propagates upward toward a
   paper-labelled theorem, the PR should stop and either prove the obligation or
   restore the paper theorem with an explicit unfinished proof.

4. **Final closure at the paper theorem.**  The theorem `mainFormal` in
   `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean` is reserved for the
   paper-shaped statement.  If the witness needed by the final transport has
   not yet been constructed from the paper hypotheses, the theorem should remain
   an explicit unfinished proof.  Do not replace the missing construction by
   extra bridge, residual, repair, package, or obligation hypotheses, and do not
   proliferate named obligation declarations merely to avoid a direct `sorry`.

   The paper-labelled `mainFormal` should have the hypotheses of the paper
   theorem: a projective strategy passing the low individual degree test, the
   stated parameter bounds, and the faithful formalization of the ambient
   domains.  Bridge, residual, repair, and proof-obligation inputs must be
   produced inside its proof rather than added to its statement.  Reusable proof
   content may remain in a plainly conditional helper, such as
   `mainFormal_ofProjectiveCompletionTransportWitness`, whose statement displays the
   witness it assumes.

### Existing bridge-like declarations

Several older declarations still name proof obligations explicitly.  They are
transitional proof debt, not a pattern to extend to paper theorem statements.
When such a declaration remains useful, its role should be one of the following:

| Declaration | Status to maintain |
|-------------|--------------------|
| `mainFormal_ofProjectiveCompletionTransportWitness` | Conditional final-transport theorem; keep as reusable proof content, but do not present it as the paper theorem |
| `MainFormalDiagonalOrthonormalizationWitness` | Internal witness produced from line-130 cross consistency; do not replace it by an orthonormalization-input hypothesis on `mainFormal` |
| `LdPastingNontrivialContext` | Nontrivial-regime context for `ldPastingNontrivial`; do not present it as the unrestricted `thm:ld-pasting` context |
| `Pasting.ldPastingNontrivial` | Restricted nontrivial-regime form of `thm:ld-pasting`; link only from a Lean-only remark until the complementary trivial cases in `references/ldt-paper/ld-pasting.tex`, lines 52--55, are formalized |
| `MainInductionStep.ldPastingInInductionSectionNontrivial` | Restricted nontrivial-regime restatement of the pasting theorem for Section 6; do not present it as the unrestricted source theorem |

The former `SelfImprovement.HelperStrongSelfConsistencyInput`,
`SelfImprovement.OrthonormalizationInput`, `SelfImprovement.FinalFieldsInput`, and
`MakingMeasurementsProjective.OrthonormalizationInput` bundles have been removed.
Useful proof content should be kept as named construction lemmas, while missing
orthonormalization or final-field arguments remain direct proof gaps on the
source-facing theorem until proved from the paper hypotheses.

### Retiring auxiliary declarations

An auxiliary declaration should be removed from the main blueprint route, or
renamed and documented as a purely internal lemma, when all of the following
conditions hold.

1. It is not a statement in the cited paper and is not an explicitly cited
   outside result.
2. No current proof of a paper-level target needs it as stated.
3. It assumes stronger proof data, finite-length data, completion data, repair
   data, synchronization data, or package fields than the paper proof requires.

If such a declaration is still useful as a formal intermediate result, keep it
as a lemma or a visibly conditional helper with a planned discharge.  It should
not remain a headline replacement for the paper theorem, and it should not be
the target of a source-labelled blueprint `\leanok`.

### The remaining proof obligations in `MainFormal.lean`

The direct tracked `sorry` in `MainFormal.lean` records the remaining
construction obligation for the paper theorem.  The proof must construct, from
the hypotheses of `thm:main-formal`, the projective-completion witness consumed
by `mainFormal_ofProjectiveCompletionTransportWitness`.  The Section 6 role witness is
now obtained by applying the theorem `MainInductionStep.mainInduction`
through `MainFormalRoleInductionWitness.ofMainInductionLargeK`; the successor
branch of that call remains the tracked `sorry` in the source Section 6 theorem,
not an added hypothesis of `mainFormal`.  The remaining Section 3 work includes:

1. The successor projective-completion obligation.  It must construct the
   line-130 orthonormalization witness from cross consistency and supply the
   completion data used after `completingToMeasurement`.
2. The base-case projective-completion witness obligation, whose active target
   is a direct
   `Nonempty (MainFormalProjectiveCompletionTransportWitness ...)`
   needed by the final transport.

These are data-construction obligations.  Once the per-slice self-improvement
proof obligations and recursive induction data are threaded through, the
paper-labelled theorem should construct the witness and call
`mainFormal_ofProjectiveCompletionTransportWitness`, without adding obligations to the
theorem statement.

This is the intended cleanup direction: use the conditional helper only to
identify reusable proof content, then prove the witness construction or keep
the paper-aligned theorem with the remaining proof gap visible.

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

Obligation structures that bundle still-unproved theorem-level steps are proof
debt under this pattern.  They should not be introduced merely because a proof
is blocked.  The preferred repair is to keep the paper-labelled statement
source-faithful and make the exact missing mathematical step visible as a named
lemma or as a `sorry` in the theorem with the paper statement.

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

- **`thm:orthonormalization`** (ch04): The Lean statement is source-facing.
  Its proof still contains the tracked issue-#1032 `sorry` for the sharp
  `100 * ζ^(1/4)` constant, so proof-level `\leanok` is withheld.

- **`thm:naimark`** (ch04): The full tensor-product correlation theorem has
  no attached Lean declaration.  The formalized questionwise local interface is
  recorded separately in the restricted Lean remark
  `rem:lean-questionwise-naimark`.

- **`thm:main-formal`** (ch02): The blueprint links to
  `MIPStarRE.LDT.Test.mainFormal`, the intended Lean transcription of the
  theorem statement.  The tracked `sorry` sites in `MainFormal.lean` mean the
  proof chain is not yet closed, so `\leanok` is deliberately withheld for this
  theorem until the repaired-hypotheses and successor-residual obligations are
  discharged.

- **`thm:ld-pasting`** (ch09) and
  **`thm:ld-pasting-in-induction-section`** (ch10): The paper theorem in
  `references/ldt-paper/ld-pasting.tex`, lines 12--50, assumes
  `k >= 400md` but does not state the nontrivial-regime inequalities as
  hypotheses.  The current Lean declarations `Pasting.ldPastingNontrivial` and
  `MainInductionStep.ldPastingInInductionSectionNontrivial` prove restricted forms with
  the additional public assumptions `gamma <= 1`, `zeta <= 1`, `d <= q`,
  `0 < d`, and `1 <= k`.  Lines 52--55 of the paper explain the reduction to
  the nontrivial regime, but the complementary trivial cases have not yet been
  formalized.  The source theorem nodes therefore do not carry primary
  `\lean{}` links or statement-level `\leanok`; the checked restricted
  declarations are linked from nearby Lean-only remarks.

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
├── MainInductionStep/        # Section 6 induction theorem
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
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationSpectral
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

### Removed anti-example

The old Section 9 interface bundled helper strong self-consistency,
orthonormalization, and final-field transport into a structure named
`SelfImprovementObligations`, then used a conditional theorem to obtain the
full self-improvement conclusion.  That made the formalization look more
complete than it was.  The current code removes that bundle and leaves the
proof gap in `MIPStarRE.LDT.SelfImprovement.selfImprovement`.

### Rules

1. **Every obligation field must have a theorem that produces it somewhere**, or a
   live tracking issue (#1458, #422, etc.) explaining when it will be produced.
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
- Issue [#1458] — source-statement bridge-debt tracker
- Issue [#1507] — main-induction successor proof obligation
- Issue [#422] — main-formal assembly gap tracker

[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#1458]: https://github.com/LionSR/MIPStarRE/issues/1458
[#1507]: https://github.com/LionSR/MIPStarRE/issues/1507
[#422]: https://github.com/LionSR/MIPStarRE/issues/422
