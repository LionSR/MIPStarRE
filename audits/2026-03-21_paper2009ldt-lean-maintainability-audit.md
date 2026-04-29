---
title: Paper2009LDT Lean maintainability audit
date: 2026-03-21
purpose: >
  Audits the Lean maintainability of the arXiv:2009.12982 LDT track and
  records structural risks for later proof development.
status: snapshot
track: paper2009ldt
kind: maintainability-audit
---

# What is structurally good

_Dated audit snapshot: this note records a 2026-03-21 maintainability review of the Lean scaffold. It is preserved as a point-in-time audit, so later fixes and renames may supersede some specific file-path observations._

- The scaffold is clear about its role. Each file starts with a short header explaining that it is a matching scaffold and naming the corresponding TeX source file. For humans, that makes navigation easy.

- The top-level routing is clean:
  - `MIPStarRE/MIPStarRE.lean` imports the active paper namespace in one place.
  - `MIPStarRE/MIPStarRE/Paper2009LDT.lean` gives a single entry point for the paper-local tree.

- The section split is mostly sensible for a matching pass. In particular:
  - `Section7ExpansionHypercubeGraph.lean` and `Section8GlobalVariance.lean` split the two logical halves of `expansion.tex` in a way that matches the source-map note.
  - `Section12Pasting.lean` isolates the longest dependency chain in its own file instead of burying it inside a larger omnibus file.
  - The theorem namespaces `MIPStarRE.Paper2009LDT.SectionX...` are stable and easy to link from the blueprint.

- Declaration naming is mostly good for ongoing blueprint work. The names are predictable, paper-aligned, and already separated by section namespace. That is the right tradeoff for a scaffold.

- The scaffold keeps repeated paper statements as separate Lean declarations when the paper states them separately. This is good. In particular:
  - `Section6MainInductionStep.selfImprovementInInductionSection` is not collapsed into `Section9SelfImprovement.selfImprovement`.
  - `Section6MainInductionStep.ldPastingInInductionSection` is not collapsed into `Section12Pasting.ldPasting`.

  For maintainability, that is better than prematurely identifying non-identical statements.

- The root namespace `MIPStarRE.Paper2009LDT` is used for shared paper nouns, while theorem declarations live in section namespaces. That is easy for a reader to browse.

- A few declarations already carry nontrivial types instead of disappearing completely into placeholder propositions. Examples include:
  - `Section3Test.mainFormal`
  - `Section7ExpansionHypercubeGraph.localToGlobal`
  - `Section12Pasting.ldDnoteq`
  - `Section12Pasting.looksEasyButTookMeAWhile`

  This helps humans see the intended mathematical shape.

- `lake build` passes. In the `Paper2009LDT` files, the warnings are the expected `sorry` warnings rather than namespace or import failures. The only non-scaffold warnings I saw were the pre-existing linter warnings in `Quantum/FiniteMatrix.lean` and one in `Quantum/Measurement.lean`.

- The repo already has an honest reusable semantic layer in:
  - `MIPStarRE/Quantum/FiniteMatrix.lean`
  - `MIPStarRE/Quantum/Measurement.lean`
  - `MIPStarRE/Quantum/OutcomeFamily.lean`

  That is structurally good for the next phase, because the scaffold has a plausible semantic destination instead of needing to invent one from scratch.

# Acceptable scaffold shortcuts

- Using placeholder error terms that currently return `0` is fine for a naming pass. Examples: `mainFormalError`, `mainInductionError`, `orthonormalizationError`, and similar definitions. They stabilize declaration names without pretending the quantitative formulas are already formalized.

- Using `default` for scaffolding constructors is also acceptable at this stage. `xRestrictedStrategy` is the clearest example.

- Keeping lightweight paper-local wrappers for paper notation is reasonable. Examples:
  - `Parameters`, `Point`, `AxisParallelLine`, `DiagonalLine`
  - `SymmetricStrategy`, `ProjectiveStrategy`
  - `IndexedPolynomialFamily`
  - `distinctTuples`, `GHatOutcome`

  These are closely tied to the paper's presentation, so there is no need to force them into a reusable global API too early.

- Section 4's notation-level aliases are acceptable as a bridge layer. Definitions such as `postProcessing`, `measurementCompletion`, `consistency`, `stateDependentDistance`, and `strongSelfConsistency` are useful if they later become thin wrappers over the honest semantic layer.

- Packaging long conclusions into helper definitions such as `...Statement` and `...Conclusion` is an acceptable scaffold shortcut in Sections 6, 9, and 12. For these chapters, the raw conjunctions would be long and hard to read. The shortcut becomes a problem only if the helper definitions stay trivial for too long.

- Using temporary abbreviations like `Fq := Fin q` or function-valued placeholders for polynomial outcomes is acceptable only as a naming scaffold. It is not a good final model, but it is a tolerable short-term shortcut if nobody starts building real proofs on top of it.

# Risky placeholder patterns

- `Section3Test.lean` currently introduces a full paper-local semantic shadow world:
  - `QuantumState`
  - `Operator`
  - `Distribution`
  - `SubMeasurement`, `Measurement`
  - `ProjectiveSubMeasurement`, `ProjectiveMeasurement`
  - `ConsistencyRel`, `StateDependentDistanceRel`, `StrongSelfConsistencyRel`
  - completeness and boundedness predicates

  This was useful to get the naming pass done quickly, but it is now starting to create technical debt. These are generic semantic notions, and the repo already has a more honest home for them under `Quantum/`.

- Many helper propositions are literally `Prop := True`. That is the biggest maintainability risk in the current scaffold. It means that large parts of the file tree no longer tell a human reader what the Lean declaration is supposed to express. It also means later refactors can silently drift without Lean noticing.

- The duplicated theorem families are not connected by shared output structures. For example:
  - `selfImprovementInInductionSectionConclusion` and `selfImprovementConclusion`
  - `ldPastingInInductionSectionConclusion` and `ldPastingConclusion`

  Even where the mathematical outputs are meant to be closely related, the scaffold currently gives Lean no way to check that they stay aligned.

- `Fq`, `Polynomial`, `AxisLinePolynomial`, and `DiagonalLinePolynomial` are currently all much too weak as mathematical models:
  - `Fq := Fin q` does not expose field structure.
  - the three polynomial-like outcome types are all just function types.

  As a temporary naming trick this is fine. As soon as real proofs begin, it will hide important distinctions rather than help.

- The paper-local names `SubMeasurement` and `Measurement` duplicate the reusable names in `MIPStarRE.Quantum.Measurement`. Right now the duplication is survivable because the scaffold does not yet import the honest layer. Once that changes, `open MIPStarRE.Paper2009LDT` will become a real source of confusion.

- `QuantumState`, `Operator`, and `Distribution` are string shells rather than thin wrappers around real objects. That is a stronger risk than ordinary `sorry` usage, because it encourages later declarations to accrete around fake semantics.

- There are a few unused or nearly-unused generic placeholders, such as `PositiveSemidefinite`, which are warning signs that the placeholder layer is broader than the current scaffold actually needs.

# Folder and import issues

- The main structural problem is the internal import order.

  Right now the files form an almost purely source-order chain:

  - `Section3Test -> Section4Preliminaries -> Section5MakingMeasurementsProjective -> Section6MainInductionStep -> Section7ExpansionHypercubeGraph -> Section8GlobalVariance -> Section9SelfImprovement -> Section10CommutativityPoints -> Section11Commutativity -> Section12Pasting`

  That is easy to build, but it is not the proof-dependency order described in `README.md`, `audits/2026-03-20_ldt-source-map.md`, and `audits/2026-03-20_ldt-blueprint-dependency-review.md`.

- This matters because the real proof order runs roughly through Sections 7--12 before Section 6. With the current import chain, `Section7ExpansionHypercubeGraph.lean` depends on `Section6MainInductionStep.lean` even though Section 7 does not need the induction theorem as mathematical input. Once Section 6 tries to import Sections 7--12 for real proofs, that source-order chain will create an import cycle.

- `Section3Test.lean` mixes two different roles:
  1. shared paper-local infrastructure needed by almost every later file;
  2. the late theorem `Section3Test.mainFormal`.

  That is not maintainable for proof filling. The shared nouns need to sit low in the dependency graph, while `mainFormal` is one of the last theorems to prove.

- `Section6MainInductionStep.lean` has a similar, smaller version of the same issue. It contains both induction bookkeeping and the theorem that later chapters are supposed to justify.

- None of the `Paper2009LDT` files currently imports the honest semantic files:
  - `Quantum/FiniteMatrix.lean`
  - `Quantum/Measurement.lean`
  - `Quantum/OutcomeFamily.lean`

  For a matching scaffold this is understandable. For ongoing development, it means the active paper tree is still structurally disconnected from the repo's actual semantics.

- The section router `MIPStarRE/MIPStarRE/Paper2009LDT.lean` is fine. The problem is not the existence of a router file; the problem is that the internal file-to-file dependencies are still organized mainly by source order instead of by reusable base layer and proof dependency.

# Recommended cleanup before real proofs

1. **Split the shared base layer away from `Section3Test.lean`.**

   Extract the paper-local shared nouns into a dedicated low-level file such as `Paper2009LDT/Basic.lean` or `Paper2009LDT/Core.lean`:
   - parameters and question/answer types;
   - strategy records;
   - paper-local geometry;
   - any paper-local notation wrappers that really are needed everywhere.

   Then let `Section3Test.lean` become a theorem file for `mainFormal` instead of the base file for the whole tree.

2. **Rewire imports to actual proof dependencies before replacing `sorry`s.**

   In particular, Sections 7--12 should not depend on Section 6 just because the TeX file appears earlier. They should import the base/preliminaries layer they actually need. Then Section 6 can safely import the later technical chapters when its proofs are filled.

3. **Choose the semantic bridge now, and stop expanding the fake semantic layer.**

   The existing `Quantum/*` files are already the more honest home for:
   - operators;
   - submeasurements and measurements;
   - postprocessing;
   - overlap bookkeeping.

   The next phase should build thin paper-local wrappers around that layer. It should not keep enriching the string-based `Paper2009LDT` placeholders.

4. **For the heaviest theorems, replace `Prop := True` output wrappers before serious proof work starts.**

   The first targets should be the conclusion packages in:
   - `Section6MainInductionStep.lean`
   - `Section9SelfImprovement.lean`
   - `Section12Pasting.lean`

   They do not need full proofs yet, but they should at least expose the intended conjunction of consistency, completeness, boundedness, and commutativity outputs. Otherwise the files remain hard to read and easy to drift.

5. **Keep paper-local only what is genuinely paper-local.**

   These are good candidates to stay inside `Paper2009LDT`:
   - point/line/diagonal-line geometry;
   - strategy packaging specific to the LDT test;
   - `xRestrictedStrategy` and other paper-specific constructions;
   - the theorem names matching paper labels.

   These are already clearly mislocated if they remain as standalone semantic objects in `Paper2009LDT`:
   - `Operator`
   - `Distribution`
   - `QuantumState`
   - `SubMeasurement` / `Measurement`
   - the generic comparison relations and boundedness/completeness predicates

6. **When the semantic rebase begins, avoid broad `open`-based mixing of the paper namespace with the reusable quantum namespace.**

   Right now `open MIPStarRE.Paper2009LDT` is harmless. Once real `MIPStarRE.Quantum` objects are imported into the same files, the duplicated names will become hard for humans to track. Qualified names or very small local aliases will be easier to maintain.

7. **Treat the current scaffold as structurally correct for naming, but not yet as the final proof layout.**

   My overall judgment is:
   - good enough for blueprint matching and declaration stabilization;
   - not yet safe to grow directly into the proof development without one round of dependency cleanup and semantic rebasing.

Low priority note: the current linter warnings in `Quantum/FiniteMatrix.lean` and `Quantum/Measurement.lean` are real, but they are not the main maintainability issue for the active `Paper2009LDT` scaffold.
