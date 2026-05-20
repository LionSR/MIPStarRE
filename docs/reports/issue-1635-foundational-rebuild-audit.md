# Issue #1635: Foundational Rebuild Audit

This report records a first audit of the rebuild cost reported in issue #1635.
The issue concerns edits near the low-degree polynomial and test-definition
layers, whose mathematical content is foundational for the later pasting and
main-induction arguments.

The measurements below were taken on 2026-05-20, after PRs #1734, #1744, and
#1745 had been merged into `main`.  The local checkout reused the existing
`.lake` cache.  Thus the single-file timings measure elaboration of the named
file with its imports already available; they should not be read as clean-build
times.

## Summary

The expensive validation pattern is a dependency-cone phenomenon rather than a
slow isolated source file.

| Source module | Direct local dependents | Reverse closure, including barrels | Reverse closure, excluding root barrels |
| --- | ---: | ---: | ---: |
| `MIPStarRE.LDT.Basic.LowDegreePolynomial` | 6 | 382 | 380 |
| `MIPStarRE.LDT.Test.Defs` | 6 | 371 | 369 |
| `MIPStarRE.LDT.Pasting.Bernoulli.Final` | 5 | 31 | 29 |

The two foundational files `LowDegreePolynomial.lean` and `Test/Defs.lean`
therefore lie below almost the whole LDT formalization.  A validation target
near the final theorem will necessarily rebuild a large part of the development
after any change to either file.  By contrast, `Pasting/Bernoulli/Final.lean`
has a much smaller downstream cone: it is used mainly by the main-induction
assembly, the final theorem assembly, the pasting theorem barrel, and the axiom
audit.

## Target Import Cones

The following counts are the transitive local imports of representative targets.

| Target module | Local imports | Contains `LowDegreePolynomial` | Contains `Test.Defs` | Contains `Pasting.Bernoulli.Final` |
| --- | ---: | --- | --- | --- |
| `MIPStarRE.LDT.Pasting.Bernoulli.Final` | 202 | yes | yes | no |
| `MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems` | 330 | yes | yes | yes |
| `MIPStarRE.LDT.Test.MainTheorem` | 367 | yes | yes | yes |
| `MIPStarRE.LDT` | 385 | yes | yes | yes |

This explains the observed cost of using a final pasting or final theorem route
as the ordinary validation command for a local polynomial lemma.  The target is
mathematically downstream from the foundational files, but it is much larger
than is needed to test the local edit.

## Cached Single-File Timings

The following commands were run with `/usr/bin/time -p lake env lean FILE`:

| File | Real time | User time | System time |
| --- | ---: | ---: | ---: |
| `MIPStarRE/LDT/Basic/LowDegreePolynomial.lean` | 3.87s | 2.72s | 1.81s |
| `MIPStarRE/LDT/Test/Defs.lean` | 5.76s | 3.46s | 3.00s |
| `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean` | 6.84s | 7.41s | 3.21s |
| `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/StageMass.lean` | 6.08s | 4.36s | 3.11s |

These figures are modest.  They support the conclusion that the problematic
case in #1635 is not the intrinsic elaboration time of the changed
foundational file, but the cost of selecting a validation target whose
mathematical dependency cone includes most of the LDT development.

## Largest Downstream Files

For `LowDegreePolynomial.lean` and `Test/Defs.lean`, the largest files in the
reverse dependency cone are now mostly split proof modules.  The largest twelve
files in the reverse cone of `LowDegreePolynomial.lean`, excluding the two root
barrel modules, are:

| Lines | File |
| ---: | --- |
| 913 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean` |
| 910 | `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` |
| 876 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean` |
| 841 | `MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical.lean` |
| 839 | `MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean` |
| 823 | `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean` |
| 819 | `MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean` |
| 810 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation/BadMass.lean` |
| 802 | `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean` |
| 795 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint/Endpoint.lean` |
| 787 | `MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean` |
| 783 | `MIPStarRE/LDT/Preliminaries/Triangles.lean` |

For `Pasting/Bernoulli/Final.lean`, the largest downstream files are concentrated
in the main-induction and final-theorem assembly:

| Lines | File |
| ---: | --- |
| 910 | `MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` |
| 663 | `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` |
| 583 | `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` |
| 515 | `MIPStarRE/LDT/MainInductionStep/Theorems/StageDataConstructors.lean` |
| 503 | `MIPStarRE/LDT/MainInductionStep/Theorems/AvgSliceErrors.lean` |
| 442 | `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/AnswerSlice.lean` |

## Recommended Validation Ladder

For edits to `MIPStarRE/LDT/Basic/LowDegreePolynomial.lean`:

1. Run `lake env lean MIPStarRE/LDT/Basic/LowDegreePolynomial.lean`.
2. Run the nearest finite-answer or embedding consumer affected by the edit,
   usually one of:
   `MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean`,
   `MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean`, or
   `MIPStarRE/LDT/Pasting/BridgeLemmas/Common.lean`.
3. Run a theorem-route target only if the changed declaration is used there.
   For pasting work, prefer `lake env lean
   MIPStarRE/LDT/Pasting/Bernoulli/Final.lean` before considering a main
   induction or final theorem file.
4. Reserve `lake build`, `lake env lean MIPStarRE/LDT/Test/MainTheorem.lean`,
   and `lake env lean
   MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` for changes
   that alter public theorem statements, imports, or shared structures.

For edits to `MIPStarRE/LDT/Test/Defs.lean`:

1. Run `lake env lean MIPStarRE/LDT/Test/Defs.lean`.
2. Run the closest consumer that interprets the changed definition, usually
   `MIPStarRE/LDT/Test/StrategyCore.lean`,
   `MIPStarRE/LDT/Test/SchwartzZippelStep.lean`, or
   `MIPStarRE/LDT/Preliminaries/Defs.lean`.
3. Run `MIPStarRE/LDT/Test/MainTheorem.lean` only when the edit changes the
   statement-level interface used by the final theorem.

For edits to `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean`:

1. Run `lake env lean MIPStarRE/LDT/Pasting/Bernoulli/Final.lean`.
2. Run `lake env lean MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean`
   when the exported pasting conclusion or error bound changes.
3. Run `lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean` when the proof status
   of a source-facing theorem changes.

## Follow-Up Work

This report does not recommend an import refactor of the polynomial layer.
Those imports express genuine mathematical dependence: the later LDT
construction uses the finite-field polynomial and test-definition interfaces.
The immediate improvement is to make local validation proportional to the
changed theorem boundary.

Possible later PRs:

- Add a short note to `docs/CONTRIBUTING.md` or `docs/ci-automation.md`
  recording the validation ladder above.
- Add a small script that prints the reverse dependency cone of a Lean file,
  so future foundational edits can choose a nearby validation target without
  rebuilding the final theorem route first.
- Continue the large-file split program for the proof modules listed above,
  especially the main-induction assembly files that still sit above the final
  Bernoulli pasting theorem.
