# Issue #930 session 48 orthonormalization discrepancy audit

Audit date: 2026-05-01

Base commit: `68e3a1d9` (`origin/main` when this worktree was created)

Branch: `gpt55/session48-930-orthonormalization-audit`

## Executive summary

I audited the already-formalized orthonormalization/projective-completion slice against:

- `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean`;
- the tightly related statement and bridge definitions in `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean`, `Defs.lean`, `Projectivization.lean`, and `ProjectivizationChain.lean`;
- the projective completion helper in `MIPStarRE/LDT/Preliminaries/Completion.lean` and the completion theorem route in `MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean`;
- `references/ldt-paper/orthonormalization.tex:67-77` and `273-370`;
- `references/ldt-paper/inductive_step.tex:130-149`;
- the blueprint nodes in `blueprint/src/chapter/ch04_projective.tex` for `thm:orthonormalization`, `lem:orthonormalization-main-lemma`, the local measurement wrappers, and the `Q/X/\widehat X/P` route.

This scope intentionally avoids proof work, the live `mainFormal` residual, and the Section 6 self-improvement closure assigned to #931. I performed a non-overlap check before editing; details are recorded below.

Verdict: no new paper-gap note is needed. The formal statements in this slice are faithful to the paper once the already documented conventions are accounted for. The only visible differences are already recorded elsewhere: the explicit normalized-state convention (#933), the orthonormalization bridge inputs and blueprint status correction (#937 / PR #945), the projectivization-completion scalar correction (#904), and the harmless stronger combinatorial abstraction in the rank-reduction route (#938). I found no additional silent repair of a paper statement in `Orthonormalization.lean` or in the immediately related projective-completion route.

No Lean theorem statement or proof needs to change.

## Non-overlap check

Before editing I inspected the open PR and issue state. At that time no relevant open PR overlapped with this slice: the only open PR then visible was draft #889, which upgrades Lean/Mathlib and is unrelated to this documentation-only audit. Before pushing I checked again; #1013 had opened, but it is a CI-warning documentation PR and does not touch this audit scope. I also inspected #931 and #834:

- #931 asks for closed self-improvement inputs usable by Section 6 and `mainFormal`; this audit does not touch `SelfImprovement/**`, `MainInductionStep/**`, or `Test/MainTheorem.lean`.
- #834 is the live `mainFormal` projective-handoff residual; this audit does not attempt proof work or alter the residual.

The audit therefore stays in the requested orthonormalization/projective-completion documentation slice.

## Statement audit

### `thm:orthonormalization`

The paper states the orthonormalization theorem for a permutation-invariant state and a submeasurement `A = {A_a}` satisfying strong self-consistency:

```text
sum_a <psi| A_a \otimes A_a |psi>
  >= sum_a <psi| A_a \otimes I |psi> - zeta.
```

It concludes that there is a projective submeasurement `P = {P_a}` with

```text
A_a \otimes I approx_{100 zeta^(1/4)} P_a \otimes I.
```

The Lean theorem `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization` has the same mathematical conclusion, expressed as an `SDDRel` between the left lifts of `A` and `P.toSubMeas` with error `orthonormalizationError zeta = 100 * zeta^(1/4)` (`Defs.lean:288-290`, `Orthonormalization.lean:674-688`). The permutation-invariance hypothesis is explicit as `PermInvState psi`, and the pure-state normalization convention is explicit as `psi.IsNormalized`; this is the formal counterpart of the paper's vector state convention and is already documented in #933.

The theorem also takes `OrthonormalizationInput psi A zeta` (`Statements.lean:215-228`). This is not an undocumented change to the paper theorem. It is the current formalization boundary for the spectral-truncation and locality-preserving repair stages of the paper's proof. PR #945 removed `\leanok` from the unconditional blueprint nodes and added comments explaining that `thm:orthonormalization` and `lem:orthonormalization-main-lemma` still require these bridge inputs. The local wrappers whose statements include the extra inputs remain correctly marked as formalized.

The proof route matches the paper reduction from submeasurements to measurements. Lean completes `A` to `optionCompletion A`, whose `none` outcome is `I - sum_a A_a` (`Statements.lean:164-190`). The lemma `optionCompletion_bipartiteSSCRel` proves the completed measurement is strongly self-consistent with error `2*zeta` (`Orthonormalization.lean:58-173`), exactly reflecting the paper's `1 - 2 zeta` lower bound at `orthonormalization.tex:339-354`. The returned projective submeasurement on `Option Outcome` is restricted back to the original outcomes by `restrictSomeProjSubMeas`, and `qSDD_liftLeft_restrictSomeProjSubMeas_le` records that dropping the extra nonnegative summand cannot increase the distance (`Orthonormalization.lean:35-56` and `175-227`). This is the formal version of the paper's definition `P_a = \widehat P_a` for `a` in the original outcome set.

The large-error branch is also harmless. The paper treats the measurement lemma as trivial above its small-error regime. Lean's top-level submeasurement theorem instead returns the zero projective submeasurement when `zeta > 1/2`, using the universal `qSDD <= 1` bound and the scalar fact that `100*zeta^(1/4) >= 1` (`Orthonormalization.lean:323-345` and `739-750`). This branch weakens no paper conclusion and changes no downstream constant.

### `lem:orthonormalization-main-lemma`

The paper's measurement lemma assumes measurements `A` and `B` with `A_a \otimes I \simeq_zeta I \otimes B_a`, and concludes a projective submeasurement `P` with error `84 zeta^(1/4)` (`orthonormalization.tex:282-293`).

The formal declaration `orthonormalizationMainLemma` exposes the current bridge boundary directly. It takes:

- an explicit normalized state `psi.IsNormalized`;
- the nonnegative and bounded error hypotheses `0 <= zeta` and `zeta <= 1`;
- a `SpectralTruncationInput` for the left-lifted measurement;
- a `ProjectivizationRepairInput` for the same left-lifted measurement;
- a `ConsRel` hypothesis representing `A_a \otimes I \simeq_zeta I \otimes B_a`.

It returns a rounded projective witness for the left-lifted measurement with error `orthonormalizationMainLemmaError zeta = 84 * zeta^(1/4)` (`Defs.lean:296-298`, `Orthonormalization.lean:400-449`). The extra bridge hypotheses are the same gap documented by #937 / PR #945. The `zeta <= 1` bound is a helper-level non-vacuous-regime assumption used in the scalar comparison `12*sqrt(2*zeta) <= 84*zeta^(1/4)`; the paper handles larger values by a trivial branch, and the public submeasurement theorem has its own large-error branch.

The local wrapper `orthonormalizationMainLemma_local` specializes this route to a measurement `A` whose strong self-consistency is converted to consistency with itself (`Orthonormalization.lean:514-557`). This matches the paper's note at `orthonormalization.tex:295-297`: for a measurement on a permutation-invariant state, strong self-consistency is equivalent to consistency with itself. The wrapper also uses `LeftLiftedProjectivizationRepairInput`, which guarantees that the repaired lifted family is of the form `P_a \otimes I`; this is the formal condition needed to descend from a projective submeasurement on the product space to a local projective submeasurement. The blueprint records this as `lem:orthonormalization-main-lemma-local` and correctly includes the extra hypotheses in the informal statement.

The cross-consistency helper `orthonormalizationMainLemma_local_of_consistency` is the direct formal counterpart of the paper's measurement lemma when the locality-preserving repair input is available (`Orthonormalization.lean:565-602`). Its public measurement-level wrappers then weaken the constant from `84` to the theorem-level `100` using `84 <= 100` (`Orthonormalization.lean:606-664`). This is faithful to the paper constants.

### Projective submeasurement versus projective measurement conventions

The paper uses two different objects in the orthonormalization-to-completion chain:

1. the orthonormalization lemma produces projective submeasurements `P^A` and `P^B` (`orthonormalization.tex:73-75`, `inductive_step.tex:138-142`);
2. the completion proposition then turns those submeasurements into projective measurements `Q^A` and `Q^B` (`inductive_step.tex:143-149`).

Lean keeps this distinction explicit. `orthonormalization` returns `P : ProjSubMeas Outcome iota`, which has total operator at most the identity. The completion step is separate: `completeAtOutcome` adjoins the residual `I - P.total` at a chosen outcome (`Preliminaries/Defs.lean:254-290`), and `completeAtOutcomeProj` proves that this canonical completion is a `ProjMeas` (`Preliminaries/Completion.lean:17-80`). The projectivization chain theorem `orthonormalizeAndComplete` returns both the intermediate `P : ProjSubMeas` and the completed `Q : ProjMeas`, together with the equality `Q.toMeasurement = completeAtOutcome P.toSubMeas a0` (`ProjectivizationChain.lean:762-796`).

This resolves the concern from #937 rather than introducing a new discrepancy. The paper-facing distinction is preserved: `P` is a projective submeasurement before completion, and `Q` is a projective measurement after completion.

### Constants and scalar bookkeeping

The constants in `Orthonormalization.lean` match the paper:

- the measurement lemma error is `84*zeta^(1/4)` (`orthonormalizationMainLemmaError`);
- the public orthonormalization theorem error is `100*zeta^(1/4)` (`orthonormalizationError`);
- completing the original submeasurement by a fresh outcome doubles the self-consistency parameter to `2*zeta`;
- the scalar inequality `84*(2*zeta)^(1/4) <= 100*zeta^(1/4)` is proved as `orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError`.

The downstream projective-completion chain uses the literal completion error

```text
2 * (100*zeta^(1/4)) + 4 * sqrt(100*zeta^(1/4)) + 2*zeta.
```

This is implemented as `orthonormalizeAndCompleteError` (`ProjectivizationChain.lean:101-117`). The fact that the paper prints `200*zeta^(1/4) + 40*zeta^(1/8)` without the final `2*zeta` term is already documented in `docs/paper-gaps/issue-904-zeta2-completion.tex`; the formal cascade uses the widened `200*zeta^(1/4) + 42*zeta^(1/8)` envelope. I did not duplicate that note.

### Q/X/\widehat X/P route and existing documentation

The blueprint's `Q/X/\widehat X/P` nodes match the paper's measurement-lemma proof at `orthonormalization.tex:410-1194`. The formal development packages some SVD consequences rather than storing a full rectangular SVD object. The blueprint already says this explicitly at `def:svd-of-X`, `lem:X-squared`, `lem:X-times-X-hat`, `lem:squared-difference`, and `lem:P-Q-approx` (`ch04_projective.tex:695-708`, `784-899`, `901-917`, `943-1023`).

The only documented strengthening in this subroute is the small-overlap combinatorial abstraction: Lean does not require a nonnegativity hypothesis for the abstract ordered-averaging lemma, although the concrete overlaps in the paper are nonnegative. This is already recorded in `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex` (#938). It is a conservative strengthening and not a theorem-level gap.

## Follow-up

No new follow-up issue or paper-gap note is needed for this slice. The remaining orthonormalization work is formalization work already exposed by the bridge hypotheses and blueprint comments; it is not an undocumented paper discrepancy found by this #930 audit.

## Validation

Validation was run after adding this report:

```text
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean
lake env lean MIPStarRE/LDT/Preliminaries/Completion.lean
lake env lean MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean
rg -n "\b(sorry|axiom|admit)\b" MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean MIPStarRE/LDT/Preliminaries/Completion.lean MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean || true
git diff --check
```

A scratch `#check`/`#print axioms` file was also run for the audited public declarations `orthonormalizationMainLemma`, `orthonormalizationMainLemma_local`, `orthonormalizationMainLemma_local_of_consistency`, `orthonormalizationMeasurement`, `orthonormalizationMeasurement_of_consistency`, `orthonormalization`, `completeAtOutcomeProj`, and `orthonormalizeAndComplete`; the only reported axioms were the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
