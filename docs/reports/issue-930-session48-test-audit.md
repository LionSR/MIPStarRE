# Issue #930 session 48 Test/main-formal interface audit

Base commit: `68e3a1d9` (`origin/main` when the requested worktree was verified).

Update, 2026-05-20: the positive-degree part of the finding below had been
discharged.  At that snapshot, the declaration `MIPStarRE.LDT.Test.mainFormal`
no longer assumed `0 < params.d`; the remaining interface restriction was that
it was still stated for a same-space strategy interface, rather than the
paper's general two-space projective strategy.  This report originally recorded
that restriction as a paper-gap note.  The note has since been removed because
the public `mainFormal` theorem now has the two-space statement.

At that snapshot the same declaration still assumed \(400md\le k\) and \(0<k\).  The
factor-\(400\) strengthening and the nonzero sampling-parameter boundary are
documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

Update, later on 2026-05-20: the blueprint source theorem
`thm:main-formal` had been restored to the printed paper statement.  The
then-current Lean declaration `MIPStarRE.LDT.Test.mainFormal` was linked from a
separate Lean-only main-formal interface node.  That Lean-only node explicitly
displayed the same-space interface and scalar-boundary restrictions.  Thus the
source-labelled blueprint theorem no longer presented the restricted Lean
interface as the paper statement.

Update, final 2026-05-20 audit state: the source-labelled theorem then linked to
`MIPStarRE.LDT.Test.mainFormal`, whose proof factors through
the named wrapper `MIPStarRE.LDT.Test.mainFormalConclusion`.  That
wrapper proved the saturated-error branch and left
`MIPStarRE.LDT.Test.mainFormal_smallErrorConclusion` as the direct
proof-term `sorry` frontier in the Test slice at that snapshot; the same-space
interface `mainFormal` no longer inherited proof debt through the corrected large-\(k\)
Section 6 successor theorem
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`, which
is now proved.  At that snapshot, the remaining final-theorem proof debt was
the source-boundary passage from the paper's two-space statement and printed
\(k\ge md\) range.

Update, 2026-05-23: the preceding paragraph is historical.  The corrected
source theorem now assumes the documented boundaries \(k\ge 400md\) and
\(0<k\), and the two-space source-boundary route is checked.  The remaining
differences from the literal printed theorem are the two statement corrections,
not the same-space interface restriction or a live
`mainFormal_smallErrorConclusion` proof hole.

## Executive summary

I audited the already-formalized Test interfaces around the low individual
degree test and the public `mainFormal` statement against
`references/ldt-paper/test_definition.tex`,
`references/ldt-paper/inductive_step.tex`, and blueprint chapters
`ch02_test.tex` and `ch10_induction.tex`.  In the original audit snapshot I
did not edit Lean statements or proof code, and I intentionally avoided the
then-live residual at `MIPStarRE/LDT/Test/MainTheorem.lean:4117` and the
then-#931-owned self-improvement producer assumptions.  In the current code
those residual and producer interfaces have been removed from the active route;
the corrected large-\(k\) Section 6 successor theorem
`MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`
is now proved.  After the later corrected-boundary repair, the source-boundary
wrapper for `thm:main-formal` is also checked under \(k\ge400md\) and \(0<k\).

Verdict at the audited snapshot: I found one real, previously undocumented
formal-interface restriction. The paper's `thm:main-formal` starts from an
arbitrary general projective strategy on possibly different local Hilbert
spaces. The then-current Lean interface `MIPStarRE.LDT.Test.mainFormal` was
stated for a same-space special case carrying swap-invariance data.  This
restriction has since been removed from the corrected source theorem:
`MIPStarRE.LDT.Test.mainFormal` is stated for
the general two-space `ProjStrat` container, under the documented \(k\ge400md\)
and \(0<k\) corrections.

Other apparent discrepancies are already documented or are faithful formal bookkeeping: the `ProjStrat` container itself is now the paper-faithful two-space API, the branch failure probabilities match the paper's `1/3` subtest average and `1/2` role averages, the final `ConsRel` tensor placement in `mainFormal` now matches the paper's left/right content, the widened `ζ₂` coefficient is already documented in `docs/paper-gaps/issue-904-zeta2-completion.tex`, and strategy-level normalization is already covered by `docs/paper-gaps/issue-933-quantumstate-normalization.tex`.

## Overlap check

Before auditing, I inspected the then-current open GitHub state. The only open
PR was draft #889 (`chore: upgrade Lean/Mathlib to v4.29.1`), which touched
`MIPStarRE/LDT/Test/StrategyBiProj.lean` among many upgrade files. I made no
Lean edits and did not touch that file.  At that time issue #931 owned the
remaining self-improvement producer assumptions; this is historical context for
the audit snapshot, not the current proof frontier.

## Scope audited

Lean files inspected:

- `MIPStarRE/LDT/Test/StrategyCore.lean`
- `MIPStarRE/LDT/Test/StrategyBiProj.lean`
- `MIPStarRE/LDT/Test/StrategyFailures.lean`
- `MIPStarRE/LDT/Test/SymmetrizationBridge.lean`
- `MIPStarRE/LDT/Test/Unsymmetrization.lean`
- `MIPStarRE/LDT/Test/ErrorCascade/Definitions.lean`
- `MIPStarRE/LDT/Test/ErrorCascade/EnvelopeBounds.lean`
- `MIPStarRE/LDT/Test/ErrorCascade/CascadeBounds/Final.lean`
- `MIPStarRE/LDT/Test/SchwartzZippelStep.lean`
- `MIPStarRE/LDT/Test/MainTheorem.lean`
- `MIPStarRE/LDT/Test/Classical.lean`
- `MIPStarRE/LDT/Test/SurfaceVsPoint.lean`
- `MIPStarRE/LDT/Test/AxiomAudit.lean`

Paper and blueprint files inspected:

- `references/ldt-paper/test_definition.tex`
- `references/ldt-paper/inductive_step.tex`
- `blueprint/src/chapter/ch02_test.tex`
- `blueprint/src/chapter/ch10_induction.tex`

Explicit exclusions:

- the then-live `sorry` at `MIPStarRE/LDT/Test/MainTheorem.lean:4117`;
- the then-#931-owned self-improvement producer closure work;
- Lean statement/proof edits;
- draft #889 upgrade work.

## Finding 1: the test and two-space strategy APIs match the paper at the statement layer

The paper's general projective strategy has a state on `H_A ⊗ H_B` and separate point, axis-parallel-line, and diagonal-line measurements for Alice and Bob (`test_definition.tex:98-115`). The current Lean `ProjStrat` is now a two-space container `ProjStrat params ιA ιB` with exactly that shape (`StrategyCore.lean:520-538`). The two-space pass predicate in `StrategyBiProj.lean:584-601` averages the axis-parallel role branch, point-agreement branch, and diagonal role branch with weight `1/3`, and the line branches themselves average the two role choices with weight `1/2`. This matches the verifier in `test_definition.tex:21-67`.

At the audit snapshot, the same-space API was a special case of the two-space
strategy with `ιA = ιB = ι`, together with additional permutation-invariance
data.  It was therefore a special case, not the paper's general strategy.  That
same-space API has since been removed from the active final-theorem route.

## Finding 2: the audited `mainFormal` interface was restricted to the same-space special case

The paper's `thm:main-formal` starts from a general projective strategy and then
symmetrizes it (`test_definition.tex:180-202`; `inductive_step.tex:26-66`).  At
the audit snapshot, the Lean interface `mainFormal` instead took a same-space
strategy input with a single carrier type `ι`, and no longer assumed the
historical hypothesis `hd : 0 < params.d`.  This was the separate same-space
Lean interface, not the corrected source theorem.  The corrected source theorem
`mainFormal` now starts from the paper-faithful two-space `ProjStrat` input under
the documented boundary corrections.

The same-space declaration at that stage no longer assumed `hd : 0 < params.d`;
this positive-degree restriction was discharged after the original audit.  Its
remaining non-source interface restriction was the same-space input.  This was
not the former #931 residual: it was a statement/interface restriction on the
separate same-space Lean theorem.  The former need for a heterogeneous
role-register wrapper is now historical for the source theorem: the corrected
two-space source-boundary route is checked in `mainFormal`.  The temporary
paper-gap note for the same-space restriction has therefore been removed.

## Finding 3: known theorem-interface corrections are already documented

The current `mainFormal` statement assumes `400 * params.m * params.d ≤ k`, whereas the paper prints `k ≥ md`. This is already documented as a genuine side-condition gap in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`, so I did not create a second note for it.

The error envelope in `mainFormalError` matches the paper's final displayed formula after that large-`k` correction (`ErrorCascade/Definitions.lean:47-56`; `ch10_induction.tex:422-440`). The formal cascade widens the paper's printed `ζ₂` coefficient from `40` to `42`; that deviation is already explained in `docs/paper-gaps/issue-904-zeta2-completion.tex` and in the blueprint at `ch10_induction.tex:446-465` and `ch10_induction.tex:743-762`.

Strategy-level normalization is not an undocumented discrepancy in this slice. Both `SymStrat` and `ProjStrat` bundle `state.IsNormalized` (`StrategyCore.lean:284-292`, `520-538`), matching the paper convention that strategies use normalized states. The broader distinction between the base `QuantumState` type and normalized strategy states is already documented in `docs/paper-gaps/issue-933-quantumstate-normalization.tex`.

## Finding 4: the final tensor-placement target is now paper-faithful

The historical `docs/reports/issue-238-consrel-check.md` found an older mismatch in the second consistency clause of `mainFormal`. On the current audited commit, the final target has the normalized left/right placement:

```lean
ConsRel strategy.state (uniformDistribution (Point params))
  (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
  (polynomialEvaluationFamily params G_B.toSubMeas)
  (mainFormalError params k eps)
∧ ConsRel strategy.state (uniformDistribution (Point params))
  (polynomialEvaluationFamily params G_A.toSubMeas)
  (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  (mainFormalError params k eps)
∧ ConsRel strategy.state (uniformDistribution Unit)
  (constSubMeasFamily G_A.toSubMeas)
  (constSubMeasFamily G_B.toSubMeas)
  (mainFormalError params k eps)
```

The same target is now obtained by the final weakening theorem
`retired final-transport witness route.toMainFormal`.  Since
the first `ConsRel` family acts on the left tensor factor and the second on the
right tensor factor, this expresses exactly the paper's three conclusions:
Alice's point measurement versus Bob's polynomial measurement, Alice's
polynomial measurement versus Bob's point measurement, and the two polynomial
measurements against each other. I did not find a new tensor-placement
discrepancy here.

## Finding 5: line parametrization and covariance are faithful bookkeeping

The paper's line questions are geometric lines, while the Lean APIs use concrete parametrized `AxisParallelLine` and `DiagonalLine` objects. The strategy structures therefore bundle transport-covariant line measurements (`AxisParallelCovariantMeasurement`, `DiagonalCovariantMeasurement`) so that rebasing the question line agrees with transporting answer polynomials (`StrategyCore.lean:127-222`). This is stronger than an arbitrary indexed family on parametrized lines, but it is the formal way to represent a measurement on the paper's geometric line. I do not count this as a paper discrepancy.

The last-direction notation and restricted diagonal samples also match the paper: `lastDirectionLine` and `lastDirectionMeasurementFamily` implement `not:conditioned-on-last-direction` (`StrategyCore.lean:363-382`; `test_definition.tex:155-166`), and `RestrictedDiagonalSample` encodes the paper's `j`-restricted diagonal lines test with Lean's `Fin params.m` indexing shifted by one (`StrategyCore.lean:307-327`; `test_definition.tex:168-175`).

## Finding 6: the classical soundness interface is an explicit hypothesis, not an ambient axiom

The overview-level theorem `classicalTestSoundness` intentionally keeps the
external Polishchuk--Spielman soundness theorem as an explicit specialized
hypothesis.  This differs from a direct formal proof of the cited classical
theorem.  The current blueprint chapter 1 therefore leaves the source-labelled
external theorem unlinked and records the conditional corollary separately as
`prop:lean-classical-test-soundness-interface`, whose statement displays the
specialized external hypothesis.  The CI-facing `AxiomAudit.lean` regression
check confirms that this corollary depends only on the standard Lean axioms once
that explicit hypothesis is supplied.

## Finding 7: submeasurement/projective conventions are locally consistent

The source target `thm:main-formal` returns projective measurements (`ProjMeas (Polynomial params) ι`) as in the paper. Intermediate Section 6 and pasting interfaces often use projective submeasurements or submeasurements because the paper itself passes through incomplete measurements before completion. In the audited Test slice, those intermediate APIs are exposed as internal witness or construction targets rather than silently weakening the final theorem. The remaining completion and successor-stage proof obligations are tracked separately; this session-48 audit did not attempt to discharge them.

## Validation

The following checks were run from `/private/tmp/mipstar-session48/test-audit`.

Targeted Lean checks succeeded for the audited Test files:

```text
lake env lean MIPStarRE/LDT/Test/StrategyCore.lean
lake env lean MIPStarRE/LDT/Test/StrategyBiProj.lean
lake env lean MIPStarRE/LDT/Test/StrategyFailures.lean
lake env lean MIPStarRE/LDT/Test/SymmetrizationBridge.lean
lake env lean MIPStarRE/LDT/Test/Unsymmetrization.lean
lake env lean MIPStarRE/LDT/Test/ErrorCascade/CascadeBounds/Final.lean
lake env lean MIPStarRE/LDT/Test/SchwartzZippelStep.lean
lake env lean MIPStarRE/LDT/Test/Classical.lean
lake env lean MIPStarRE/LDT/Test/SurfaceVsPoint.lean
lake env lean MIPStarRE/LDT/Test/MainTheorem.lean
lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean
```

`MainTheorem.lean` emitted the expected warning that `mainFormal` uses `sorry`;
the other targeted files were clean.  A scratch check confirmed the key type
signatures used in this audit at that time: `ProjStrat` was two-space,
`ProjStrat.PassesLowIndividualDegreeTest` was available from `StrategyBiProj`,
and `mainFormal` took a same-space strategy input, `0 < params.d`,
`400 * params.m * params.d ≤ k`, and `0 < k`.  The positive-degree hypothesis
and the same-space input have since been removed from the public `mainFormal`;
the scalar-boundary assumptions remain as documented corrections.

Scratch `#print axioms` checks showed only `[propext, Classical.choice,
Quot.sound]` for `classicalTestSoundness`,
`mainFormal_trivial_witness`, the final main-formal target weakening theorem,
and the same-space symmetrization bound then used by the same-space route.  The
unused same-space symmetrization package layer has since been removed.  The
same scratch file showed
`sorryAx` for `mainFormal`, exactly as expected from the excluded live residual
in the audit snapshot.  That historical `sorryAx` route through the Section 6
successor construction has since been discharged for the corrected large-\(k\)
interface.  The later source-boundary small-error wrapper named below is also
now checked under the corrected \(k\ge400md\) and \(0<k\) hypotheses.

The audited-scope grep in the original snapshot

```text
rg -n "\b(sorry|admit|axiom|unsafe|native_decide)\b" MIPStarRE/LDT/Test -g '*.lean'
```

found only documentation mentions of the former ambient axiom and the expected
`sorry` comment/proof term in `MainTheorem.lean`; the only actual proof-term
`sorry` was then at `MainTheorem.lean:4117`.  This proof-frontier paragraph is
historical.  In the current tree, the corrected two-space source theorem assumes
the documented boundaries \(k\ge400md\) and \(0<k\); the former
`MIPStarRE.LDT.Test.mainFormal_smallErrorConclusion` wrapper is checked,
and there is no live Test-slice proof-term `sorry` attached to that
source-boundary route.

The temporary paper-gap note created during the original audit compiled
successfully.  That note is no longer present in the repository, because the
same-space restriction it documented has been eliminated from the public
two-space `mainFormal` theorem.

`git diff --check` passed on the final diff.
