# Issue #930 session 48 MakingMeasurementsProjective discrepancy audit

Audit date: 2026-05-01

Base commit: `68e3a1d9` (`origin/main` when this worktree was created)

Branch: `gpt55/session48-930-making-projective-audit`

> **Status note, 2026-05-20.**  The coordination paragraphs below record the
> issue state at the May 1 audit snapshot.  The old `Test/MainTheorem.lean`
> Step-6 residual and #931 self-improvement input-producer route are no longer
> the current proof frontier.  The later Section 6 small-error successor
> construction is checked, and the former source-boundary obligation wrappers
> have been retired under the documented \(k\ge400md\) and \(0<k\) statement
> corrections.  This historical audit remains valid as a statement audit for
> the projectivization support slice.

## Executive summary

I audited the already-formalized projectivization support slice against:

- `references/ldt-paper/orthonormalization.tex:36-1194`;
- `references/ldt-paper/preliminaries.tex:223-229`, `:883-949`, and `:1101-1172`;
- `references/ldt-paper/inductive_step.tex:130-185`;
- `blueprint/src/chapter/ch04_projective.tex:1-1037`, with the relevant support nodes in `blueprint/src/chapter/ch03_preliminaries.tex` and `blueprint/src/chapter/ch10_induction.tex`.

The audited Lean scope was `MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean`, `MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean`, `MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkFull.lean`, `MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean`, `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/**`, `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities.lean`, `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerData.lean`, and the completion/self-consistency support in `MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/**`, `MIPStarRE/LDT/Preliminaries/Completion.lean`, and `MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean`.

This scope intentionally excludes `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean`, since a separate orthonormalization-only audit was active in session 48. It also avoided the then-live `Test/MainTheorem.lean` Step-6 witness residual (#834), the then-#931 self-improvement input producer work assigned to `jizhengfeng`, and draft PR #889, which was the Lean/Mathlib v4.29.1 upgrade.  Open PR inspection at the audit snapshot found only draft #889; open issue inspection then found #931 and #834 as the live proof-work owners relevant to this slice.

Verdict: no new `docs/paper-gaps/` note is warranted for this slice. The checked projectivization/completion/match-mass route is faithful where it claims a paper theorem, and the genuine differences I found are already documented: the completion scalar correction is recorded in `docs/paper-gaps/issue-904-zeta2-completion.tex`; the QXP combinatorial strengthening is recorded in `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex`; normalized-state bookkeeping is recorded in `docs/paper-gaps/issue-933-quantumstate-normalization.tex`; and the orthonormalization bridge-status / projective-submeasurement packaging is documented in the blueprint after PR #945. At the time of this audit, the remaining line-169 exactness condition was still represented as an explicit internal exact-match interface. The current tree has since retired that exact interface in favor of the repaired line-169 route documented in the blueprint.

## Coordination and non-overlap

The only open PR at audit start was draft #889, `chore: upgrade Lean/Mathlib to v4.29.1`. I made no Lean or blueprint changes that could interact with that upgrade.

At the audited snapshot, issue #931 remained open and assigned to
`jizhengfeng`; it owned the self-improvement input producers for Section 6 and
was outside this audit.  Issue #834 then remained open for the `mainFormal`
Step-6 witness residual.  This audit therefore did not attempt to construct
`MainFormalRoleInductionWitness`, line-130 orthonormalization inputs,
completion producers, or match-mass witnesses for `mainFormal`.

The requested parallel orthonormalization audit has a separate worktree and branch. I read the blueprint comments needed to understand the boundary, but I did not audit or edit `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean`.

## Statement and route audit

### Naimark dilation support

The paper first states the full Naimark dilation theorem, then proves the
one-measurement helper.  This historical audit predated the repair of the full
tensor-product statement.  The current blueprint links `thm:naimark` to
`MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation`
and marks it `\leanok` in the projective-submeasurement form documented in
`docs/paper-gaps/naimark.tex`.

The audited one-measurement theorem `oneMeasNaimark` matches the paper helper. It constructs a projective submeasurement on the enlarged space `d × Option α`, using the extra `none` outcome as the auxiliary direction, and proves the normalized-trace compression identity for each original outcome (`NaimarkOneMeas.lean:238-257`). The proof follows the paper route: build the isometry column from the square roots of the submeasurement effects and the residual effect, extend it to a unitary, and conjugate the auxiliary-basis projectors (`NaimarkOneMeas.lean:247-255`, `:271-286`).

The full `naimarkTensorProductCorrelation` theorem now constructs the auxiliary
spaces, auxiliary product state, dilated state, and projective submeasurements
from these one-measurement helpers, and proves the two-sided trace identity for
bipartite correlation preservation.

### Q/X/\widehat X/P layer

The QXP support files implement the formalized part of the paper's proof of `lem:orthonormalization-main-lemma`: once the rounded projectors `R_a` and the primitive `X`, `\widehat X`, and `P` identities are supplied, Lean proves the rank-reduction, completeness, almost-projectivity, and final `P`-versus-`Q` estimates with the paper constants.

`projectiveLowRankSum` consumes an explicit `RoundingToProjectorsWitness` for the rounded family `R_a`. This is not a silent weakening of the paper proof: the blueprint and PR #945 already document that the spectral-truncation and late repair producers remain bridge inputs for the orthonormalization theorem. Conditional on that input, Lean proves the paper's rank-reduction output: a family `Q_a` of projections, the bound `Q ≤ (1+2√ζ)I`, the rank bound, and the `12√ζ` distance from `A_a` to `Q_a` (`QXPLayer/RankReduction.lean:827-866`). The `r>d` branch follows the paper's top-overlap truncation argument and uses the checked combinatorial lemma `sum_small_le_four_sqrt` (`QXPLayer/RankReduction.lean:625-800`). The already-landed note `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex` records that Lean proves the abstract double-counting lemma without the paper's automatic nonnegativity hypothesis; this is a conservative strengthening, not a new discrepancy.

The completeness and almost-projectivity constants match the paper and blueprint. Lean proves `ev_ψ(Q) ≥ 1 - 11ζ^{1/4}` in `qCompleteness` (`QXPLayer/QCompleteness.lean:69-83`), `ev_ψ(√Q) ≥ 1 - 12ζ^{1/4}` in `sqrtQCompleteness` (`QXPLayer/QCompleteness.lean:371-384`), and `∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ I` in `qAlmostProjective` (`QXPLayer/AlmostProjective.lean:17-31`).

The formal API records only the `X`, `\widehat X`, and mixed-product identities needed downstream, not an explicit rectangular SVD object. This is already explained in the blueprint at `def:svd-of-X`: the paper writes `X=UΣV†`, while Lean stores the downstream consequences `X†X=Q`, `\widehat X\widehat X†=I`, and `X†\widehat X=√Q` (`blueprint/src/chapter/ch04_projective.tex:695-708`; `QXPLayer/Core.lean:129-147`). The proof of `squaredDifference` derives the same inequality from these primitive identities (`QXPLayerIdentities.lean:245-322`), and `pQApprox` derives the paper's `30ζ^{1/4}` bound without storing an additional closeness field in the data package (`QXPLayerIdentities.lean:702-824`). This is an explicit formal packaging choice, not an undocumented paper discrepancy.

I also checked the auxiliary lemma `aLooksProjective` in `QXPLayer/RankReduction.lean`. Its public statement assumes the comparison measurement is projective, whereas the paper's displayed derivation of `eq:A-looks-projective` only needs a measurement. This does not create a new gap in the formalized proof route: the general measurement-level route is supplied by `consistencyToAlmostProjective`, whose private helper `qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect` works for arbitrary measurements and is the theorem used by the orthonormalization wrapper (`Projectivization.lean:175-183`, `:328-377`). The projective variant is therefore a redundant strengthened helper, not the formal substitute for the paper step.

### Bipartite self-consistency and completion support

The preliminary self-consistency support matches the paper's strong-self-consistency calculus with explicit hypotheses that are already documented elsewhere. `twoNotionsOfSelfConsistency` proves that bipartite strong self-consistency at level `δ` implies the state-dependent squared-distance relation at level `2δ`, under permutation invariance (`BipartiteSelfConsistency/Core.lean:304-325`). This is the paper's `prop:two-notions-of-self-consistency` in the direction used by completion and projectivization.

The local bridge `bipartiteSSC_implies_localSSC_liftLeft` converts the bipartite defect into a one-register strong-self-consistency defect for left-lifted families (`BipartiteSelfConsistency/Local.lean:21-41`). This bridge is exactly the tensor-placement bookkeeping needed by the formal completion proof. Its explicit `PermInvState` and normalized-state requirements are not new paper discrepancies; normalized-state bookkeeping for such auxiliary lemmas is already recorded in `docs/paper-gaps/issue-933-quantumstate-normalization.tex`.

The completion theorem `completingToMeasurement` matches the paper proposition after making those hypotheses explicit. It assumes a measurement `A`, a submeasurement `B`, a closeness bound `A≈_δ B`, and bipartite strong self-consistency of `A` at level `ζ`, and returns the canonical completion with error `2δ+4√δ+2ζ` (`CompletionTransfer.lean:229-254`). The structural helper `completeAtOutcomeProj` proves that completing a projective submeasurement by adding the residual mass at one outcome gives a projective measurement (`Completion.lean:17-25`). This is the exact structural fact used by the projectivization chain.

### Projectivization chain and line-156/line-169 handoff

`orthonormalizeAndComplete` composes the orthonormalization output with `completingToMeasurement` and then packages the canonical completion as a `ProjMeas` (`ProjectivizationChain.lean:730-796`). The statement returns both the intermediate projective submeasurement `P` and the completed projective measurement `Q`, together with the equality `Q.toMeasurement = completeAtOutcome P.toSubMeas a0` and the left-register completion closeness (`ProjectivizationChain.lean:628-652`, `:762-775`). This matches the paper's Step 6 construction, except for the already documented scalar correction.

The scalar discrepancy is already covered by `docs/paper-gaps/issue-904-zeta2-completion.tex`. Lean keeps the literal composed error

```text
2 * (100 * ζ^(1/4)) + 4 * sqrt(100 * ζ^(1/4)) + 2 * ζ,
```

as `orthonormalizeAndCompleteError`, and proves its absorption into `200ζ^{1/4}+42ζ^{1/8}` under `0≤ζ≤1` (`ProjectivizationChain.lean:101-149`). The paper prints the coefficient `40` without the residual `2ζ`; this was already identified and documented by #904, so this audit adds no duplicate note.

Right-register transport is explicit and checked. The helper `qSDD_liftRight_eq_liftLeft_of_permInv` turns a left-lifted squared-distance statement into the corresponding right-lifted statement under permutation invariance (`ProjectivizationChain.lean:162-180`), and `OrthonormalizeAndCompleteStatement.completedCloseness_liftRight` packages the Bob-side estimate needed for `inductive_step.tex:146-147` (`ProjectivizationChain.lean:655-677`). This is the bookkeeping added by the earlier Step-6 projectivization work and is already reflected in the blueprint remark at `blueprint/src/chapter/ch04_projective.tex:78-93`.

The line-156 handoff matches the paper constant. `ProjectivizationLine156Handoff.line156Approx` starts from the pre-projective consistency `G^A ≃_{ζ₁} G^B`, the two completion closeness estimates at `ζ₂`, converts the pre-projective consistency to a `2ζ₁` squared-distance bound, and applies the three-step triangle inequality to obtain `6ζ₁+6ζ₂` (`ProjectivizationChain.lean:240-300`). This is the paper's `ζ₃ = 6ζ₁ + 6ζ₂` calculation.

The apparent line-169 issue is also already documented rather than silent. From state-dependent-distance closeness alone, Lean proves only the honest `triangleSub` consequences with loss `ζ₁+√ζ₂` (`ProjectivizationChain.lean:540-601` in the audit snapshot). The current tree keeps the sharper repaired pre-completion route instead: it pays the square-root loss at the orthonormalization scale and uses only the checked completion helper `ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge` to show that canonical completion adds no further diagonal match-mass loss. The older exact-match interface from the audit snapshot has since been retired, so there is no longer a live hidden exactness obligation in this slice.

## Existing documented bookkeeping

No new paper-gap note is needed because the discrepancies or packaging differences in this slice are already visible in the repository:

- `docs/paper-gaps/issue-904-zeta2-completion.tex` records the missing `2ζ₁` term in the completion scalar and the formal absorption into the coefficient `42`.
- `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex` records the stronger-than-paper abstract combinatorial lemma for the small-overlaps truncation step.
- `docs/paper-gaps/issue-933-quantumstate-normalization.tex` records the explicit normalized-state hypotheses needed by auxiliary scalar, completion, and projectivization estimates.
- PR #945 adjusted the Chapter 4 blueprint so that the bridge hypotheses for the spectral-truncation and locality-preserving repair stages are explicit, and so unconditional `\leanok` is not claimed for the paper-facing orthonormalization nodes.
- PR #944 resolved the old diagonal-sandwich surrogate concern as stale; the current tensor-form switch-sandwich infrastructure matches the paper and does not create a new projectivization gap.

## Follow-up

I did not open a new follow-up issue. At the time of this audit, the only live
projectivization-related proof obligation was the already tracked #834 Step-6
witness residual. In the current tree that exact-match sub-obligation has been
retired, and the corrected large-\(k\) Section 6 small-error successor
construction is proved.  The former source-boundary obligation wrappers have
also been retired under the documented statement corrections, so this report
does not identify a current projectivization proof frontier.

## Validation

Validation was run after adding this report:

```text
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkFull.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/AlmostProjective.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities.lean
lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean
lake env lean MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean
lake env lean MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Local.lean
lake env lean MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Completion.lean
lake env lean MIPStarRE/LDT/Preliminaries/Completion.lean
lake env lean MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean
lake build MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
lake build MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer
rg -n "\b(sorry|axiom|admit)\b" \
  MIPStarRE/LDT/MakingMeasurementsProjective \
  MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency \
  MIPStarRE/LDT/Preliminaries/Completion.lean \
  MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean \
  -g '*.lean' | rg -v 'MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean' || true
git diff --check
```

A scratch `#check`/`#print axioms` file was also run for the audited public declarations `oneMeasNaimark`, `naimark`, `projectiveLowRankSum`, `qCompleteness`, `sqrtQCompleteness`, `qAlmostProjective`, `squaredDifference`, `pProjectivity`, `pQApprox`, `twoNotionsOfSelfConsistency`, `bipartiteSSC_implies_localSSC_liftLeft`, `completeAtOutcomeProj`, `completingToMeasurement`, `orthonormalizeAndCompleteError_le_absorbedZeta2`, `qSDD_liftRight_eq_liftLeft_of_permInv`, `ProjectivizationLine156Handoff.line156Approx`, `ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge`, `ProjectivizationMatchMassMonotonicity.leftConsistency`, `ProjectivizationMatchMassMonotonicity.rightConsistency`, `ProjectivizationMatchMassMonotonicity.of_submeasurement_match_mass_and_completion`, `OrthonormalizeAndCompleteStatement.completedCloseness_liftRight`, `ProjectivizationLine156Handoff.ofOrthonormalizeAndCompleteStatements`, and `orthonormalizeAndComplete`.  This validation sentence is itself a historical audit snapshot: in the current tree the retired exact-route declarations named here have been deleted, while `ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge` remains the live helper.  The only reported axioms were the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
