# Issue #1586: `sorryAx` Inventory

Date: 2026-05-20.

This note records the current `sorryAx` frontier in the LDT formalization.  In
Lean, a source-level `sorry` elaborates to the kernel axiom `sorryAx`.  Thus
`sorryAx` in a transitive axiom report is not an independently declared axiom;
it is the marker for an unfinished proof.  For a paper-facing theorem, keeping a
direct proof hole is preferable to adding a bridge, residual, repair, package,
witness, or hypotheses bundle to the theorem statement.

## Direct Proof Holes

The command

```bash
rg -n '^\s*sorry\b' MIPStarRE/LDT --glob '*.lean'
```

currently reports two direct proof holes.

| Site | Declaration | Tracking issue | Mathematical obligation |
|---|---|---|---|
| `MIPStarRE/LDT/MainInductionStep/Theorems/SourceTheorems.lean:79` | `MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` | #906, under #1458 | Prove the positive-degree non-base small-error branch of the source interval `md ≤ k < 400md` for `thm:main-induction`, after the derived side condition `1 ≤ k` has been supplied by the wrapper.  The large-error branch is closed by `mainInductionOfOneLeError`, the base case is closed by `mainInductionBaseCase`, the degree-zero branch is contradictory, and the checked large-`k` range `400md ≤ k` is handled by `MainInductionStep.mainInduction`.  The interval is not made vacuous by the small-error hypothesis: `docs/paper-gaps/issue-906-main-formal-k-bound.tex` records explicit asymptotic choices with `md ≤ k < 400md` and `mainInductionError < 1`. |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:188` | `Test.mainFormal_sourceSmallErrorObligation` | #906, #930, under #1458 | Derive the non-vacuous branch of the printed two-space source theorem `thm:main-formal`, with a general projective strategy, the paper hypothesis `k ≥ md`, and `mainFormalError params k eps < 1`.  The wrapper `Test.mainFormal_sourceObligation` now proves the saturated-error branch by `Test.mainFormal_source_trivial_witness`, so only this small-error source-boundary branch remains as a direct final-theorem proof hole.  The rebuilt graph splits its mathematical content into two unproved blueprint propositions: `prop:main-formal-source-two-space-role-register` and `prop:main-formal-source-k-range-boundary`.  This branch is not empty: `docs/paper-gaps/issue-906-main-formal-k-bound.tex` records asymptotic choices in `md ≤ k < 400md` with final error below `1`. |

The source-range obligation and the final small-error source obligation are
deliberate source-boundary proof holes: they make the printed paper statements
visible in Lean and linked from the source blueprint entries, without
certifying their proofs.  They do not add bridge, residual, repair, package,
producer, or generic hypothesis fields to the source theorems.  The former
Naimark tensor-product proof hole has been discharged.
Each direct proof-hole declaration now carries an explicit `**Unfaithful:**`
docstring marker identifying the unfinished proof step, its paper source, its
tracking note or issue, and the construction expected to eliminate the
`sorryAx` dependency.

The successor theorem is intentionally stated without restricted-probability,
recursive-slice, self-improvement, pasting, residual, repair, or generic
obligation hypotheses.  The public successor wrapper
`mainInductionSuccessorNext` now splits the large-error case and calls the named
ordinary small-error construction in the nontrivial branch.  That ordinary
construction keeps only the successor strategy hypotheses and the branch
condition `mainInductionError < 1`, and is proved from the internal
answer-valued induction theorem.  The answer-valued pasting theorem
`MainInductionStep.answerLdPastingInInductionSectionOfSmallError` is now a
checked wrapper around discharged answer-valued estimates:
`answerComMainForCarrier_ofAnswerGood`,
`answerLdPastingInInductionSectionDegreeZeroOfSmallError`, and
`answerLdPastingInInductionError_le_mainInductionError_of_smallError`.  The
first of these now proves the Section 11 commutativity input from the
answer-valued Section 10 point-commutativity theorem, rather than from the
ordinary carrier's dummy diagonal measurement.

The existing formal assembly no longer leaves a successor-stage input
unproved.  In the small-error branch,
`mainInductionFromAnswerStageDataOfSmallError` proves the successor conclusion
from answer-valued restriction data, answer-valued per-slice induction data,
and answer-valued self-improvement data.  The answer-valued
restricted-probabilities theorem supplies the first of these from
`strategy.IsGood eps delta gamma`.  The predecessor induction conclusion for
the restricted answer-valued slices, corresponding to
`references/ldt-paper/inductive_step.tex:441-454`, is supplied by the
strong-induction proof of `answerMainInduction`, not as an additional theorem
hypothesis.  The final answer-valued pasting invocation at
`references/ldt-paper/inductive_step.tex:541-551` is checked inside the
current large-`k` successor route.
As of the latest repair, the low-level `ldGbcon` and one-point sandwich
transfers have axis/self-only variants.  These variants show that the
point-to-vertical-line transfer and the endpoint sandwich step do not
mathematically require the ordinary strategy's diagonal-line measurement; only
the later pasting route still needs the answer-valued diagonal verifier
relation.

The internal theorem
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier`
records this reduction in Lean: from the predecessor answer-valued induction
hypothesis, the predecessor large-`k` side condition, and the nonzero-`k` side
condition, it derives the nontrivial successor conclusion using the existing
small-error assembly and the checked answer-valued self-improvement carrier.
The nonzero-`k` side condition is derived from the small-error branch, not from
a positive-degree assumption.  The checked strengthening
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier`
derives the predecessor large-`k` side condition from the successor large-`k`
hypothesis, and the nontrivial branch derives `k ≥ 1` from
`mainInductionError < 1`.  The checked split theorem
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
then combines this small-error reduction with the already proved large-error
branch.  The newer checked theorem
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier`
uses the predecessor induction hypothesis without assuming `0 < d`, so the
former degree-zero successor construction is no longer part of the active
frontier.  The older degree-split helper
`MainInductionStep.mainInductionSuccessorNext_degreeZero_ofPastingFamily` shows
that the retired degree-zero route could use the already completed degree-zero
pasting construction once a proof supplies a complete, point-consistent slice
family and the scalar comparison with `mainInductionError`.  The checked
composition theorem
`MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitPastingObligations`
plugs this family-and-scalar route into the degree split, but this route is no
longer the active frontier.
`AxiomAudit.lean` checks the six completed helpers as standard-axiom
declarations and checks the assembled small-error construction and its public
successor wrappers as standard-axiom clean.  It also checks
that the final Section 3 role-register transport theorem
`MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness` does not
itself import this frontier; the dependency enters `mainFormal` only through the
role-induction witness supplied by Section 6.
The base-case role witness
`MainFormalRoleInductionWitness.ofBaseCase`, the conversions
`MainFormalRoleInductionWitness.toRoleMeasurementWitness` and
`MainFormalRoleInductionWitness.roleWitness`, the base specialization
`mainFormalBaseRoleInductionWitness`, and the final transport theorem
`mainFormal_ofProjectiveCompletionTransportWitness` are also checked as
standard-axiom declarations.  Thus the final-theorem witness layer does not
hide an additional proof frontier.  The successor-dependent constructor
`MainFormalRoleInductionWitness.ofMainInduction` is standard-axiom clean for
the current same-space corrected-range interface; the remaining `sorryAx`
dependencies enter only through the printed source-boundary wrappers listed
below.
The same audit checks the answer-valued restriction, per-slice induction,
self-improvement transport, and small-error stage assembly constructors used by
this route.  The linked Section 6 stage-data structures themselves are checked,
as are their constructors.  The restriction estimates, predecessor-hypothesis
predicates, answer/legacy conversion constructors, averaged-pasting invocation,
base-case theorem, and large-error theorem linked from Chapter 10 are also
checked not to import `sorryAx`.  In both the ordinary and answer-valued slice
interfaces, the transport lemmas which derive averaged point-operator
compatibility from point-measurement equality, transport restricted goodness
from verifier-visible measurement agreement, package full measurement
agreement, apply the Section 9 theorem slice by slice, and assemble the
resulting self-improvement data are all checked not to import `sorryAx`.  Thus
the former answer-valued self-improvement obstruction is discharged by
`AnswerSelfImprovementData.ofAnswerCarrier`, and the answer-valued pasting
invocation is also discharged in the current large-`k` successor route.
The Chapter 2 strategy interfaces linked from the blueprint are also checked:
the role type and involution, the two-space and same-space projective strategy
containers, their low-individual-degree failure probabilities and passing
predicates, the same-space forgetful map, the symmetric strategy container and
goodness predicate, the direct-sum role-register block lemmas, the
heterogeneous role-register state, its exchange-invariance and normalized-trace
theorems, the projective-measurement constructors, the transport-covariance
proofs for the role-register line measurements, the resulting heterogeneous
role-register `SymStrat`, the two occupied-sector expectation identities for
the `A/B` and `B/A` blocks, the three heterogeneous role-register branch
comparison theorems, the resulting `(3ε,3ε,3ε)` goodness theorem, the Alice and
Bob principal-block extraction operations for submeasurements and POVMs on
`Role × (ιA ⊕ ιB)`, their postprocessing and polynomial-evaluation
compatibility, the extraction identities for `roleRegisterProjMeas`, the
last-direction notation, the restricted diagonal sample space, and the
restricted diagonal failure probability do not import `sorryAx`.

The two-space role-register source-boundary factor-two proof has now been
formalized as a trace-compression assertion for arbitrary role-register
measurements.  The false stronger statement would identify operators before
taking the trace; this fails in the presence of off-role or off-direct-sum
blocks.  The proved assertion is that the \(AB\)-supported part of the
role-register density pairs with an arbitrary observable only through its
occupied principal block, and similarly for the \(BA\)-supported part.  The
formal endpoints are
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average`,
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm`,
and
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm`.
The source-boundary handoff
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_sourceMainInduction` now also
applies the source-shaped main-induction theorem to the heterogeneous
role-register symmetrization under the paper hypothesis `k ≥ md`.  It is not
proof-marked in the blueprint, because it inherits the open source-range
obligation from `MainInductionStep.mainInduction_sourceStatement`.
The combined theorem
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterUnsymmetrizedPointConsistency`
then extracts the two complete polynomial measurements and proves the two
factor-two point-consistency estimates for the original two-space strategy.
This combined theorem still inherits the same source-range obligation and does
not claim projectivity or final self-consistency.

The subsequent Schwartz--Zippel component is no longer a same-space obstacle:
`MIPStarRE.LDT.Preliminaries.polynomialCollisionMass_le_mdq` and
`MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound` now have
heterogeneous statements for a state on \(H_A\otimes H_B\).  The heterogeneous
triangle/SDD comparison theorem has also been proved, and
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterCompletePolynomialSelfConsistency`
combines these results to reach the complete-measurement full-polynomial
consistency relation at the end of Step 5.  This still does not claim
projectivity or scalar absorption for `thm:main-formal`.  The heterogeneous
orthonormalization steps on both tensor factors are also formalized:
`MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous`
and
`MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous`
turn a cross consistency relation between complete measurements on
\(H_A\) and \(H_B\) into SDD estimates against projective submeasurements on
\(H_A\) and \(H_B\), and
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterTwoSidedProjectiveSubmeasurements`
applies them to the source role-register data.  The completion step has also
been derived: `MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurements_ofTwoSidedSubmeasurements`
constructs the completed projective measurements and
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterCompletedProjectiveMeasurements`
applies this construction to the source role-register route.  The repaired
polynomial line-169 relations are also derived by
`MIPStarRE.LDT.ProjStrat.completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements`.
The final point-evaluation triangle is derived by
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFinalPointConsistency`, using the
heterogeneous evaluation data-processing lemmas in
`MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.Evaluation`.  The
scalar absorption from these explicit pre-absorption errors to
`mainFormalError` is now checked by
`MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofRoleRegisterScalarBoundary`,
under the scalar-cascade boundary `0 < k`.  The remaining two-space final
theorem work is the source-range boundary together with the zero-sampling
corner isolated as
`MIPStarRE.LDT.Test.mainFormal_sourceZeroKBoundaryObligation`.  The scalar
lemma `MIPStarRE.LDT.Test.mainFormalError_zero_k` records why this is a
statement-level boundary: at `k = 0` the displayed final error is exactly zero.

The former slice-transport datum had a precise formal meaning: it asked for
ordinary `SymStrat` slice strategies on which the existing Section 9 theorem
could be applied.  The active route avoids this requirement.  It applies
`selfImprovementInInductionSection_of_axisParallel_selfConsistency` to the
ordinary carrier of `xRestrictedAnswerSymStrat`, whose diagonal component is
inert.

The legacy restricted strategy `xRestrictedStrategy` is insufficient for this
purpose as it stands.  It deliberately keeps only the `zeroCoord` value of the
restricted diagonal-line answer and re-embeds that value as a constant slice
polynomial.  This is enough for the diagonal failure probability, and it is why
the answer-valued and legacy restricted-probability statements agree, but it
does not give the transport-covariant diagonal measurement required by an
ordinary `SymStrat`.

## Blueprint Proof-Level Status

The blueprint synchronization report records two proof-level gaps: the two
source-labelled statements whose remaining proof debt is factored through named
obligations above.  The corrected Lean-only current interfaces are now
proof-complete.

| Blueprint node | Lean declaration | Status |
|---|---|---|
| `thm:main-induction` | `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` | Statement-level `\leanok` only.  This is the printed paper statement with `k ≥ md`; the corrected large-`k` subrange is reduced to the current interface, while the source interval `md ≤ k < 400md` is isolated as `mainInduction_sourceRangeObligation`.  That wrapper proves its large-error branch and calls `mainInduction_sourceRangeSmallErrorObligation` only in the small-error branch; the small-error wrapper proves the base case, the non-base wrapper removes the impossible degree-zero branch, and the positive-degree wrapper derives `1 ≤ k`, leaving `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` as the direct source-range proof hole. |
| `thm:main-induction-current-interface` | `MIPStarRE.LDT.MainInductionStep.mainInduction` | Statement and proof are marked `\leanok`.  This is the corrected large-`k` interface, not the printed source theorem. |
| `thm:main-formal` | `MIPStarRE.LDT.Test.mainFormal_sourceStatement` | Statement-level `\leanok` only.  This is the printed two-space paper statement with `k ≥ md`; the wrapper `mainFormal_sourceObligation` proves the saturated-error branch and leaves the non-vacuous branch as `mainFormal_sourceSmallErrorObligation`. |
| `thm:main-formal-current-interface` | `MIPStarRE.LDT.Test.mainFormal` | Statement and proof are marked `\leanok`.  This is the same-space corrected-range interface, not the printed two-space source theorem. |

The source-labelled theorems `thm:main-induction` and `thm:main-formal` are no
longer linked to the restricted Lean declarations.  They now link to
source-faithful Lean statements whose remaining proof debt is tracked directly
or through named source-range obligations, and are intentionally left without
proof-level formalization marks until the printed source statements are proved
from their stated hypotheses.

## Statement Integrity Audit for Remaining Source Theorems

The two remaining `sorryAx` dependencies are not produced by hypotheses hidden
inside the source theorem statements.  They are proof holes in source-shaped
statements.  This distinction is mathematically important: a theorem with an
extra bridge or residual hypothesis would no longer be the theorem printed in
the paper, whereas the present declarations keep the printed hypotheses visible
and leave the missing arguments as named proof obligations.

| Source label | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `thm:main-induction` | A symmetric strategy for the `(m,q,d)` test which is `(eps,delta,gamma)`-good, and an integer `k` with `k ≥ md`; see `references/ldt-paper/inductive_step.tex:7-18`. | `params : Parameters`, `[FieldModel params.q]`, `strategy : SymStrat params ι`, `hgood : strategy.IsGood eps delta gamma`, and `hk : params.m * params.d ≤ k`, with finite and decidable index type instances. | A polynomial measurement `G` whose evaluation family is point-consistent with the point measurement at error `mainInductionError params k eps delta gamma`. | `∃ G : Measurement (Polynomial params) ι, ConsRel strategy.state (uniformDistribution (Point params)) ... (mainInductionError params k eps delta gamma)`. | Exact up to faithful formal encoding of finite index types, the field model, parameters, measurements, and consistency.  There is no bridge, residual, repair, package, producer, or generic hypothesis field.  The remaining proof debt is the source interval `md ≤ k < 400md`, represented by `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`. |
| `thm:main-formal` | A projective two-prover strategy passing the low individual degree test with probability at least `1 - eps`, and an integer `k` with `k ≥ md`; see `references/ldt-paper/test_definition.tex:180-202`. | `params : Parameters`, `[FieldModel params.q]`, a two-space projective strategy `strategy : ProjStrat params ιA ιB`, `hpass : strategy.PassesLowIndividualDegreeTest eps`, and `hk : params.m * params.d ≤ k`, with finite and decidable index type instances. | Projective polynomial measurements `G_A` and `G_B` satisfying the two point-consistency conclusions and the final self-consistency conclusion at error `mainFormalError params k eps`. | `∃ G_A : ProjMeas (Polynomial params) ιA, ∃ G_B : ProjMeas (Polynomial params) ιB, ...`, with the two point `ConsRel` conclusions and the constant-family `ConsRel` conclusion. | Exact up to faithful formal encoding of the two Hilbert-space index types, the field model, projective measurements, uniform distributions, and consistency relations.  There is no bridge, residual, repair, package, producer, or generic hypothesis field.  The remaining proof debt is the non-vacuous two-space source-boundary branch, represented by `mainFormal_sourceSmallErrorObligation`. |

## High-Risk Blueprint Link Cross-Check

The auxiliary audit

```bash
python3 scripts/audit_blueprint_high_risk_links.py --root . --ci
```

scans blueprint `\lean{...}` links whose declaration names contain words such
as `Bridge`, `Residual`, `Repair`, `Package`, `Input`, `Producer`,
`Obligation`, `Hypotheses`, `Assumptions`, `Witness`, `Statement`,
`Slackness`, or `Dominance`.  These names are not intrinsically wrong: in many
places they denote source statements, SDP slackness assertions, construction
witnesses, or Lean-only auxiliary interfaces.  They are nevertheless high risk
because they can conceal the proof-evasion pattern in which an unproved
mathematical assertion is moved into a theorem hypothesis.

The current audit scans 685 blueprint-linked Lean entries, finds 87 high-risk
entries, and reports no unaudited high-risk link.  The no-finding result means
only that every high-risk blueprint-linked declaration is explicitly covered in
`MIPStarRE/LDT/Test/AxiomAudit.lean`; it is a reviewability guard, not by
itself a proof that the linked statement matches the paper.

The high-risk links with theorem, lemma, or proposition environments split as
follows.

| Class | Status |
|---|---|
| Source-boundary theorem/proposition links `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, `MIPStarRE.LDT.Test.mainFormal_sourceObligation`, `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation`, `MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofRoleRegisterScalarBoundary`, `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation`, `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`, `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_sourceMainInduction`, `MIPStarRE.LDT.ProjStrat.sourceRoleRegisterUnsymmetrizedPointConsistency`, and `MIPStarRE.LDT.ProjStrat.sourceRoleRegisterFinalPointConsistency` | These are intentionally not proof-marked in the blueprint.  They are the live source-boundary frontier or source-boundary handoffs depending on that frontier, not hidden hypotheses on paper theorems. |
| Source-shaped proved statements with high-risk words, such as `NaimarkTensorProductCorrelationStatement`, `RazSafraSoundnessStatement`, `PolishchukSpielmanClassicalSoundnessStatement`, `SdpStatementWithSlackness`, and `AddInUFullStatement` | These are explicitly audited in `AxiomAudit.lean`.  Their high-risk words record the Lean statement interface or the SDP slackness conclusion, not an added bridge assumption. |
| Proved construction and transport lemmas with high-risk words, such as the projectivization `Repair` declarations, SDP `Witness` and `Dominance` declarations, and `SliceBoundednessInput` accessors | These are Lean-only construction or bookkeeping interfaces.  They may be linked from auxiliary blueprint entries, but they are not advertised as replacements for the source-labelled theorems unless the surrounding blueprint text states the corresponding restriction or construction role. |

This cross-check does not replace the statement-by-statement comparison against
`references/ldt-paper/`; it narrows the present proof-integrity risk.  At the
source theorem boundary, the only high-risk unproved links are exactly the two
source-frontier families already recorded in the direct proof-hole table.

The stricter paper-facing proof-debt audit

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root . --ci
```

now scans 513 paper-facing Lean references and reports no missing Lean
references, no proof-debt header findings, and no conditional declaration-name
findings.  It still reports 30 faithful boundary-input findings, all classified
as either the paper boundedness hypothesis `SliceBoundednessInput` from
`commutativity-G.tex` and `ld-pasting.tex`, or the numeric error-cascade regime
`CascadeHypotheses` from the final scalar calculation.  During this audit, the
blueprint links from the proof-marked propositions
`prop:main-induction-successor-predecessor-induction` and
`prop:main-induction-successor-answer-valued-pasting` to the conditional helper
declarations taking `AnswerMainInductionHypothesis` were removed.  The helper
declarations remain in Lean as internal reductions, but they are no longer
advertised as proof-level blueprint formalizations of those propositions.

The broader inventory

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root . \
  --broad-vocabulary --include-informational-envs --json
```

now scans 685 Lean references, including the theorem-like entries together
with blueprint definitions, remarks, and examples.  It reports no missing
references, and all theorem-like broad-vocabulary findings are classified as
faithful boundary inputs, external citations, or fixed source-construction
contexts.  After classifying the informational construction vocabulary against
the cited paper passages and audit notes, it reports no unclassified broad
header findings, no conditional declaration-name findings, 30 faithful boundary
findings, 2 external-citation findings, and 141 source-construction-context
findings.  These classifications are
deliberately explicit: definition and remark entries are allowed to name
construction data, witnesses, and local statement records only as Lean-only
interfaces, not as additional hypotheses of a source theorem.

The four formerly conditional-looking informational links are
`ProjectivizationSelfConsistencyHandoff.ofOrthonormalizeAndCompleteStatements`,
`selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion`,
`MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness`, and
`mainFormal_ofProjectiveCompletionTransportWitness`.  The audit now classifies
these exact names as Lean-only source-construction contexts only in
informational blueprint entries.  If any of them is linked from a theorem-like
entry, it remains a conditional declaration-name finding.

## Explicit Axiom Declarations

The dedicated audit

```bash
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
```

reports:

```text
Explicit Lean axiom declaration audit
scanned files: 427
findings: 0
```

Thus the current LDT tree contains no explicit Lean axiom declarations.  The
only proof-integrity markers in the kernel are the `sorryAx` dependencies
generated by the two direct proof holes above: the source-range obligation and
the final small-error source-boundary obligation.

## Transitive `sorryAx` Frontier

The file `MIPStarRE/LDT/Test/AxiomAudit.lean` records the expected transitive
axiom closure for public declarations.  After the current repairs, the only
audited public declarations expected to depend on `sorryAx` are:

| Declaration | Reason |
|---|---|
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` | This is the direct proof obligation for the positive-degree non-base small-error branch of the source interval `md ≤ k < 400md` in `thm:main-induction`, with the derived side condition `1 ≤ k`.  The branch is not contradicted by `mainInductionError < 1`; it needs a genuine source-range argument or an explicitly corrected theorem range. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation` | This is the named wrapper for the positive-degree non-base small-error source interval; it derives `1 ≤ k` from `md ≤ k`, `m > 0`, and `0 < d`, then calls `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorNonBaseObligation` | This is the named wrapper for the non-base small-error source interval; it proves the degree-zero branch by contradiction and calls `mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation` only in the positive-degree branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorObligation` | This is the named wrapper for the small-error source interval; it proves the base case by `mainInductionBaseCase` and calls `mainInduction_sourceRangeSmallErrorNonBaseObligation` only in the non-base branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation` | This is the named wrapper for the source interval `md ≤ k < 400md`; it proves the large-error branch by `mainInductionOfOneLeError` and calls `mainInduction_sourceRangeSmallErrorObligation` only in the remaining small-error branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` | This is the printed source statement of `thm:main-induction`.  In the already covered range `400md ≤ k`, it calls the corrected large-`k` interface; in the remaining range it calls `mainInduction_sourceRangeObligation`. |
| `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` | This is the direct proof obligation for the non-vacuous branch of the printed two-space source statement of `thm:main-formal`.  The rebuilt blueprint separates its mathematical content into the two-space role-register reduction and the source `k`-range and scalar-boundary issue.  It is not discharged by the saturated-error estimate. |
| `MIPStarRE.LDT.Test.mainFormal_sourceObligation` | This is the named wrapper for the printed two-space source statement of `thm:main-formal`; it proves the saturated-error branch by `mainFormal_source_trivial_witness` and calls `mainFormal_sourceSmallErrorObligation` only in the remaining small-error branch. |
| `MIPStarRE.LDT.Test.mainFormal_sourceStatement` | This is the printed two-space source statement of `thm:main-formal`; it calls `mainFormal_sourceObligation` rather than adding the missing source-boundary work as theorem hypotheses. |
The Lean docstrings for the remaining source-boundary route carry explicit
`**Unfaithful:**` markers at the theorem boundary where the unfinished proof is
used: the source-range wrappers, the source main-induction statement, and the
two source-final-theorem declarations.  These markers classify the proof status;
they do not change any public statement or add hypotheses.

The following previously listed proof holes have been discharged and are now
checked as standard-axiom declarations in `AxiomAudit.lean`: the
induction-section self-improvement theorem, the orthonormalization theorem and
main lemma, unrestricted low-degree pasting including its degree-zero branch,
the self-improvement theorem and helper theorem, the SDP slackness statement,
global variance, the ordered Laplacian spectral-gap theorem, the answer-valued
successor pasting theorem, the corrected large-`k` main-induction interface, and
the current same-space final theorem interface.
The same audit also checks that the internal Section 6 assembly theorems
`mainInductionFromStageData` and
`mainInductionFromAnswerStageDataOfSmallError` do not import `sorryAx`.
It also checks the foundational Chapter 2 strategy interfaces used to state the
current final theorem, so the remaining source-boundary frontier cannot be
hidden in the strategy definitions, failure probabilities, or last-direction
notation.

## Repair Direction

The active repair direction is now source-boundary work.  For
`thm:main-induction`, one must prove the interval
`md ≤ k < 400md` in the positive-degree, non-base, small-error regime, or else
replace the paper-facing theorem by a documented corrected range.  For
`thm:main-formal`, the two-space role-register route now reaches the final
point-consistency estimates and absorbs the explicit scalar expressions into
`mainFormalError` under the nonzero scalar-cascade boundary.  The remaining
work is to resolve the source `k ≥ md` range boundary and the zero-sampling
boundary permitted by the printed hypotheses when `d = 0` and `k = 0`; in that
corner `mainFormalError_zero_k` shows that the advertised error bound is zero.
The
answer-valued successor construction, including the final pasting invocation,
is now checked and is not part of this remaining frontier.

The same explicit-input reduction now covers the mass-comparison half of
pasting.  The no-`sorryAx` declarations
`overAllOutcomes_ofComMain_of_axis_self`, `fromHToG_ofComMain`,
`ldPastingNCompleteness_ofComMain_of_axis_self`, and
`answerLdPastingInInductionSectionOfComMainAndErrorBound` show that, after the
answer-valued Section 11 commutativity statement is supplied, the
positive-degree answer-valued pasting witness is constructed by checked Lean
code; the degree-zero branch and final scalar absorption are also proved.
The active main-induction and current same-space `mainFormal` interfaces have
therefore lost their `sorryAx` dependency.  The full printed
`thm:main-formal` still requires the separately displayed
final-theorem source frontiers:
`prop:main-formal-source-two-space-role-register`,
and `prop:main-formal-source-k-range-boundary`.
