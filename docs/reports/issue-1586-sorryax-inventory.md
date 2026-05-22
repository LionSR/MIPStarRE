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

currently reports no direct proof holes in the LDT tree.  The former
main-induction source-range proof hole has been removed after the factor \(400\)
was accepted as a confirmed statement correction, and the former final-theorem
zero-sampling obligation has been removed by the corrected source hypothesis
`0 < k`.

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
the current same-space corrected-range interface.
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
role-register symmetrization under the corrected large-`k` hypothesis
`k ≥ 400md`.  This handoff is now standard-axiom clean.
The combined theorem
`MIPStarRE.LDT.ProjStrat.sourceRoleRegisterUnsymmetrizedPointConsistency`
then extracts the two complete polynomial measurements and proves the two
factor-two point-consistency estimates for the original two-space strategy.
This combined theorem does not claim projectivity or final self-consistency.

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
under the corrected scalar-cascade boundary `0 < k`.  The scalar lemma
`MIPStarRE.LDT.Test.mainFormalError_zero_k` records why the excluded
zero-sampling corner is a statement-level boundary: at `k = 0` the displayed
final error is exactly zero.

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

The blueprint synchronization report records both corrected source-facing
theorems as proof-complete.

| Blueprint node | Lean declaration | Status |
|---|---|---|
| `thm:main-induction` | `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` | Statement and proof are marked `\leanok`.  This is the corrected large-`k` statement with `k ≥ 400md`; the printed `k ≥ md` bound is treated as a confirmed source statement gap. |
| `thm:main-formal` | `MIPStarRE.LDT.Test.mainFormal_sourceStatement` | Statement and proof are marked `\leanok`.  This is the corrected two-space statement with `k ≥ 400md` and `0 < k`; the source-boundary reduction proves the saturated-error branch and the small-error branch calls the checked role-register scalar-boundary theorem. |
| `thm:main-formal-current-interface` | `MIPStarRE.LDT.Test.mainFormal` | Statement and proof are marked `\leanok`.  This is the same-space corrected-range interface, not the printed two-space source theorem. |

The corrected source-labelled theorems `thm:main-induction` and
`thm:main-formal` are proof-complete.

## Statement Integrity Audit for Corrected Source Theorems

The remaining source-facing statements are corrected theorem statements rather
than conditional bridge theorems.  The corrections are recorded as explicit
statement changes, not as hidden package, bridge, residual, repair, producer, or
generic hypothesis fields.

| Source label | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `thm:main-induction` | A symmetric strategy for the `(m,q,d)` test which is `(eps,delta,gamma)`-good, and an integer `k` with the corrected bound `k ≥ 400md`; see `references/ldt-paper/inductive_step.tex:7-18` and `docs/paper-gaps/issue-906-main-formal-k-bound.tex`. | `params : Parameters`, `[FieldModel params.q]`, `strategy : SymStrat params ι`, `hgood : strategy.IsGood eps delta gamma`, and `hk : 400 * params.m * params.d ≤ k`, with finite and decidable index type instances. | A polynomial measurement `G` whose evaluation family is point-consistent with the point measurement at error `mainInductionError params k eps delta gamma`. | `∃ G : Measurement (Polynomial params) ι, ConsRel strategy.state (uniformDistribution (Point params)) ... (mainInductionError params k eps delta gamma)`. | Local correction for a confirmed source statement gap: the Lean statement uses the large-`k` hypothesis required by the proof through pasting, with no bridge, residual, repair, package, producer, or generic hypothesis field. |
| `thm:main-formal` | A projective two-prover strategy passing the low individual degree test with probability at least `1 - eps`, an integer `k` with the corrected bound `k ≥ 400md`, and the corrected nonzero sampling condition `0 < k`; see `references/ldt-paper/test_definition.tex:180-202`, `docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`. | `params : Parameters`, `[FieldModel params.q]`, a two-space projective strategy `strategy : ProjStrat params ιA ιB`, `hpass : strategy.PassesLowIndividualDegreeTest eps`, `hk : 400 * params.m * params.d ≤ k`, and `hk0 : 0 < k`, with finite and decidable index type instances. | Projective polynomial measurements `G_A` and `G_B` satisfying the two point-consistency conclusions and the final self-consistency conclusion at error `mainFormalError params k eps`. | `∃ G_A : ProjMeas (Polynomial params) ιA, ∃ G_B : ProjMeas (Polynomial params) ιB, ...`, with the two point `ConsRel` conclusions and the constant-family `ConsRel` conclusion. | Local correction for the confirmed large-`k` source statement gap and the zero-sampling source statement gap.  The proof is standard-axiom clean and introduces no bridge, residual, repair, package, producer, or generic hypothesis field. |

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
| Corrected source-boundary theorem/proposition links `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, `MIPStarRE.LDT.Test.mainFormal_sourceObligation`, and `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` | These are proof-marked in the blueprint after the zero-sampling boundary was corrected by the explicit hypothesis `0 < k`.  They are not hidden hypotheses on paper theorems. |
| Source-shaped proved statements with high-risk words, such as `NaimarkTensorProductCorrelationStatement`, `RazSafraSoundnessStatement`, `PolishchukSpielmanClassicalSoundnessStatement`, `SdpStatementWithSlackness`, and `AddInUFullStatement` | These are explicitly audited in `AxiomAudit.lean`.  Their high-risk words record the Lean statement interface or the SDP slackness conclusion, not an added bridge assumption. |
| Proved construction and transport lemmas with high-risk words, such as the projectivization `Repair` declarations, SDP `Witness` and `Dominance` declarations, and `SliceBoundednessInput` accessors | These are Lean-only construction or bookkeeping interfaces.  They may be linked from auxiliary blueprint entries, but they are not advertised as replacements for the source-labelled theorems unless the surrounding blueprint text states the corresponding restriction or construction role. |

This cross-check does not replace the statement-by-statement comparison against
`references/ldt-paper/`; it narrows the present proof-integrity risk.  At the
source theorem boundary, the former high-risk unproved links are now corrected
source statements checked by `AxiomAudit.lean`.

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

Thus the current LDT tree contains no explicit Lean axiom declarations, and the
corrected source-facing final theorem no longer has a `sorryAx` dependency.

## Transitive `sorryAx` Frontier

The file `MIPStarRE/LDT/Test/AxiomAudit.lean` records the expected transitive
axiom closure for public declarations.  After the current repairs, no audited
public source-facing declaration in this neighborhood is expected to depend on
`sorryAx`.

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
current final theorem, so source-boundary proof debt cannot be hidden in the
strategy definitions, failure probabilities, or last-direction notation.

## Repair Direction

The active source-boundary repair in this neighborhood has been converted into
documented statement corrections.  For `thm:main-induction`, the source-facing
statement now records the confirmed large-`k` range.  For `thm:main-formal`,
the two-space role-register route reaches the final point-consistency estimates
and absorbs the explicit scalar expressions into `mainFormalError` under the
corrected nonzero scalar-cascade boundary.  The answer-valued successor
construction, including the final pasting invocation, is now checked and is not
part of this frontier.

The same explicit-input reduction now covers the mass-comparison half of
pasting.  The no-`sorryAx` declarations
`overAllOutcomes_ofComMain_of_axis_self`, `fromHToG_ofComMain`,
`ldPastingNCompleteness_ofComMain_of_axis_self`, and
`answerLdPastingInInductionSectionOfComMainAndErrorBound` show that, after the
answer-valued Section 11 commutativity statement is supplied, the
positive-degree answer-valued pasting witness is constructed by checked Lean
code; the degree-zero branch and final scalar absorption are also proved.
The active main-induction, current same-space `mainFormal` interface, and
corrected two-space source-facing `thm:main-formal` have therefore lost their
`sorryAx` dependency.  The remaining two-space role-register node in the
blueprint is expository structure for the checked route, not a proof-hole
dependency of the source theorem.
