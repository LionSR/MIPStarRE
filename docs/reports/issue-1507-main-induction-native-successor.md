# Issue #1507 main-induction native successor obligation

Audit date: 2026-05-18.

Last status update: 2026-05-22.  The classifications below incorporate the
current split between the printed source theorem `thm:main-induction` and the
separate corrected large-`k` Lean interface
`thm:main-induction-current-interface`, together with the axiom-audit evidence
recorded in `MIPStarRE/LDT/Test/AxiomAudit.lean`.

Later update on 2026-05-22: the corrected large-`k` successor route is now
proof-complete.  Older paragraphs in this report describe the answer-valued
pasting invocation, the enclosing predecessor induction, and the printed source
range as active frontiers; those statements are historical.  The present
source-facing route treats the factor `400` as a confirmed statement correction
and no longer carries a source-range proof-obligation declaration.

Update on 2026-05-21: the predecessor answer-valued induction hypothesis no
longer assumes `0 < params.d`.  The recursive slice route is therefore
available also in the case `d = 0`; the side condition `1 ≤ k` is derived from
the nontrivial branch `mainInductionError < 1`.  The checked theorem
`mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound` shows that the
small-error successor construction reduces to the predecessor induction
argument with the successor large-`k` bookkeeping already discharged.  The
source-facing theorem `mainInductionSuccessorNext_ofSmallErrorConstruction`
then supplies that predecessor argument from `answerMainInduction`.  The
answer-valued slice self-improvement construction is checked directly, and the
earlier degree-zero family-and-scalar branch is retired as an artifact of the
former internal hypothesis, not a separate requirement of the paper proof.
The checked theorem `mainInductionSuccessorNext` adds the complementary
large-error branch, so the full successor conclusion is now available from the
successor strategy hypotheses alone.

Update on 2026-05-22: the answer-valued ambient point-consistency averaging
step is now checked.  The lemmas
`answer_family_pointConsistencyError_eq_avg` and
`answer_family_consistency_of_slice_bounds` prove, respectively, the
Fubini/reindexing identity over
`Point params.next ≃ Point params × Fq params` for an ambient
`AnswerSymStrat`, and the consequence that slice-wise consistency estimates
average to the ambient consistency estimate.  These lemmas are audited in
`MIPStarRE/LDT/Test/AxiomAudit.lean` as `sorryAx`-free.  Thus the remaining
answer-valued averaged assembly is not the point-consistency calculation.

The ordinary family-level averaging components have also been separated from
the monolithic assembly theorem.  The lemmas
`idxPolyFamily_complete_of_slice_bounds`,
`idxPolyFamily_stronglySelfConsistent_of_slice_bounds`, and
`idxPolyFamily_sliceBoundednessInput_of_slice_bounds` prove the completeness,
strong self-consistency, and boundedness fields from the corresponding
slice-wise estimates.  The ordinary `assembleAveragedPastingData` now consumes
these lemmas.  All three are audited as `sorryAx`-free.  At this stage of the
repair the remaining work was to state and prove the `AnswerSymStrat` ambient
analogue needed by the simultaneous successor theorem.  The later updates in
this report record the subsequent proof of that answer-valued pasting route.

The answer-valued successor scalar averaging estimate has also been separated
from the ambient pasting question.  The lemmas
`average_answerSuccessorSliceSelfImprovementError_le`,
`average_answerSuccessorSliceMainInductionNu_le` and
`average_answerSuccessorSliceMainInductionError_le` prove the `zeta_x`,
`nu_x`, and `sigma_x` Jensen and conditioning estimates for an
`AnswerSuccessorRestrictedFailureProfile`, i.e. for the actual restricted
profiles of an ambient `AnswerSymStrat` successor.
The theorem
`answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis` then
extracts the recursive slice measurements from the predecessor answer-valued
induction hypothesis and proves the averaged `sigma_x` estimate.  The theorem
`answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis` applies the
axis-parallel/self-consistency form of self-improvement to those slices and
constructs the projective slice submeasurements and witnesses, together with
the averaged `zeta_x` and `sigma_x` bounds.  These declarations are audited as
`sorryAx`-free.  The theorem
`answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis` now assembles
these outputs into an ambient answer-valued polynomial family: it proves
averaged completeness, point consistency with the actual answer-valued point
measurement, strong self-consistency, the carrier-typed slice boundedness
input, and the averaged `kappa` and `zeta` scalar bounds.  The boundedness
input is still typed through `answerSelfImprovementCarrier` because the
existing boundedness interface is an ordinary-strategy interface; this is not a
claim that the carrier's dummy diagonal measurement satisfies the
answer-valued diagonal-line test.  The answer-valued pasting invocation was
isolated as
`answerLdPastingInInductionSectionOfSmallError`.  The checked reduction
`answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting` shows
that, with the predecessor answer-valued induction hypothesis in the successor
context, the successor branch reduces to this answer-valued pasting theorem.
Thus, at this intermediate stage, the `AnswerSymStrat` successor assembly was
not blocked on the recursive-call output, the slice-wise self-improvement
output, the averaged recursive and self-improvement error bounds, or the
family-level averaging fields.  The remaining item was the answer-valued final
pasting invocation, which is recorded below as subsequently proved.

For answer-valued self-improvement data attached to an ordinary ambient
strategy, the corresponding fields are now also checked directly:
`AnswerSelfImprovementData.complete_of_slice_bounds`,
`AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds`,
`AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds`, and
`AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds`.  These
consume the answer-slice self-improvement average bound
`average_answerSliceSelfImprovementError_le`; together with
`average_answerSliceError_le`, they feed the direct theorem
`mainInductionFromAnswerStageDataOfSmallErrorDirect`.  The exported assembly
`mainInductionFromAnswerStageDataOfSmallError` now calls this direct proof
instead of converting through the legacy `SelfImprovementData` record.  This
removes another conversion layer from the ordinary answer-valued route.  At
this stage it did not close the ambient `AnswerSymStrat` successor theorem; the
later answer-valued successor route closes that theorem.

Update later on 2026-05-22: the first pasting transfers have been separated
from the diagonal-line test hypothesis.  The lemmas
`Pasting.pointVerticalLineSdd_of_axis_self`,
`Pasting.ldGbcon_of_axis_self`,
`Pasting.ldGbcon_liftedVerticalLine_of_axis_self`,
`Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self`,
`Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self`,
`Pasting.ldSandwichLineOnePoint_core_of_axis_self`, and
`Pasting.ldSandwichLineOnePoint_ofGHatFacts_of_axis_self` now state the actual
dependencies of those steps: the axis-parallel test, point self-consistency,
and, where scalar estimates require it, nonnegativity of `gamma`.  The original
source-facing names remain as wrappers.  This does not prove the final
answer-valued pasting theorem, but it removes a spurious full-good-strategy
dependency from the part of the pasting proof where the diagonal measurement is
not mathematically used.

## Scope

This note records the repair batch for the main-induction proof frontier.  The
source-labelled blueprint node `thm:main-induction` is the printed theorem with
the paper hypothesis `k >= md`; the current Lean declaration is now linked from
the separate corrected large-`k` interface
`thm:main-induction-current-interface`.  The public graph on the GitHub Pages
branch predates this split and marks `thm:main-induction` blue, while
`lem:main-induction-base` and `def:successor-pasting-data` are green.  Thus the
historical obstruction inspected by this note was the successor branch of the
corrected formal interface, not the base case or the already formalized
pasting data.  In the current working tree that corrected successor branch is
checked; the remaining Section 6 source-boundary obstruction is the printed
range `md <= k < 400md`.

## Source comparison

The source theorem is `references/ldt-paper/inductive_step.tex:7-18`, with the
successor proof at `references/ldt-paper/inductive_step.tex:441-551`.  The proof
is naturally a step from dimension `m` to dimension `m + 1`: for a good
symmetric strategy in dimension `m + 1`, one restricts to each height
`x \in F_q`, applies the induction hypothesis in dimension `m`, self-improves
the slice measurements, averages the resulting estimates, and invokes the
induction-section pasting theorem.

The blueprint source theorem in `blueprint/src/chapter/ch10_induction.tex` now
records the confirmed correction from the printed `k >= md` hypothesis to
`k >= 400md`, following
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  It links to the Lean
declaration `MIPStarRE.LDT.MainInductionStep.mainInduction`, and the corrected
successor proof is proof-complete.

## Classification

`thm:main-induction`: source theorem.

Classification: corrected source statement, linked to
`MainInductionStep.mainInduction_sourceStatement`.  The printed hypothesis
`k >= md` has been replaced by the documented correction `k >= 400md`; no
source-range obligation remains in the active route.

`thm:main-induction-current-interface`: corrected Lean interface.

Classification: checked corrected interface.  The Lean theorem has the
source-shaped conclusion and corrected large-`k` hypotheses.  The printed range
is now treated as a documented statement correction, not as a remaining proof
hole.

`mainInductionSuccessorNext`: Lean successor obligation.

Classification: checked successor theorem for the corrected large-`k` route.
This is the native `m -> m + 1` successor statement.  It carries no
restricted-probability, recursive-slice, self-improvement, or pasting data as
hypotheses.

`mainInductionSuccessor`: Lean branch theorem.

Classification: boundary transport.  This handles the arbitrary non-base
parameter presentation by decomposing it as a successor and then calling
`mainInductionSuccessorNext`.

`mainInductionFromStageData` and
`mainInductionFromAnswerStageDataOfSmallError`: existing Lean assembly theorems.

Classification: internal assembly theorems.  The first consumes the ordinary
restriction, induction, self-improvement, and averaged pasting data.  The
second is the answer-valued small-error wrapper used by the current successor
route: once the answer-valued restriction, per-slice induction, and
self-improvement data are constructed, it now calls the direct theorem
`mainInductionFromAnswerStageDataOfSmallErrorDirect`, which invokes the
induction-section pasting theorem from the answer-valued fields and scalar
estimates.  Neither theorem is advertised as `thm:main-induction`, and neither
supplies an extra hypothesis to the source statement.  The file
`MIPStarRE/LDT/Test/AxiomAudit.lean` checks both assembly theorems as free of
`sorryAx`, so they are not part of the remaining proof frontier.

## Repair

The corrected large-`k` successor route has now been repaired.  The ordinary
successor theorem `mainInductionSuccessorNext_ofSmallErrorConstruction` has
only the successor strategy hypotheses and the small-error branch condition; it
is proved from the internal answer-valued induction theorem and the checked
answer-carrier reduction.  The predecessor answer-valued induction argument is
supplied by the strong-induction proof of `answerMainInduction`.  The native
successor theorem `mainInductionSuccessorNext` splits the already proved
large-error branch from this nontrivial construction.  The public branch
theorem `mainInductionSuccessor` performs the predecessor decomposition for
`params.m != 1` and then calls the checked successor theorem.

The answer-valued ingredients used in this proof are no longer hypotheses of
the successor statement.  The theorem
`mainInductionFromAnswerStageDataOfSmallError` turns answer-valued restriction
data, answer-valued per-slice induction data, and answer-valued
self-improvement data into the desired successor conclusion.  The
answer-valued restricted-probabilities theorem supplies the restriction data
from `strategy.IsGood eps delta gamma`.  The internal theorem
`mainInductionSuccessorNext_ofAnswerCarrier` records
the corresponding reduction under a predecessor answer-valued induction
hypothesis, the predecessor large-`k` side condition, and the nonzero-`k` side
condition.  The strong-induction proof supplies the predecessor hypothesis, and
the elementary side conditions are derived in the successor branch rather than
postulated.

The checked theorem
`mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound`
removes the elementary size bookkeeping from this frontier.  From the successor
hypothesis `400(m+1)d <= k`, Lean derives the predecessor hypothesis
`400md <= k`; from the small-error branch it derives `k >= 1`.  It then calls
the answer-valued successor assembly above.  Thus the large-`k` side condition,
the nonzero-`k` side condition, and the predecessor induction hypothesis are
not additional assumptions of the public successor theorem.

The theorem `mainInductionSuccessorNext` records the all-error conclusion in
the current answer-carrier route: the small-error branch invokes
`mainInductionSuccessorNext_ofSmallErrorConstruction`, and the complementary
branch invokes `mainInductionOfOneLeError`.
The axiom audit also checks the linked base-case theorem, large-error theorem,
restricted-probability estimates, predecessor-hypothesis predicates,
answer/legacy conversion constructors, and averaged-pasting invocation as
free of `sorryAx`.  Thus the current proof debt is not in those bookkeeping or
reduction declarations.

The answer-carrier successor route removes the former degree-zero obstruction.
It uses the predecessor induction hypothesis for the restricted slices without
assuming `0 < d`, and derives `1 <= k` from the small-error branch.  Therefore
the successor route does not require a separate degree-zero polynomial-family
construction.  The older slice-transport and degree-split helpers had no
remaining caller after this repair and have been removed rather than retained as
separate inactive routes.

The answer-valued pasting invocation for the ambient successor strategy has
now been proved internally in the successor route.  It has not been promoted to
a public hypothesis of `mainInduction`, `mainInductionSuccessorNext`, or
`mainFormal`.

The paper-to-Lean correspondence is now as follows.  Lines
`441-454` of `references/ldt-paper/inductive_step.tex` are the recursive
predecessor call, represented in Lean by `AnswerPerSliceInductionData` and the
local induction hypothesis supplied by `answerMainInduction`.  Lines `456-485` are the
slice-wise self-improvement step, represented by `AnswerSelfImprovementData`
and now constructed by `AnswerSelfImprovementData.ofAnswerCarrier`.  Lines
`487-550` are the averaging of the slice-wise
properties.  The point-consistency component of this averaging is now checked
directly for an ambient `AnswerSymStrat` by
`answer_family_pointConsistencyError_eq_avg` and
`answer_family_consistency_of_slice_bounds`.  The ordinary family-level
completeness, self-consistency, and boundedness calculations are now checked
separately by `idxPolyFamily_complete_of_slice_bounds`,
`idxPolyFamily_stronglySelfConsistent_of_slice_bounds`, and
`idxPolyFamily_sliceBoundednessInput_of_slice_bounds`.  For answer-valued
self-improvement data over an ordinary ambient strategy, the fields are checked
directly by `AnswerSelfImprovementData.complete_of_slice_bounds`,
`AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds`,
`AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds`, and
`AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds`.  The direct
ordinary-ambient answer-valued assembly
`mainInductionFromAnswerStageDataOfSmallErrorDirect` invokes
`ldPastingInInductionSection` from these fields and the answer-valued averaged
scalar estimates, and the exported theorem
`mainInductionFromAnswerStageDataOfSmallError` calls this direct proof.  The
corresponding `AnswerSymStrat` ambient versions of these fields have now been
assembled without using the dummy diagonal carrier as a substitute for the
given strategy.  Lines `552-623` are the final pasting invocation and scalar
absorption; the scalar estimates in the answer-valued route and the full
ambient answer-valued pasting interface are now checked.  The older separate
degree-zero family route is retained only as a checked composition lemma and is
not part of the active successor route.

The recursive predecessor argument is not a new mathematical hypothesis about
the given successor strategy.  It is the induction hypothesis for dimension
`m`, applied to the restricted strategies at heights `x \in F_q`, and it is now
produced by the strong-induction proof of `answerMainInduction`.  The remaining
source-boundary repair is not to add a predecessor-conclusion hypothesis
anywhere; it is to handle the printed source range and the final theorem
wrapper from the paper hypotheses.

Update on 2026-05-22: the answer-valued base case
`answerMainInductionBaseCase` is also checked.  It uses the same
one-dimensional axis-parallel-line construction as `mainInductionBaseCase`;
the function-valued diagonal answer interface is irrelevant in dimension one.
The answer-valued large-error branch `answerMainInductionOfOneLeError` is also
checked, by the same distinguished trivial polynomial measurement as
`mainInductionOfOneLeError`.  These supply the base and saturated-error branches
of the simultaneous answer-valued recursion.  The successor predecessor
hypothesis is supplied by the strong-induction proof of `answerMainInduction`.

This was the main place where a formally green intermediate theorem would have
been misleading.  A theorem named as the small-error successor construction,
but proved only from an assumed predecessor conclusion that was not produced by
an actual induction on `m`, would not have proved the successor step of the
paper.  The current proof avoids that error by using `answerMainInduction`; the
later source-boundary repair replaces the former source-range and final-theorem
wrappers by corrected proof-complete statements.

The former slice-transport obstruction is no longer part of the active route.
The restricted slice used for the recursive call is represented by
`xRestrictedAnswerSymStrat`, and
`AnswerSelfImprovementData.ofAnswerCarrier` now obtains the needed
self-improvement data by applying the axis-parallel/self-consistency form of
Section 9 to an ordinary carrier with an inert diagonal measurement.
The next simultaneous-induction construction has also been made explicit:
`xRestrictedAnswerSymStratOfAnswer` restricts an answer-valued successor
strategy to an answer-valued predecessor slice while preserving the full
function-valued diagonal answer.  This removes a definitional obstruction to
stating the recursive answer-valued induction theorem; it does not by itself
prove the predecessor induction argument.
The matching restricted-probability theorem for an answer-valued successor,
`answerSuccessorRestrictedProbabilities`, is now also checked.  Its diagonal
part is proved directly for the function-valued diagonal answers, rather than
by realizing the diagonal measurement as an ordinary low-degree polynomial
measurement.  The theorem `answerSuccessorRestrictedSliceConclusions` now
performs the actual recursive call for these answer-valued successor slices:
from the predecessor answer-valued induction hypothesis, the successor
large-`k` bound, and the small-error branch, it derives the main-induction
conclusion for every restricted slice.  Thus the remaining
recursive-predecessor frontier is no longer a missing slice definition,
restricted-probability estimate, or local application of the predecessor
induction hypothesis.  What remains is to place this answer-valued recursive
argument inside a genuine induction on the dimension.

The legacy restricted object `xRestrictedStrategy` is still not an ordinary
realization of the answer-valued diagonal interface.  It is a
`RestrictedSymStrat`, not a `SymStrat`, and its diagonal measurement keeps only
the sampled base-point value before re-embedding it into the degree-bounded
slice-polynomial alphabet.
The former ordinary-realization slice-transport constructors have been retired
from the checked route.  The active route no longer needs such ordinary
realizations: it applies the axis-parallel/self-consistency form of
self-improvement to the ordinary carrier of the answer-valued slice.  A
low-degree support theorem is therefore not needed for this stage, though it
would still be the theorem needed for a stronger ordinary-realization route.
The older degree-bounded restricted strategy `xRestrictedStrategy` cannot simply
fill this role.  Its diagonal measurement `restrictDiagonalMeasurement`
postprocesses an ambient slice-preserving diagonal answer to the value at
`zeroCoord` and then embeds that value as a constant slice polynomial.  This
preserves the verifier-visible diagonal test used in the restricted-probability
calculation, but it does not preserve the full diagonal-line rebasing
covariance required by `SymStrat`: after rebasing by a parameter `t`, the
ambient measurement is read at `t`, while the degree-bounded restriction has
discarded all values except the one at `zeroCoord`.  Consequently the ordinary
slice realization cannot be obtained by reusing `xRestrictedStrategy` unchanged.

## Pull-request history diagnosis

The recent pull-request history separates genuine proof progress from interface
realignment.  The Naimark branch is proof progress: it proves the tensor-product
correlation theorem from the one-measurement dilation, and the corresponding
source node may be treated as proved.  By contrast, the Section 6 branches that
introduce named records, successor-stage data, or obligation statements do not
by themselves prove the paper's induction theorem.  They are acceptable only as
local coordinates for the remaining argument, and their green status must not be
read as discharging `thm:main-induction`.

The remaining mathematical theorem is therefore not another record-valued
interface.  At the time of the diagnosis, one had to prove an answer-valued
recursive induction theorem whose successor case applies the predecessor
hypothesis to the restricted answer-valued slices and then carries the
resulting slice measurements through the Section 6 self-improvement and pasting
estimates.  That construction is now checked by the `answerMainInduction`
route.  The lesson remains: a PR that merely packages recursive conclusions as
fields or assumptions is not a proof of the induction step.  The current
proof-bearing targets are the source-boundary range
`md <= k < 400md` and the final printed theorem wrapper.

Update on 2026-05-22: the small-error scalar part of the answer-valued route
has been advanced.  The lemmas
`answer_eps_nonneg_of_isGood`, `answer_delta_nonneg_of_isGood`,
`answer_gamma_nonneg_of_isGood`, and
`answer_diagonalFailureProbability_nonneg` prove the corresponding facts
directly from the answer-valued test definitions.  The subsequent lemmas
`answer_eps_le_one_of_mainInductionError_lt_one`,
`answer_delta_le_one_of_mainInductionError_lt_one`,
`answer_gamma_le_one_of_mainInductionError_lt_one`,
`answer_dq_le_q_of_mainInductionError_lt_one`,
`answer_three_le_k_sq_mul_next_m_of_hsmall`,
`answer_selfImprovementInInductionError_le_mainInductionNu`, and
`answer_selfImprovementInInductionError_le_one_of_mainInductionError_lt_one`
port the ordinary small-error scalar side conditions to an ambient
`AnswerSymStrat`.  The subsequent theorem
`answerLdPastingInInductionError_le_mainInductionError_of_smallError` proves
the scalar absorption for the answer-valued pasting route from these numerical
facts and the averaged `κ` and `ζ` bounds.  These are not source theorem
hypotheses and, by themselves, did not close the successor branch.  They
remove the scalar obstruction to the answer-valued successor route.  The
degree-zero
answer-valued pasting branch is also now proved by an axis/self-consistency
variant of the degree-zero pasting construction.  A later update below records
the proof of the answer-valued Section 11 commutativity input for the
point-equivalent carrier.

## Statement integrity audit

Paper assumptions for `thm:main-induction`: an `(eps, delta, gamma)`-good
symmetric strategy for the `(m,q,d)` low individual degree test and an integer
`k >= md`.

Lean assumptions in `MainInductionStep.mainInduction`: a symmetric strategy
`strategy : SymStrat params ι`, the good-strategy hypothesis
`strategy.IsGood eps delta gamma`, and the corrected large-`k` bound
`400 * params.m * params.d <= k`.

Paper conclusion: a measurement in `PolyMeas(m,q,d)` whose evaluations are
consistent with the point measurement at the main-induction error.

Lean conclusion in `MainInductionStep.mainInduction`: an existential measurement
`Measurement (Polynomial params) ι` satisfying `ConsRel` against
`polynomialEvaluationFamily params` at `mainInductionError params k eps delta
gamma`.

Verdict for the theorem boundary: the blueprint now records the documented
statement correction `k >= 400md`, and `MainInductionStep.mainInduction` proves
the corrected source-facing theorem.  The former source-range obligation is no
longer part of the active route.

Paper assumptions for the native successor step: in the non-base induction
step, an `(eps, delta, gamma)`-good symmetric strategy for dimension `m + 1`,
together with the integer `k` used in the induction theorem.

Lean assumptions in `mainInductionSuccessorNext`: a good symmetric strategy
`strategy : SymStrat params.next ι`, the error parameters, and
`400 * params.next.m * params.next.d <= k`.  The named small-error theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction` has the same successor
hypotheses, together with the branch condition
`mainInductionError params.next k eps delta gamma < 1`; its proof now calls the
internal theorem `answerMainInduction`.  The former direct Section 6 proof hole
below `answerLdPastingInInductionSectionOfSmallError` has been discharged:
`answerComMainForCarrier_ofAnswerGood` proves the answer-valued Section 11
commutativity input for the carrier from answer-valued point commutativity.  The
degree-zero branch
`answerLdPastingInInductionSectionDegreeZeroOfSmallError` is now proved by the
axis/self degree-zero construction.  The scalar estimate
`answerLdPastingInInductionError_le_mainInductionError_of_smallError` is now
proved from the answer-valued small-error scalar lemmas and the averaged
`κ` and `ζ` bounds.

Paper conclusion for the successor step: a measurement in
`PolyMeas(m + 1,q,d)` whose evaluations are consistent with the point
measurement at the main-induction error.

Lean conclusion for the successor step: an existential measurement
`Measurement (Polynomial params.next) ι` satisfying `ConsRel` against
`polynomialEvaluationFamily params.next` at
`mainInductionError params.next k eps delta gamma`.

Verdict for the successor step: source-faithful modulo the documented
large-`k` correction and the explicit small-error branch split.  The remaining
unproved source-range obligation is the interval `md ≤ k < 400md`, not an
additional hypothesis on the paper theorem or on the current Lean interface.

Further update on 2026-05-22: the Section 12 `H-B`/`H-A` transport has been
split at its actual mathematical inputs.  The checked theorems
`hAConsistency_submeas_from_lineConsistency_of_axis_self`,
`hAConsistency_submeas_ofLinePointBounds_of_axis_self`,
`hAConsistency_submeas_ofGHatFacts_of_axis_self`, and
`hAConsistency_submeas_ofComMain_of_axis_self` show that the passage from
vertical-line consistency and one-point sandwich estimates to the final
point-consistency estimate uses only the axis-parallel and self-consistency
bounds of the ambient strategy.  The diagonal-line estimate enters only through
the upstream Section 11 commutativity conclusion.  The auxiliary theorem
`gHatFacts_ofComMainAndSelfConsistency` makes the same separation for
`cor:G-hat-facts`: after `thm:com-main` and slice self-consistency are known,
the `G-hat` estimates do not require a separate good-strategy package.  This
separated the answer-valued pasting obstruction to the answer-valued analogue
of the Section 11 commutativity input, rather than the ordinary carrier's dummy
diagonal measurement; the later update below records that this input has now
been proved.

Later on 2026-05-22 the same separation was propagated through the remaining
mass-comparison part of Section 12.  The checked theorems
`overAllOutcomes_ofComMain_of_axis_self`, `fromHToG_ofComMain`, and
`ldPastingNCompleteness_ofComMain_of_axis_self` show that the
`over-all-outcomes`, `from-H-to-G`, and `N`-completeness stages can be assembled
from an explicit Section 11 commutativity conclusion for the point-equivalent
carrier.  The theorem
`answerLdPastingInInductionSectionOfComMainAndErrorBound` then proves the
answer-valued final pasting assembly once the answer-valued commutativity
conclusion for the carrier is available; the scalar inequality absorbing the
resulting `ldPastingInInductionError` into `mainInductionError` is now proved.
The broad theorem
`answerLdPastingInInductionSectionOfSmallError` has consequently been changed
from a direct proof hole into a checked wrapper whose Section 11 input, scalar
absorption, and answer-valued degree-zero construction are all proved.  The
answer-valued commutativity proof proceeds through
`CommutativityPoints.answerCommutativityPoints` and
`Commutativity.comMain_of_commutativityPoints`, so it uses the answer-valued
diagonal verifier relation rather than the ordinary carrier's dummy diagonal
measurement.
