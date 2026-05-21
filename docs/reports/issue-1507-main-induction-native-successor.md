# Issue #1507 main-induction native successor obligation

Audit date: 2026-05-18.

Last status update: 2026-05-21.  The classifications below incorporate the
current split between the printed source theorem `thm:main-induction` and the
separate corrected large-`k` Lean interface
`thm:main-induction-current-interface`, together with the axiom-audit evidence
recorded in `MIPStarRE/LDT/Test/AxiomAudit.lean`.

## Scope

This note records the repair batch for the main-induction proof frontier.  The
source-labelled blueprint node `thm:main-induction` is the printed theorem with
the paper hypothesis `k >= md`; the current Lean declaration is now linked from
the separate corrected large-`k` interface
`thm:main-induction-current-interface`.  The public graph on the GitHub Pages
branch predates this split and marks `thm:main-induction` blue, while
`lem:main-induction-base` and `def:successor-pasting-data` are green.  Thus the
remaining mathematical obstruction is the successor branch of the corrected
formal interface, not the base case or the already formalized pasting data.

## Source comparison

The source theorem is `references/ldt-paper/inductive_step.tex:7-18`, with the
successor proof at `references/ldt-paper/inductive_step.tex:441-551`.  The proof
is naturally a step from dimension `m` to dimension `m + 1`: for a good
symmetric strategy in dimension `m + 1`, one restricts to each height
`x \in F_q`, applies the induction hypothesis in dimension `m`, self-improves
the slice measurements, averages the resulting estimates, and invokes the
induction-section pasting theorem.

The blueprint source theorem in `blueprint/src/chapter/ch10_induction.tex` keeps
the printed hypothesis `k >= md` and now links to the source-faithful Lean
statement `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`,
which sends the remaining source range `md <= k < 400md` to the named
obligation `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation`;
in the covered range `400md <= k`, it calls the corrected large-`k` interface.
The separate current-interface theorem uses the corrected large-`k` hypothesis
`k >= 400md`, following
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and links the Lean
declaration `MIPStarRE.LDT.MainInductionStep.mainInduction`.  No proof-level
`\leanok` is claimed for the successor proof.

## Classification

`thm:main-induction`: source theorem.

Classification: source statement, linked to
`MainInductionStep.mainInduction_sourceStatement`.  The printed hypothesis is
`k >= md`; the present Lean source statement proves the subrange
`400md <= k` by calling the corrected interface and leaves the interval
`md <= k < 400md` as the named obligation
`mainInduction_sourceRangeObligation`.

`thm:main-induction-current-interface`: corrected Lean interface.

Classification: stated with proof hole.  The Lean theorem has the source-shaped
conclusion and corrected large-`k` hypotheses; the successor branch remains
unfinished.

`mainInductionSuccessorNext`: Lean successor obligation.

Classification: stated with proof hole.  This is the native `m -> m + 1`
successor statement.  It carries no restricted-probability, recursive-slice,
self-improvement, or pasting data as hypotheses.

`MainInductionSuccessorSmallErrorConstructionStatement`: internal construction
statement.

Classification: Lean-only proof obligation.  This proposition names the three
remaining ingredients for the small-error successor proof: the predecessor
answer-valued induction hypothesis, the degree-zero family-and-scalar
construction, and the positive-degree answer-valued slice transport.  It is not
linked as a paper theorem and is not a permissible additional hypothesis of the
source theorem.

`mainInductionSuccessorNext_ofSmallErrorConstruction_ofConstructionStatement`:
checked conditional reduction.

Classification: internal assembly theorem.  It proves the small-error successor
conclusion from
`MainInductionSuccessorSmallErrorConstructionStatement` by calling the checked
degree-split and internal-constructions reductions.  Its conditional hypothesis
is an internal proof obligation, not a hypothesis of `thm:main-induction`.

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
self-improvement data are constructed, it passes through the ordinary assembly
and proves the successor conclusion.  Neither theorem is advertised as
`thm:main-induction`, and neither supplies an extra hypothesis to the source
statement.  The file `MIPStarRE/LDT/Test/AxiomAudit.lean` checks both assembly
theorems as free of `sorryAx`, so they are not part of the remaining proof
frontier.

## Repair

The direct `sorry` has been moved from the arbitrary non-base presentation to the
named small-error construction
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  The native successor
theorem `mainInductionSuccessorNext` now only splits the already proved
large-error branch from this nontrivial construction.  The public branch theorem
`mainInductionSuccessor` still only performs the predecessor decomposition for
`params.m != 1`; the missing mathematics is exactly the nontrivial source proof
step from `m` to `m + 1`.

The next proof work is now more sharply localized.  The theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction` is the current direct
proof obligation.  In that nontrivial small-error branch,
`mainInductionFromAnswerStageDataOfSmallError` already
turns answer-valued restriction data, answer-valued per-slice induction data,
and answer-valued self-improvement data into the desired successor conclusion.
The answer-valued restricted-probabilities theorem supplies the restriction
data from `strategy.IsGood eps delta gamma`.  The internal theorem
`mainInductionSuccessorNext_ofAnswerStageObligations` records the next reduction:
given the predecessor answer-valued induction hypothesis, the positive-degree
side condition, the predecessor large-`k` side condition, and concrete
answer-valued slice-transport data, it proves the nontrivial successor
conclusion.

The checked theorem
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`
removes the elementary size bookkeeping from this frontier.  From the
successor hypothesis `400(m+1)d <= k` and `d > 0`, Lean derives both
`k >= 1` and the predecessor hypothesis `400md <= k`, then calls the
answer-valued successor assembly above.  Thus the remaining open inputs are not
the large-`k` side conditions; they are the predecessor induction hypothesis and
the answer-valued slice-transport construction.

The checked theorem
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
also removes the large-error case from the successor frontier.  It performs the
same positive-degree small-error reduction when
`mainInductionError params.next k eps delta gamma < 1`, and otherwise applies
the trivial-measurement theorem `mainInductionOfOneLeError`.  Consequently the
large-error case is no longer part of the remaining construction.
The axiom audit also checks the linked base-case theorem, large-error theorem,
restricted-probability estimates, predecessor-hypothesis predicates,
answer/legacy conversion constructors, and averaged-pasting invocation as
free of `sorryAx`.  Thus the remaining proof debt is not in those bookkeeping
or reduction declarations.

The checked theorem
`mainInductionSuccessorNext_ofDegreeSplitObligations` also separates the
small-error degree-zero branch from the positive-degree route.  In positive
degree it calls the answer-valued successor assembly above; when `d = 0`, it
waits for a separate degree-zero successor construction.  This is the correct
source-facing status: the theorem statement has not acquired a positivity
hypothesis, and the degree-zero branch is now named as its own internal proof
obligation.

The checked helper
`mainInductionSuccessorNext_degreeZero_ofPastingFamily` connects this
degree-zero obligation to the existing degree-zero pasting theorem.  It says
that a successor measurement follows from `degreeZeroPastedPointConsistency`
once the proof has constructed a slice family which is complete and
point-consistent with parameters `kappa` and `zeta`, and has proved that the
resulting degree-zero pasting error is at most the main-induction error.  Thus
the degree-zero branch is not blocked on interpolation itself; it is blocked on
the construction of the appropriate slice family and the corresponding scalar
absorption.

The checked composition theorem
`mainInductionSuccessorNext_ofDegreeSplitPastingObligations` plugs this
degree-zero pasting-family route into the degree split.  Thus the remaining
degree-zero input is no longer an abstract proof of the successor conclusion:
it is the construction of the complete point-consistent slice family, together
with the scalar absorption inequality which places the degree-zero pasting
error below `mainInductionError`.

The checked small-error theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions`
then closes the small-error successor conclusion from exactly these internal
constructions and the predecessor answer-valued induction hypothesis.  It is
not a source theorem and is not linked as the proof of
`thm:main-induction`; it records where the eventual induction proof will use
its local hypothesis for dimension `m`.

The Lean-only proposition
`MainInductionSuccessorSmallErrorConstructionStatement` now packages these
three remaining mathematical ingredients as a single statement, and the proved
conditional theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofConstructionStatement`
closes the small-error successor conclusion from that statement.  This is a
sharpening of the proof frontier, not a weakening of the public theorem:
`mainInductionSuccessorNext_ofSmallErrorConstruction` retains its source-shaped
successor hypotheses and its tracked proof hole, while the new checked theorem
records exactly what must be constructed internally before the existing
degree-split assembly applies.

The remaining missing data are therefore the recursive predecessor argument and
the small-error successor constructions from
`references/ldt-paper/inductive_step.tex:441-551`: a degree-zero branch, and in
positive degree the slice-transport construction for the restricted
answer-valued strategies.  These data should be supplied internally by the
final proof of `thm:main-induction`; they should not be promoted to public
hypotheses of `mainInduction`, `mainInductionSuccessorNext`, or `mainFormal`.

The paper-to-Lean correspondence is now as follows.  Lines
`441-454` of `references/ldt-paper/inductive_step.tex` are the recursive
predecessor call, represented in Lean by `AnswerPerSliceInductionData` and the
local induction hypothesis expected by
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  Lines `456-485` are the
slice-wise self-improvement step, represented by `AnswerSelfImprovementData`;
the open point is that the paper's restricted slice is currently modeled as an
`AnswerSymStrat`, while `selfImprovementInInductionSection` is an ordinary
`SymStrat` theorem.  Lines `487-550` are the averaging of the slice-wise
properties, already consumed by
`mainInductionFromAnswerStageDataOfSmallError` after the answer-valued
restriction, induction, and self-improvement data are supplied.  Lines
`552-623` are the final pasting invocation and scalar absorption; the ordinary
positive-degree route is checked by the stage assembly, while the separate
degree-zero route has been reduced to constructing a complete point-consistent
slice family and the corresponding scalar inequality.

The recursive predecessor argument has a different logical status from the
degree-zero and slice-transport constructions.  It is not a new mathematical
hypothesis about the given successor strategy.  It is the induction hypothesis
for dimension `m`, applied to the restricted strategies at heights
`x \in F_q`.  A final repair should therefore either prove `mainInduction` by
an explicit induction on the dimension and pass this predecessor conclusion
locally to the checked successor assembly, or introduce a named internal
successor lemma whose induction-hypothesis parameter is consumed only inside
that recursive proof.  Such a parameter must not be displayed as an assumption
of the source theorem, the corrected large-`k` current interface, or the final
formal soundness theorem.

The slice-transport obstruction is not merely notational.  The restricted slice
used for the recursive call is currently represented by
`xRestrictedAnswerSymStrat`, an `AnswerSymStrat` whose diagonal-line answers are
full functions, matching the paper's restriction more literally.  The available
Section 9 theorem `selfImprovementInInductionSection`, however, is stated for an
ordinary `SymStrat`, whose diagonal-line answers are
`DiagonalLinePolynomial`s with the covariant measurement interface.  Thus the
missing construction is one of the following equivalent mathematical bridges:
construct an ordinary covariant slice strategy whose verifier-visible point,
axis-parallel, and diagonal zero-coordinate tests agree with
`xRestrictedAnswerSymStrat`, or prove the induction-section self-improvement
theorem directly for `AnswerSymStrat`.  This is an internal construction
obligation, not an admissible extra hypothesis on the public theorem.

The legacy restricted object `xRestrictedStrategy` does not discharge this
obligation as it stands.  It is a `RestrictedSymStrat`, not a `SymStrat`, and
its diagonal measurement keeps only the sampled base-point value before
re-embedding it into the degree-bounded slice-polynomial alphabet.  Therefore it
supplies the diagonal failure-probability comparison used in
`lem:restricted-probabilities`, but it does not supply the transport-covariant
ordinary diagonal measurement needed as input to the Section 9 theorem.
The existing ordinary and answer-valued slice-transport constructors are
checked not to import `sorryAx`; once concrete ordinary slice strategies and
their verifier-visible measurement equalities are available, they apply the
Section 9 theorem slice by slice and assemble the required self-improvement
data.  The missing assertion is the construction of those strategies, or else
an answer-valued version of the self-improvement theorem.

The second route is a genuine generalization of the Section 9 interface, not a
local change to the induction assembly.  The current self-improvement
definitions use the ordinary `SymStrat` point-conditioned operator
`pointConditionedOutcomeOperatorAtPolynomial`, the averaged SDP operator
`averagedPointOperator`, and the local-variance expressions built from them.
An answer-valued self-improvement theorem would therefore either refactor these
operators through the common point-measurement and state data, or reprove the
same analytic chain for `AnswerSymStrat`.  This confirms that the remaining
gap is the mathematical interface between the paper-faithful restricted
strategy and the existing Section 9 theorem, rather than a missing simplifier or
rename in the successor assembly.

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

Verdict for the theorem boundary: the printed source theorem
`thm:main-induction` remains exact in the blueprint and is now linked to the
source-faithful Lean statement
`MainInductionStep.mainInduction_sourceStatement`, which factors the interval
`md <= k < 400md` through the named obligation
`mainInduction_sourceRangeObligation`.  The current Lean theorem
`MainInductionStep.mainInduction` is a separate corrected large-`k` interface;
it supplies the covered range `400md <= k` but not the full printed range
`k >= md`.

Paper assumptions for the native successor step: in the non-base induction
step, an `(eps, delta, gamma)`-good symmetric strategy for dimension `m + 1`,
together with the integer `k` used in the induction theorem.

Lean assumptions in `mainInductionSuccessorNext`: a good symmetric strategy
`strategy : SymStrat params.next ι`, the error parameters, and
`400 * params.next.m * params.next.d <= k`.  The named remaining theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction` has the same successor
hypotheses, together with the branch condition
`mainInductionError params.next k eps delta gamma < 1`.

Paper conclusion for the successor step: a measurement in
`PolyMeas(m + 1,q,d)` whose evaluations are consistent with the point
measurement at the main-induction error.

Lean conclusion for the successor step: an existential measurement
`Measurement (Polynomial params.next) ι` satisfying `ConsRel` against
`polynomialEvaluationFamily params.next` at
`mainInductionError params.next k eps delta gamma`.

Verdict for the successor step: source-faithful modulo the documented
large-`k` correction and the explicit small-error branch split.  The remaining
proof hole is a named source-faithful proof obligation, not an additional
hypothesis on the paper theorem or on the current Lean interface.
