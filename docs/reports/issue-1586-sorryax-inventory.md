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

currently reports three direct proof holes.

| Site | Declaration | Tracking issue | Mathematical obligation |
|---|---|---|---|
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:680` | `MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction` | #1507, under #1458 | Prove the nontrivial small-error successor construction for the corrected large-`k` interface to `thm:main-induction`, deriving the restricted probability estimates, recursive slice measurements, self-improvement outputs, averaged pasting data, and scalar side conditions internally. |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SourceTheorems.lean:56` | `MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` | #906, under #1458 | Prove the positive-degree non-base small-error branch of the source interval `md ≤ k < 400md` for `thm:main-induction`, after the derived side condition `1 ≤ k` has been supplied by the wrapper.  The large-error branch is closed by `mainInductionOfOneLeError`, the base case is closed by `mainInductionBaseCase`, the degree-zero branch is contradictory, and the checked large-`k` range `400md ≤ k` is handled by `MainInductionStep.mainInduction`. |
| `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:153` | `Test.mainFormal_sourceSmallErrorObligation` | #906, #930, #1507, under #1458 | Derive the non-vacuous branch of the printed two-space source theorem `thm:main-formal`, with a general projective strategy, the paper hypothesis `k ≥ md`, and `mainFormalError params k eps < 1`.  The wrapper `Test.mainFormal_sourceObligation` now proves the saturated-error branch by `Test.mainFormal_source_trivial_witness`, so only this small-error source-boundary branch remains as a direct final-theorem proof hole. |

The source-range obligation and the final small-error source obligation were introduced
deliberately in paper-realignment mode: they make the printed paper statements
visible in Lean and linked from the source blueprint entries, without certifying
their proofs.  They do not add bridge, residual, repair, package, producer, or
generic hypothesis fields to the source theorems.
Each direct proof-hole declaration now carries an explicit `**Unfaithful:**`
docstring marker identifying the unfinished proof step, its paper source, its
tracking note or issue, and the construction expected to eliminate the
`sorryAx` dependency.

The successor theorem is intentionally stated without restricted-probability,
recursive-slice, self-improvement, pasting, residual, repair, or generic
obligation hypotheses.  The public successor wrapper
`mainInductionSuccessorNext` now splits the large-error case and calls the named
small-error construction above in the nontrivial branch; this named construction
is the source of the current `sorryAx` frontier.

The existing formal assembly has already localized the missing input.  In the
small-error branch, `mainInductionFromAnswerStageDataOfSmallError` proves the
successor conclusion from answer-valued restriction data, answer-valued
per-slice induction data, and answer-valued self-improvement data.  The
answer-valued restricted-probabilities theorem supplies the first of these from
`strategy.IsGood eps delta gamma`.  The absent construction is the predecessor
induction conclusion for the restricted answer-valued slices, corresponding to
`references/ldt-paper/inductive_step.tex:441-454`.  It must enter through the
eventual recursive proof of the corrected large-`k` interface to
`thm:main-induction`, not as an additional theorem hypothesis.

The internal theorem
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligations` records
this reduction in Lean: from the predecessor answer-valued induction hypothesis,
positive degree, the predecessor large-`k` side condition, and the concrete
answer-valued slice-transport data, it derives the nontrivial successor
conclusion using the existing small-error assembly.  The checked strengthening
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`
derives the predecessor `k`-side conditions from the successor large-`k`
hypothesis and `d > 0`.  The checked split theorem
`MainInductionStep.mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
then combines this small-error reduction with the already proved large-error
branch.  The further checked theorem
`MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitObligations`
separates the small-error branch into the positive-degree answer-valued route
and a distinct degree-zero successor construction.  Thus `0 < d` is not being
added to the source theorem; the degree-zero branch is now a named internal
obligation.  The checked helper
`MainInductionStep.mainInductionSuccessorNext_degreeZero_ofPastingFamily` shows
that this degree-zero obligation can use the already completed degree-zero
pasting construction once the proof supplies a complete, point-consistent slice
family and the scalar comparison with `mainInductionError`.  The checked
composition theorem
`MainInductionStep.mainInductionSuccessorNext_ofDegreeSplitPastingObligations`
plugs this family-and-scalar route into the degree split, so the remaining
degree-zero frontier is no longer an abstract successor assumption.
`AxiomAudit.lean` checks the six completed helpers as standard-axiom
declarations and checks the named small-error construction and its public
successor wrappers as exactly the expected `sorryAx` frontier.  It also checks
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
hide an additional proof frontier: only
`MainFormalRoleInductionWitness.ofMainInduction` inherits the remaining
`sorryAx`, and it does so exactly through `MainInductionStep.mainInduction`.
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
the remaining positive-degree obstruction is the construction of the required
ordinary covariant slice strategies or an answer-valued self-improvement
theorem, not an unfinished proof inside the existing transport declarations.
The Chapter 2 strategy interfaces linked from the blueprint are also checked:
the role type and involution, the two-space and same-space projective strategy
containers, their low-individual-degree failure probabilities and passing
predicates, the same-space forgetful map, the symmetric strategy container and
goodness predicate, the direct-sum role-register block lemmas, the
last-direction notation, the restricted diagonal sample space, and the
restricted diagonal failure probability do not import `sorryAx`.

The slice-transport datum has a precise formal meaning.  It asks for ordinary
`SymStrat` slice strategies on which the existing Section 9 theorem
`selfImprovementInInductionSection` can be applied, together with proofs that
their verifier-visible measurements agree with the answer-valued restricted
strategy `xRestrictedAnswerSymStrat`.  Since `xRestrictedAnswerSymStrat` is an
`AnswerSymStrat`, not a `SymStrat`, this is not a definitional coercion.  The
remaining construction must either build the corresponding ordinary covariant
slice strategies or provide the self-improvement theorem directly in the
answer-valued interface.

The legacy restricted strategy `xRestrictedStrategy` is insufficient for this
purpose as it stands.  It deliberately keeps only the `zeroCoord` value of the
restricted diagonal-line answer and re-embeds that value as a constant slice
polynomial.  This is enough for the diagonal failure probability, and it is why
the answer-valued and legacy restricted-probability statements agree, but it
does not give the transport-covariant diagonal measurement required by an
ordinary `SymStrat`.

## Blueprint Proof-Level Status

The blueprint synchronization report records four proof-level gaps.  Two are
the source-labelled statements whose remaining proof debt is factored through
named obligations above, and two are the current corrected Lean interfaces
which still inherit the Section 6 successor frontier.

| Blueprint node | Lean declaration | Status |
|---|---|---|
| `thm:main-induction` | `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` | Statement-level `\leanok` only.  This is the printed paper statement with `k ≥ md`; the corrected large-`k` subrange is reduced to the current interface, while the source interval `md ≤ k < 400md` is isolated as `mainInduction_sourceRangeObligation`.  That wrapper proves its large-error branch and calls `mainInduction_sourceRangeSmallErrorObligation` only in the small-error branch; the small-error wrapper proves the base case, the non-base wrapper removes the impossible degree-zero branch, and the positive-degree wrapper derives `1 ≤ k`, leaving `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` as the direct source-range proof hole. |
| `thm:main-induction-current-interface` | `MIPStarRE.LDT.MainInductionStep.mainInduction` | Statement-level `\leanok` only.  The proof block deliberately has no proof-level `\leanok` while the successor construction above is unfinished. |
| `thm:main-formal` | `MIPStarRE.LDT.Test.mainFormal_sourceStatement` | Statement-level `\leanok` only.  This is the printed two-space paper statement with `k ≥ md`; the wrapper `mainFormal_sourceObligation` proves the saturated-error branch and leaves the non-vacuous branch as `mainFormal_sourceSmallErrorObligation`. |
| `thm:main-formal-current-interface` | `MIPStarRE.LDT.Test.mainFormal` | Statement-level `\leanok` only.  This current same-space interface inherits the Section 6 successor frontier through `mainInduction`, so no proof-level completion is claimed. |

The source-labelled theorems `thm:main-induction` and `thm:main-formal` are no
longer linked to the restricted Lean declarations.  They now link to
source-faithful Lean statements whose remaining proof debt is tracked directly
or through named source-range obligations, and are intentionally left without
proof-level formalization marks until the corrected interfaces are derived from
the source statements.

## Explicit Axiom Declarations

The dedicated audit

```bash
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
```

reports:

```text
Explicit Lean axiom declaration audit
scanned files: 423
findings: 0
```

Thus the current LDT tree contains no explicit Lean axiom declarations.  The
only proof-integrity markers in the kernel are the `sorryAx` dependencies
generated by the three direct proof holes above: the source-range obligation,
the final small-error source-boundary obligation, and the Section 6 successor
construction.

## Transitive `sorryAx` Frontier

The file `MIPStarRE/LDT/Test/AxiomAudit.lean` records the expected transitive
axiom closure for public declarations.  After the current repairs, the only
audited public declarations expected to depend on `sorryAx` are:

| Declaration | Reason |
|---|---|
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` | This is the direct proof obligation for the positive-degree non-base small-error branch of the source interval `md ≤ k < 400md` in `thm:main-induction`, with the derived side condition `1 ≤ k`. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation` | This is the named wrapper for the positive-degree non-base small-error source interval; it derives `1 ≤ k` from `md ≤ k`, `m > 0`, and `0 < d`, then calls `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorNonBaseObligation` | This is the named wrapper for the non-base small-error source interval; it proves the degree-zero branch by contradiction and calls `mainInduction_sourceRangeSmallErrorPositiveNonBaseObligation` only in the positive-degree branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorObligation` | This is the named wrapper for the small-error source interval; it proves the base case by `mainInductionBaseCase` and calls `mainInduction_sourceRangeSmallErrorNonBaseObligation` only in the non-base branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation` | This is the named wrapper for the source interval `md ≤ k < 400md`; it proves the large-error branch by `mainInductionOfOneLeError` and calls `mainInduction_sourceRangeSmallErrorObligation` only in the remaining small-error branch. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` | This is the printed source statement of `thm:main-induction`.  In the already covered range `400md ≤ k`, it calls the corrected large-`k` interface and hence inherits the Section 6 successor-construction frontier from that interface; in the remaining range it calls `mainInduction_sourceRangeObligation`. |
| `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` | This is the direct proof obligation for the non-vacuous branch of the printed two-space source statement of `thm:main-formal`, covering the documented interface, scalar-boundary, and Section 6 successor issues. |
| `MIPStarRE.LDT.Test.mainFormal_sourceObligation` | This is the named wrapper for the printed two-space source statement of `thm:main-formal`; it proves the saturated-error branch by `mainFormal_source_trivial_witness` and calls `mainFormal_sourceSmallErrorObligation` only in the remaining small-error branch. |
| `MIPStarRE.LDT.Test.mainFormal_sourceStatement` | This is the printed two-space source statement of `thm:main-formal`; it calls `mainFormal_sourceObligation` rather than adding the missing source-boundary work as theorem hypotheses. |
| `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction` | This is the direct small-error successor construction obligation. |
| `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext` | Its small-error branch calls `mainInductionSuccessorNext_ofSmallErrorConstruction`; its large-error branch is proved. |
| `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessor` | It decomposes a non-base parameter bundle and calls `mainInductionSuccessorNext`. |
| `MIPStarRE.LDT.MainInductionStep.mainInduction` | This is the corrected large-`k` Lean interface to `thm:main-induction`; its non-base branch calls `mainInductionSuccessor`, which calls the native successor theorem `mainInductionSuccessorNext`. |
| `MIPStarRE.LDT.Test.strategySymmetrization_mainInduction` | It is the Section 3 symmetrization handoff and calls `MainInductionStep.mainInduction`. |
| `MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofMainInduction` | It packages the Section 6 output as the role-register witness used by `mainFormal`. |
| `MIPStarRE.LDT.Test.mainFormal` | The current same-space, corrected large-`k` interface calls `MainInductionStep.mainInduction` through the role-register route; hence it inherits the Section 6 successor proof hole. |
| `MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofSameSpaceLargeK` | This proved subcase embeds the current same-space, corrected large-`k` interface into the source-shaped two-space conclusion after forgetting `SameSpaceProjStrat` to `ProjStrat`; hence it has exactly the same transitive Section 6 successor dependency as `mainFormal`. |

The Lean docstrings for this transitive route now carry explicit
`**Unfaithful:**` markers at the theorem boundary where the unfinished proof is
used: the small-error successor construction, the native successor wrapper, the
parameter-decomposition successor theorem, the corrected large-`k` main
induction interface, the source-range obligation, the source main-induction
statement, the Section 3 symmetrization handoff, the role-register witness
constructor, the current same-space final theorem interface, the checked
same-space source-conclusion subcase, and the two source-final-theorem
declarations.  These markers classify the proof status; they do not change any
public statement or add hypotheses.

The following previously listed proof holes have been discharged and are now
checked as standard-axiom declarations in `AxiomAudit.lean`: the
induction-section self-improvement theorem, the orthonormalization theorem and
main lemma, unrestricted low-degree pasting including its degree-zero branch,
the self-improvement theorem and helper theorem, the SDP slackness statement,
global variance, and the ordered Laplacian spectral-gap theorem.
The same audit also checks that the internal Section 6 assembly theorems
`mainInductionFromStageData` and
`mainInductionFromAnswerStageDataOfSmallError` do not import `sorryAx`.
It also checks the foundational Chapter 2 strategy interfaces used to state the
current final theorem, so the remaining transitive frontier cannot be hidden in
the strategy definitions, failure probabilities, or last-direction notation.

## Repair Direction

The active repair direction is to prove
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`.  This
should construct the
successor-stage objects used by the paper,
\[
  \text{restrict} \longrightarrow \text{induct}
  \longrightarrow \text{self-improve} \longrightarrow \text{paste},
\]
from the corrected theorem hypotheses together with the recursive predecessor
argument and answer-valued slice-transport construction internal to the
small-error, positive-degree branch of the corrected large-`k` proof of
`thm:main-induction`.  The
large-error branch and the elementary predecessor `k`-side conditions are
already discharged by checked internal lemmas.  The proof must not move any of
these objects into the public hypotheses of `mainInduction` or `mainFormal`.

Once this proof is complete, `MainInductionStep.mainInduction` and the current
`Test.mainFormal` interface should both lose their `sorryAx` dependency.  The
full printed `thm:main-formal` will still require the separately documented
two-space role-register wrapper.
