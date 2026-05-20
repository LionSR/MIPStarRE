import MIPStarRE.LDT.Test.MainTheorem.NativeTargets
import MIPStarRE.LDT.Test.StrategyBiProj

/-!
# Main-formal soundness theorem

Base handoff, final projective-completion transport, and the current same-space
formal interface toward `thm:main-formal` (`\Cref{thm:main-formal}`).  This
module contains:

* `mainFormalBaseRoleInductionWitness` — names the Section 6 role-register witness
  used by the base case `m = 1`.

* `mainFormal_ofProjectiveCompletionTransportWitness` — derives the three consistency
  conclusions of `thm:main-formal` from a constructed Section 6
  projective-completion witness.

* `mainFormal_sourceObligation` and `mainFormal_sourceStatement` — record the
  printed two-space source theorem, prove its saturated-error branch, and name
  the remaining small-error source-boundary obligation.

* `mainFormal_sourceConclusion_ofSameSpaceLargeK` — proves the source-shaped
  conclusion in the same-space corrected-range subcase by calling the current
  `mainFormal` interface.

* `mainFormal` — the current same-space formal interface toward the final
  theorem, taking a same-space projective strategy that passes the LID test with
  probability `≥ 1 − ε`, together with the explicit boundary conditions `0 < k`
  and `400md ≤ k`, and producing the three pointwise consistency targets at
  error bound `mainFormalError`.  The remaining same-space interface restriction
  is documented in
  `docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
  large-`k` and `k > 0` scalar-cascade boundary is documented in
  `docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  Its proof now follows
  the checked branch structure: the vacuous branch is closed by
  `mainFormal_trivial_witness`, the non-vacuous branch invokes the Section 6
  role-register witness, the post-role projective-completion construction
  target, and the final transport.  The remaining proof gap is the transitive
  Section 6 small-error successor construction, not an additional hypothesis of
  `mainFormal`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `\Cref{thm:main-formal}` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal-current-interface}`; and
  `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-step6-obligations}`,
  `\label{lem:main-formal-successor-handoff}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Base handoff and final projective-completion transport

The base branch of `mainFormal` needs a concrete Section 6 role witness and one
post-role projective-completion witness.  Earlier scaffolding expressed this
through separate bridge and obligation packages.  The current interface below
does not keep such packages as hypotheses: the source theorem remains separate in
the blueprint, and the missing source-boundary work is represented by named
obligations. -/

/--
Trivial saturated-error branch for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`; this is the
large-error branch separated by the source-boundary repair documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`.

**Source:** This is a source-faithful saturated-error branch: when the printed
target error is at least `1`, the consistency conclusion follows from the
normalization bound for bipartite consistency defects, without adding any
construction hypothesis to the source theorem.

Whenever `mainFormalError params k eps ≥ 1`, the three consistency conclusions
hold for arbitrary projective polynomial measurements, since each underlying
consistency defect is bounded by `1` for a normalized bipartite state and a
uniform question distribution.  This is the two-space analogue of
`mainFormal_trivial_witness`; it does not use the low individual degree test
hypothesis. -/
theorem mainFormal_source_trivial_witness
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (k : ℕ)
    (herr : 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialA : ProjMeas (Polynomial params) ιA := default
  let trivialB : ProjMeas (Polynomial params) ιB := default
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) herr⟩

/--
Small-error internal proof obligation for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the remaining non-vacuous source-boundary work needed to
derive the paper theorem from the present formal infrastructure.  It is not an
additional hypothesis of `thm:main-formal`; the source-boundary wrapper below
calls this obligation only after the saturated-error branch has been discharged
by `mainFormal_source_trivial_witness`.

**Proof gap:** The current checked route proves the separate same-space,
corrected large-`k` interface `mainFormal`.  To close this small-error
obligation one must derive the final conclusions for a general two-space
projective strategy with only the printed hypothesis `k ≥ m d` and
`mainFormalError params k eps < 1`.  This requires the heterogeneous
role-register symmetrization recorded in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`, the scalar
range and `k > 0` boundary recorded in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and the Section 6 successor
construction tracked by issue #1507 under #1458.

**Unfaithful:** This proof currently contains the tracked `sorry` for deriving
the non-vacuous branch of the printed two-space source theorem from the present
same-space, corrected large-`k` infrastructure.  It therefore uses `sorryAx`
rather than deriving `references/ldt-paper/test_definition.tex:180-202` from
the paper hypotheses.  Documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, issue #1507, and issue
#1458.  Elimination: prove the two-space role-register reduction, the source
`k ≥ m d` boundary, and the Section 6 successor construction. -/
theorem mainFormal_sourceSmallErrorObligation
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (_hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k)
    (_hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  sorry

/--
Internal proof-obligation wrapper for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem removes the saturated-error branch from the source-boundary
frontier.  If `mainFormalError params k eps ≥ 1`, the conclusion follows from
`mainFormal_source_trivial_witness`; otherwise the proof is exactly the named
small-error obligation `mainFormal_sourceSmallErrorObligation`.  The wrapper is
not an additional hypothesis of `thm:main-formal`.

**Unfaithful:** The small-error branch calls the tracked obligation
`mainFormal_sourceSmallErrorObligation`, whose proof is not yet derived from the
source theorem hypotheses.  Documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, issue #1507, and issue
#1458; the source theorem is `references/ldt-paper/test_definition.tex:180-202`.
Elimination: discharge `mainFormal_sourceSmallErrorObligation` while preserving
the printed two-space statement and the paper bound `k ≥ m d`. -/
theorem mainFormal_sourceObligation
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormal_source_trivial_witness params strategy eps k hlarge
  · exact mainFormal_sourceSmallErrorObligation params strategy eps hpass k hk hlarge

/--
Source statement of `thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the printed paper theorem for a general two-space
projective strategy, with the paper's hypothesis `k ≥ m d` and the three final
consistency conclusions at the error `mainFormalError`.

**Proof gap:** The checked route below proves only the separate same-space,
corrected large-`k` interface `mainFormal`.  The same-space restriction is
documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
large-`k` and scalar-cascade boundary is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  The current route also
inherits the Section 6 small-error successor construction gap through
`MainInductionStep.mainInduction`, tracked by issue #1507 under #1458.  The
source theorem is therefore kept as a source-faithful statement and its proof is
factored through the named internal obligation `mainFormal_sourceObligation`,
rather than being replaced by a theorem with additional bridge, residual,
repair, package, producer, or generic hypothesis fields.

**Unfaithful:** The proof currently calls the tracked wrapper
`mainFormal_sourceObligation`; its saturated-error branch is proved, while its
small-error branch calls `mainFormal_sourceSmallErrorObligation`, whose proof is
not yet derived from the source theorem hypotheses.  Documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`,
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, issue #1507, and issue
#1458; the source theorem is `references/ldt-paper/test_definition.tex:180-202`.
Elimination: discharge `mainFormal_sourceSmallErrorObligation` while preserving
the printed two-space statement and the paper bound `k ≥ m d`. -/
theorem mainFormal_sourceStatement
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : ProjMeas (Polynomial params) ιA,
      ∃ G_B : ProjMeas (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  exact mainFormal_sourceObligation params strategy eps hpass k hk


/-- The role-register witness used by the `m = 1` branch of
`mainFormal`.

Supports the base case (`m = 1`) of the main formal theorem
`\label{thm:main-formal}` in `references/ldt-paper/inductive_step.tex`.
The base-case argument uses the witness produced by
`MainFormalRoleInductionWitness.ofBaseCase`; this definition names that choice. -/
noncomputable def mainFormalBaseRoleInductionWitness
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    MainFormalRoleInductionWitness params strategy eps hpass k :=
  Classical.choice (MainFormalRoleInductionWitness.ofBaseCase params strategy eps k hpass hm1)

/-- Derives the three consistency conclusions of `thm:main-formal` from a
constructed Section 6 projective-completion witness.

The witness contains the role-register output and the post-role completion
data.  This theorem performs only the already-formalized final transport and
scalar absorption steps; it does not introduce additional auxiliary
hypotheses. -/
theorem mainFormal_ofProjectiveCompletionTransportWitness
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (projectiveCompletionWitness :
      MainFormalProjectiveCompletionTransportWitness params strategy eps k scalars) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  exact MainFormalProjectiveCompletionTransportWitness.toMainFormal
    projectiveCompletionWitness hpass

/--
`thm:main-formal`, current formal interface.

This is the same-space, corrected large-`k` Lean interface
toward the paper theorem.  The printed theorem in `test_definition.tex` starts
from a general two-space projective strategy and prints the weaker condition
`k ≥ m d`.  The same-space interface restriction is documented in
`docs/paper-gaps/issue-930-main-formal-interface-restrictions.tex`; the
large-`k` and `k > 0` scalar-cascade boundary is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.

The statement does not assume repaired auxiliary data, role-register witness
data, or final projective-completion hypotheses. Those remain open steps to be
derived from the pass condition and the preceding sections.

The hypothesis `hk : 400 * params.m * params.d ≤ k`, together with `hk0`,
records the strengthened boundary from issue #906 and
`rem:main-formal-k-boundary`; the paper states the weaker condition `k ≥ md`.
The positivity of `k` is a scalar-cascade boundary: it supplies the `1 ≤ k`
field of `CascadeHypotheses` in the non-vacuous branch, rather than any
measurement-construction data.
The field model is presently fixed at universe level `0`, matching the current
Section 6 successor theorem rather than an additional mathematical restriction.

**Proof gap:** this current interface has no bridge, residual, repair, or
obligation hypotheses.  In the non-vacuous branch the proof constructs the
scalar cascade and role-register witness from the theorem hypotheses, then
calls `MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness`
and the already proved final transport.  The role-register witness is built
from `MainInductionStep.mainInduction` via
`strategySymmetrization_mainInduction`; the base case is discharged by
`mainInductionBaseCase`.  The Step 6 base-case transport uses the checked
repaired line-169 estimate with its explicit additional loss, so the exact
match-mass branch no longer lies on the active `mainFormal` path.  The only
remaining transitive `sorry` is the native Section 6 small-error successor
construction, isolated in
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction` and
tracked by #1507 (umbrella tracking: #1458).

**Unfaithful:** The proof transitively uses
`MainInductionStep.mainInduction`, whose successor branch still depends on the
tracked construction obligation
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`.  This
is not an additional hypothesis of `mainFormal`, but the proof still imports
`sorryAx` through the Section 6 route.  Documented in issue #1507 under #1458;
the relevant source proof is `references/ldt-paper/inductive_step.tex:26-236`,
using the successor construction at `references/ldt-paper/inductive_step.tex:441-551`.
Elimination: prove the native Section 6 small-error successor construction. -/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  by_cases hlarge : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k hlarge
  · have hepsNN : 0 ≤ eps := SameSpaceProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 hlarge
    rcases MainFormalRoleInductionWitness.ofMainInduction
        params strategy eps k hpass hk with ⟨roleInductionWitness⟩
    rcases
        MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness
          (scalars := scalars) hlarge roleInductionWitness with
      ⟨projectiveCompletionWitness⟩
    exact mainFormal_ofProjectiveCompletionTransportWitness (hpass := hpass)
      projectiveCompletionWitness

/--
Same-space, corrected-range subcase of the source-shaped conclusion of
`thm:main-formal`.

This theorem records the portion of the printed two-space source theorem that is
already obtained from the current checked interface: after forgetting a
`SameSpaceProjStrat` to its underlying two-space `ProjStrat`, the three final
consistency conclusions follow under the corrected hypotheses
`400 * m * d ≤ k` and `0 < k`.

It is not a substitute for the source theorem.  The general two-space
symmetrization and the paper range `k ≥ m d` remain the separate source-boundary
work recorded in `mainFormal_sourceObligation`, whose saturated-error branch is
proved and whose remaining branch is `mainFormal_sourceSmallErrorObligation`.
The proof also inherits the transitive Section 6 successor construction gap
through `mainFormal`.

**Unfaithful:** This theorem calls `mainFormal`, whose proof transitively uses
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`.  Thus it
records a checked reduction to the current same-space interface, but is
standard-axiom clean only after the Section 6 successor construction is proved.
Documented in issue #1507 under #1458; the source theorem is
`references/ldt-paper/test_definition.tex:180-202`, and the transitive Section
6 construction is `references/ldt-paper/inductive_step.tex:441-551`.
Elimination: prove the native Section 6 small-error successor construction. -/
theorem mainFormal_sourceConclusion_ofSameSpaceLargeK
    (params : Parameters)
    [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A : ProjMeas (Polynomial params) ι,
      ∃ G_B : ProjMeas (Polynomial params) ι,
        ConsRel strategy.toProjStrat.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.toProjStrat.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (mainFormalError params k eps) ∧
          ConsRel strategy.toProjStrat.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.toProjStrat.pointMeasurementB)
            (mainFormalError params k eps) ∧
          ConsRel strategy.toProjStrat.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (mainFormalError params k eps) := by
  simpa using
    mainFormal params strategy eps hpass k hk (hk0 := hk0)

end Test

end MIPStarRE.LDT
