import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Main-formal soundness theorem

Base handoff, final projective-completion transport, and the paper-facing proof
gap for `thm:main-formal` (`\Cref{thm:main-formal}`).  This module contains:

* `mainFormalBaseRoleInductionWitness` — names the Section 6 role-register witness
  used by the base case `m = 1`.

* `mainFormal_ofProjectiveCompletionTransportWitness` — derives the three consistency
  conclusions of `thm:main-formal` from a constructed Section 6
  projective-completion witness.

* `mainFormal` — the paper theorem statement, taking a projective strategy that
  passes the LID test with probability `≥ 1 − ε`, together with the explicit
  boundary conditions `0 < d`, `0 < k`, and `400md ≤ k`, and producing the three
  pointwise consistency targets at error bound `mainFormalError`.  Its proof now
  follows the checked branch structure: the vacuous branch is closed by
  `mainFormal_trivial_witness`, the non-vacuous branch invokes the Section 6
  role-register witness, the post-role projective-completion construction
  target, and the final transport.  The remaining proof gaps are the named
  construction theorems used by this chain, not additional hypotheses of
  `mainFormal`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `\Cref{thm:main-formal}` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`; and
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
through separate bridge and obligation packages.  The current public theorem below
does not keep such packages as hypotheses: the theorem remains paper-shaped, and
the missing construction is represented by a direct proof gap. -/


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
scalar absorption steps; it does not introduce additional bridge hypotheses. -/
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
`thm:main-formal` from `test_definition.tex`.

This is the paper theorem statement. The statement includes the large-`k` and
positive-boundary conditions currently needed by the formalization, but it does
not assume repaired auxiliary data, role-register witness data, or final
projective-completion hypotheses. Those remain open steps to be derived from the
pass condition and the preceding sections.

The hypothesis `hk : 400 * params.m * params.d ≤ k`, together with `hk0`,
records the strengthened boundary from issue #906 and
`rem:main-formal-k-boundary`; the paper states the weaker condition `k ≥ md`.
The field model is presently fixed at universe level `0`, matching the current
Section 6 successor theorem rather than an additional mathematical restriction.

**Proof gap:** the paper-facing statement has no bridge, residual, repair, or
obligation hypotheses.  In the non-vacuous branch the proof constructs the
scalar cascade and role-register witness from the paper hypotheses, then calls
`MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness`
and the already proved final transport.  The transitive proof gaps are therefore
localized in the named construction theorems: the Section 6 successor proof
inside `MainInductionStep.mainInduction`, and the exact line-169 match-mass
preservation obligation in the post-role completion step.  That exact route is
tracked by #1610; the checked local repair has an explicit additional loss.
These are tracked by #1043, #1363, #1369, #1458, #1507, #1566, and #1610.

**Unfaithful:** This proof currently depends transitively on
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_with_matchMass`,
whose exact match-mass preservation conclusion is not yet derived from
`thm:main-formal` and the cited Section 5 and Step 6 arguments in
`references/ldt-paper/inductive_step.tex`.  This is documented in issue #1610
and in `docs/paper-gaps/issue-1099-line169-triangle-sub-loss.tex`.
Elimination: prove the exact construction-level monotonicity from the paper
hypotheses, or route the final theorem through the repaired line-169 estimate
with its explicit loss, without adding a non-paper hypothesis to `mainFormal`.
-/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (_hd : 0 < params.d)
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
    rcases MainFormalRoleInductionWitness.ofMainInductionLargeK
        params strategy eps k hpass hk with ⟨roleInductionWitness⟩
    rcases
        MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness
          (scalars := scalars) hlarge roleInductionWitness with
      ⟨projectiveCompletionWitness⟩
    exact mainFormal_ofProjectiveCompletionTransportWitness (hpass := hpass)
      projectiveCompletionWitness

end Test

end MIPStarRE.LDT
