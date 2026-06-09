import MIPStarRE.LDT.Test.MainTheorem.SourceScalars
import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Final

/-!
# Main-formal soundness theorem

This module contains the corrected two-space final theorem for
`thm:main-formal`.  The theorem starts from a general projective strategy
`ProjStrat params ιA ιB`, applies the heterogeneous role-register route, and
absorbs the explicit intermediate errors into the final parameter
`mainFormalError`.

The public theorem uses the confirmed large-`k` correction `k ≥ 400 m d` and
the nonzero sampling condition `0 < k`.  These are documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `thm:main-formal` at line 180; its proof is in
  `references/ldt-paper/inductive_step.tex` (lines 26–236).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `\label{thm:main-formal}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-! ### Two-space source route -/

/--
Trivial saturated-error branch for the printed two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

**Source:** This is a source-faithful saturated-error branch: when the printed
target error is at least `1`, the consistency conclusion follows from the
normalization bound for bipartite consistency defects, without adding any
construction hypothesis to the source theorem.

Whenever `mainFormalError params k eps ≥ 1`, the three consistency conclusions
hold for arbitrary projective polynomial measurements, since each underlying
consistency defect is bounded by `1` for a normalized bipartite state and a
uniform question distribution.  The argument does not use the low individual
degree test hypothesis. -/
theorem mainFormal_trivial_witness
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
  let trivialA : ProjMeas (Polynomial params) ιA :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  let trivialB : ProjMeas (Polynomial params) ιB :=
    ProjMeas.trivialDistinguishedOutcome (default : Polynomial params)
  refine ⟨trivialA, trivialB, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) herr⟩

/-- Source role-register conclusion after the scalar branch has supplied
`0 < k`.

This theorem is not an additional hypothesis of `thm:main-formal`; it isolates
the checked two-space role-register construction from the scalar absorption at
the corrected nonzero sampling boundary.  The proof uses
`ProjStrat.sourceRoleRegisterFinalPointConsistency` and then weakens the three
explicit pre-absorption errors to `mainFormalError` by the existing Step 8
scalar cascade. -/
theorem mainFormalConclusion_ofRoleRegisterScalarBoundary
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
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
  have hepsNN : 0 ≤ eps := ProjStrat.eps_nonneg_of_passes hpass
  let scalars : MainFormalScalarBounds params eps k :=
    MainFormalScalarBounds.ofNontrivialMainFormal hepsNN hk0 hsmall
  let σsrc : Error :=
    2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)
  let ζ₁src : Error :=
    σsrc + 2 * Real.sqrt (3 * eps + σsrc) + (params.m * params.d : Error) / params.q
  let ζ₂src : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src
  let ηsrc : Error :=
    ζ₁src + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ₁src)
  let ζ₃src : Error := 6 * ζ₁src + 6 * ζ₂src
  have hσsrc : σsrc = 2 * scalars.sigma := by
    simp [σsrc, MainFormalScalarBounds.sigma, mainFormalScalarSigma_eq_mainInductionError]
  have hζ₁src : ζ₁src = scalars.zeta1 := by
    simp [ζ₁src, σsrc, MainFormalScalarBounds.zeta1, cascadeZeta1,
      MainFormalScalarBounds.sigma, mainFormalScalarSigma_eq_mainInductionError]
  have hζ₂src : ζ₂src ≤ scalars.zeta2 := by
    change MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ₁src ≤ scalars.zeta2
    rw [hζ₁src]
    exact MainFormalScalarBounds.orthonormalizeAndCompleteError_zeta1_le_zeta2
      scalars hsmall
  have hηsrc : ηsrc = scalars.line169Error := by
    have hζ0 : 0 ≤ scalars.zeta1 := MainFormalScalarBounds.zeta1_nonneg scalars
    have hsqrt :
        Real.sqrt (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1) =
          10 * Real.rpow scalars.zeta1 (1 / (8 : Error)) :=
      MakingMeasurementsProjective.sqrt_orthonormalizationError_eq hζ0
    simp [ηsrc, hζ₁src, MainFormalScalarBounds.line169Error,
      cascadeLine169RepairError, hsqrt]
  have hζ₃src : ζ₃src ≤ scalars.zeta3 := by
    have hζ₁le : ζ₁src ≤ scalars.zeta1 := le_of_eq hζ₁src
    have hcore : 6 * ζ₁src + 6 * ζ₂src ≤ 6 * scalars.zeta1 + 6 * scalars.zeta2 := by
      nlinarith
    simpa [ζ₃src, MainFormalScalarBounds.zeta3, cascadeZeta3] using hcore
  have hsourcePoint :
      σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ mainFormalError params k eps := by
    have hrad :
        ηsrc + ζ₃src / 2 ≤ scalars.line169Error + scalars.zeta3 / 2 := by
      have hηle : ηsrc ≤ scalars.line169Error := le_of_eq hηsrc
      nlinarith
    have hsqrt :
        Real.sqrt (ηsrc + ζ₃src / 2) ≤
          Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) :=
      Real.sqrt_le_sqrt hrad
    have hrepaired :
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2) ≤ scalars.zeta4Repaired := by
      calc
        σsrc + 2 * Real.sqrt (ηsrc + ζ₃src / 2)
            = 2 * scalars.sigma + 2 * Real.sqrt (ηsrc + ζ₃src / 2) := by
              rw [hσsrc]
        _ ≤ 2 * scalars.sigma + 2 *
              Real.sqrt (scalars.line169Error + scalars.zeta3 / 2) := by
            nlinarith
        _ = scalars.zeta4Repaired := by
            rfl
    exact hrepaired.trans (MainFormalScalarBounds.zeta4Repaired_le_mainFormalError scalars)
  have hsourceSelf :
      ζ₃src / 2 ≤ mainFormalError params k eps := by
    have htoCascade : ζ₃src / 2 ≤ scalars.zeta3 / 2 := by
      nlinarith
    exact htoCascade.trans (MainFormalScalarBounds.zeta3_div_two_le_mainFormalError scalars)
  rcases ProjStrat.sourceRoleRegisterFinalPointConsistency
      params strategy eps hpass k hk with ⟨Q_A, Q_B, hA, hrest⟩
  rcases hrest with ⟨hB, hrest⟩
  rcases hrest with ⟨_hQQEval, hQQ⟩
  refine ⟨Q_A, Q_B, ?_, ?_, ?_⟩
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hA
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourcePoint) hB
  · exact ConsRel.mono (by
      simpa [σsrc, ζ₁src, ζ₂src, ηsrc, ζ₃src] using hsourceSelf) hQQ

/--
Small-error branch for the corrected two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the small-error branch of the corrected source theorem.
It is not an additional hypothesis of `thm:main-formal`; the source-boundary
reduction below calls it only after the saturated-error branch has been
discharged by `mainFormal_trivial_witness`.

The heterogeneous role-register symmetrization, factor-two
unsymmetrization, point-agreement branch, heterogeneous triangle step,
Schwartz--Zippel Step 5 calculation, the step making measurements projective,
completion, line-169 transport, final point-evaluation triangle, and scalar absorption into
`mainFormalError` are checked in the two-space route once the nonzero
scalar-cascade boundary `0 < k` is supplied.  This nonzero boundary is the
correction recorded in
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`. -/
theorem mainFormal_smallErrorConclusion
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
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
  exact
    mainFormalConclusion_ofRoleRegisterScalarBoundary
      params strategy eps hpass k hk hk0 hsmall

/--
Source-boundary reduction for the corrected two-space theorem
`thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem closes the saturated-error branch of the source-boundary
argument.  If `mainFormalError params k eps ≥ 1`, the conclusion follows from
`mainFormal_trivial_witness`; otherwise the proof is exactly the named
small-error branch `mainFormal_smallErrorConclusion`.  This reduction
is not an additional hypothesis of `thm:main-formal`.
-/
theorem mainFormalConclusion
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
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
  · exact mainFormal_trivial_witness params strategy eps k hlarge
  · exact mainFormal_smallErrorConclusion params strategy eps hpass k hk hk0 hlarge

/--
Corrected source statement of `thm:main-formal`.

Paper origin: `references/ldt-paper/test_definition.tex:180-202`.

This theorem records the two-space source theorem with the confirmed large-`k`
correction `k ≥ 400 m d`.  The paper prints the weaker hypothesis `k ≥ m d`;
the missing factor `400` is documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  The additional condition
`0 < k` corrects the zero-sampling boundary where the printed error collapses
to zero; this boundary is documented in
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`. -/
theorem mainFormal
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k) :
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
  exact mainFormalConclusion params strategy eps hpass k hk hk0

end Test

end MIPStarRE.LDT
