
namespace MIPStarRE.LDT
namespace Test

-- source: MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:288-326  (MIPStarRE.LDT.Test.mainFormal)
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
  sorry

end Test
end MIPStarRE.LDT
