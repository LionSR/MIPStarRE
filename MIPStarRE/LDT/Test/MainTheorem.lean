import MIPStarRE.LDT.Test.Strategy

/-!
# Section 3 — Main theorem

The main formal output of the low individual degree test (`thm:main-formal`).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

namespace Test

/-- The explicit `ν` from `thm:main-formal`, recorded with the paper's formula. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))

/--
`thm:main-formal` from `test_definition.tex`.
-/
theorem mainFormal
    (params : Parameters) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsWithPolyEval params strategy.state
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          G_B.toSubMeas
          (mainFormalError params k eps) ∧
        ConsWithPolyEval params strategy.state
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          G_A.toSubMeas
          (mainFormalError params k eps) ∧
        PolyMeasCons params strategy.state
          G_A.toSubMeas
          G_B.toSubMeas
          (mainFormalError params k eps) := by
  sorry

end Test

end MIPStarRE.LDT
