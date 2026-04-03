import MIPStarRE.LDT.MakingMeasurementsProjective.Theorems

set_option linter.style.longLine false

/-!
Definitions for Section 6 of the low individual degree paper in
`references/ldt-paper/inductive_step.tex`.

This file contains restriction/lifting maps, section-local error terms,
averaging operators, and temporary tensor-placement helpers.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift an axis-line answer from the restricted slice back to the ambient space. -/
def liftAxisAnswer (params : Parameters) (x : Fq params) :
    AxisLinePolynomial params → AxisLinePolynomial params.next :=
  fun f => AxisLinePolynomial.appendAtHeight params f x

/-- Lift a diagonal-line answer from the restricted slice back to the ambient space. -/
def liftDiagonalAnswer (params : Parameters) (x : Fq params) :
    DiagonalLinePolynomial params → DiagonalLinePolynomial params.next :=
  fun f => DiagonalLinePolynomial.appendAtHeight params f x

/-- Restricted slice data keeps the point and axis-parallel measurements complete,
but only records a projective submeasurement on diagonal lines. The ambient
measurement type allows outcomes of degree up to `(m + 1) d`, while the honest
slice pullback only sees the degree-`m d` image. -/
structure RestrictedSymStrat (params : Parameters) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurement :
    IdxProjSubMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

namespace RestrictedSymStrat

/-- Sampled point answers in the axis-parallel lines test. -/
noncomputable def axisParallelPointAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Trace-based failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  consError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (IdxSubMeas.liftLeft (axisParallelPointAnswerFamily strategy))
    (IdxSubMeas.liftLeft (axisParallelLineAnswerFamily strategy))

/-- Trace-based failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  sscError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test. -/
noncomputable def diagonalFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  consError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy))
    (IdxSubMeas.liftLeft (diagonalLineAnswerFamily strategy))

/-- Goodness data for a restricted strategy. -/
structure IsGood {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end RestrictedSymStrat

private def axisLinePolynomialEquiv (params : Parameters) (x : Fq params) :
    AxisLinePolynomial params ≃ AxisLinePolynomial params.next where
  toFun := liftAxisAnswer params x
  invFun := fun f => AxisLinePolynomial.restrictAtHeight params f x
  left_inv := by
    intro f
    cases f
    rfl
  right_inv := by
    intro f
    cases f
    rfl

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
noncomputable def restrictAxisParallelMeasurement (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    let restrictedTotal : MIPStarRE.Quantum.Op ι :=
      ∑ f : AxisLinePolynomial params,
        lifted.toSubMeas.outcome (liftAxisAnswer params x f)
    have hrestrictedTotal :
        restrictedTotal = 1 := by
      calc
        restrictedTotal
          = ∑ g : AxisLinePolynomial params.next, lifted.toSubMeas.outcome g := by
              simpa [restrictedTotal] using
                (Fintype.sum_equiv (axisLinePolynomialEquiv params x)
                  (fun f => lifted.toSubMeas.outcome (liftAxisAnswer params x f))
                  (fun g => lifted.toSubMeas.outcome g)
                  (by intro f; rfl))
        _ = 1 := by
            rw [lifted.toSubMeas.sum_eq_total, lifted.total_eq_one]
    { toMeasurement := {
        toSubMeas := {
          outcome := fun f =>
            lifted.toSubMeas.outcome (liftAxisAnswer params x f)
          total := 1
          outcome_pos := fun f => lifted.outcome_pos (liftAxisAnswer params x f)
          sum_eq_total := by
            simpa [restrictedTotal] using hrestrictedTotal
          total_le_one := by
            change Matrix.PosSemidef ((1 : MIPStarRE.Quantum.Op ι) - 1)
            simpa using (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : MIPStarRE.Quantum.Op ι))
        }
        total_eq_one := by
          rfl }
      proj := fun f => lifted.proj (liftAxisAnswer params x f) }

/-- Restrict a diagonal-line measurement to the slice at height `x`. -/
noncomputable def restrictDiagonalMeasurement (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjSubMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)
    { toSubMeas := {
        outcome := fun f =>
          lifted.toSubMeas.outcome (liftDiagonalAnswer params x f)
        total := ∑ f : DiagonalLinePolynomial params,
          lifted.toSubMeas.outcome (liftDiagonalAnswer params x f)
        outcome_pos := fun f => lifted.outcome_pos (liftDiagonalAnswer params x f)
        sum_eq_total := by
          rfl
        total_le_one := by
          classical
          calc
            ∑ f : DiagonalLinePolynomial params,
                lifted.toSubMeas.outcome (liftDiagonalAnswer params x f)
              = ∑ g ∈ (Finset.univ.image (liftDiagonalAnswer params x)),
                  lifted.toSubMeas.outcome g := by
                    symm
                    exact Finset.sum_image (by
                      intro f _ g _ hfg
                      cases f
                      cases g
                      cases hfg
                      rfl)
            _ ≤ ∑ g : DiagonalLinePolynomial params.next, lifted.toSubMeas.outcome g := by
                  exact Finset.sum_le_univ_sum_of_nonneg
                    (s := Finset.univ.image (liftDiagonalAnswer params x))
                    (w := fun g => lifted.outcome_pos g)
            _ = lifted.toSubMeas.total := by
                  rw [lifted.toSubMeas.sum_eq_total]
            _ ≤ 1 := lifted.toSubMeas.total_le_one
      }
      proj := fun f => lifted.proj (liftDiagonalAnswer params x f) }

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
noncomputable def xRestrictedStrategy (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) : RestrictedSymStrat params ι where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement := restrictAxisParallelMeasurement params strategy x
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

@[simp] theorem restrictAxisParallelMeasurement_outcome (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas.outcome f) =
      (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftAxisAnswer params x f) :=
  rfl

@[simp] theorem restrictDiagonalMeasurement_outcome (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) (f : DiagonalLinePolynomial params) :
    ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas.outcome f) =
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftDiagonalAnswer params x f) :=
  rfl

/-- The intermediate `ν` from `thm:main-induction`. -/
noncomputable def mainInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
    (Real.rpow eps (1 / (1024 : Error)) +
      Real.rpow delta (1 / (1024 : Error)) +
      Real.rpow gamma (1 / (1024 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))

/-- The explicit `σ` of `thm:main-induction`. -/
noncomputable def mainInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (mainInductionNu params k eps delta gamma +
      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- The section-local self-improvement error. -/
noncomputable def selfImprovementInInductionError (params : Parameters)
    (eps delta _gamma : Error) : Error :=
  3000 * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The intermediate `ν` from the section-local pasting theorem. -/
noncomputable def ldPastingInInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma zeta : Error) : Error :=
  100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The section-local pasting consistency error. -/
noncomputable def ldPastingInInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error) : Error :=
  kappa * (1 + 1 / (100 * (params.m : Error))) +
    2 * ldPastingInInductionNu params k eps delta gamma zeta +
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Weighted sum of operators over a distribution's finite support.
Local copy to break import cycle with `ExpansionHypercubeGraph.Defs`. -/
private noncomputable def averageOperatorOverDistribution' {α : Type*}
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in boundedness. -/
noncomputable def averagedPointEvaluationOperator (params : Parameters)
    (strategy : SymStrat params ι) (h : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}`. -/
noncomputable def averagedSlicePointEvaluationOperator (params : Parameters)
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

/-- Tensor-failure expectation on a bipartite space.

Computes `⟨ψ| (Z ⊗ I)(I ⊗ (I - Σ H_a)) |ψ⟩` where `Z` acts on the left register
and `H` acts on the right register. -/
noncomputable def tensorFailureExpectation {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op ιA) (H : SubMeas Outcome ιB) :
    Error :=
  ev ψ <|
    leftTensor (ι₂ := ιB) Z *
      rightTensor (ι₁ := ιA) (1 - H.total)

/-- Probability that a sampled test line in `F_q^{m+1}` is not parallel to the new axis. -/
noncomputable def sliceTransverseDirectionWeight (params : Parameters) : Error :=
  (params.m : Error) / (((params.m + 1 : ℕ) : Error))

/-- Reciprocal loss incurred when conditioning away the new axis direction. -/
noncomputable def sliceConditioningLoss (params : Parameters) : Error :=
  (((params.m + 1 : ℕ) : Error) / (params.m : Error))

/-- In the current diagonal-test encoding, restricting to the slice at height
`x` corresponds to conditioning on the sampled ambient diagonal direction having
last coordinate `0`. This event has probability `1 / q`. -/
noncomputable def sliceDiagonalDirectionWeight (params : Parameters) : Error :=
  1 / (params.q : Error)

/-- Reciprocal loss incurred when conditioning the diagonal test onto a fixed
slice in the current encoding. -/
noncomputable def sliceDiagonalConditioningLoss (params : Parameters) : Error :=
  (params.q : Error)

end MIPStarRE.LDT.MainInductionStep
