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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift an axis-line answer from the restricted slice back to the ambient space. -/
def liftAxisAnswer (params : Parameters) (x : Fq params) :
    AxisLinePolynomial params → AxisLinePolynomial params.next :=
  fun f => AxisLinePolynomial.appendAtHeight params f x

/-- Lift a diagonal-line answer from the restricted slice back to the ambient space. -/
def liftDiagonalAnswer (params : Parameters) (x : Fq params) :
    DiagonalLinePolynomial params → DiagonalLinePolynomial params.next :=
  fun f => DiagonalLinePolynomial.appendAtHeight params f x

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
def restrictAxisParallelMeasurement (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeas := {
        outcome := fun f =>
          lifted.toSubMeas.outcome (liftAxisAnswer params x f)
        total := lifted.toSubMeas.total
      } } }

/-- Restrict a diagonal-line measurement to the slice at height `x`. -/
def restrictDiagonalMeasurement (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeas := {
        outcome := fun f =>
          lifted.toSubMeas.outcome (liftDiagonalAnswer params x f)
        total := lifted.toSubMeas.total
      } } }

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
def xRestrictedStrategy (params : Parameters)
    (strategy : SymStrat params.next ι) (x : Fq params) : SymStrat params ι where
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
  (𝒟.support.map fun a => 𝒟.weight a • f a).sum

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
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op ιA) (H : SubMeas Outcome ιB) :
    Error :=
  ev ψ <|
    leftTensor (ι₂ := ιB) Z *
      rightTensor (ι₁ := ιA) (1 - H.total)

/-- The uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def sliceHeightDistribution (params : Parameters) : Distribution (Fq params) :=
  uniformDistribution (Fq params)

/-- Average over the uniform choice of a slice height `x ∈ F_q`. -/
noncomputable def averageOverSlices (params : Parameters) (f : Fq params → Error) : Error :=
  avgOver (sliceHeightDistribution params) f

/-- Weighted average over uniformly chosen slice heights. -/
noncomputable def weightedAverageOverSlices (params : Parameters)
    (w : Error) (f : Fq params → Error) : Error :=
  averageOverSlices params (fun x => w * f x)

/-- Probability that a sampled test line in `F_q^{m+1}` is not parallel to the new axis. -/
noncomputable def sliceTransverseDirectionWeight (params : Parameters) : Error :=
  (params.m : Error) / (((params.m + 1 : ℕ) : Error))

/-- Reciprocal loss incurred when conditioning away the new axis direction. -/
noncomputable def sliceConditioningLoss (params : Parameters) : Error :=
  (((params.m + 1 : ℕ) : Error) / (params.m : Error))

end MIPStarRE.LDT.MainInductionStep
