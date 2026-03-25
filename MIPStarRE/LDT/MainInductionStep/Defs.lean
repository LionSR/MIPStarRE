import MIPStarRE.LDT.MakingMeasurementsProjective.Theorems

/-!
Definitions for Section 6 of the low individual degree paper in
`references/ldt-paper/inductive_step.tex`.

This file contains restriction/lifting maps, section-local error terms,
averaging operators, and temporary tensor-placement helpers.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

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
    (strategy : SymmetricStrategy params.next) (x : Fq params) :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params) :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeasurement := {
        name := s!"{lifted.toSubMeasurement.name}.restrict({x.1})"
        outcomeOperator := fun f =>
          lifted.toSubMeasurement.outcomeOperator (liftAxisAnswer params x f)
        totalOperator := lifted.toSubMeasurement.totalOperator
      } } }

/-- Restrict a diagonal-line measurement to the slice at height `x`. -/
def restrictDiagonalMeasurement (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params) :=
  fun ℓ =>
    let lifted := strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeasurement := {
        name := s!"{lifted.toSubMeasurement.name}.restrict({x.1})"
        outcomeOperator := fun f =>
          lifted.toSubMeasurement.outcomeOperator (liftDiagonalAnswer params x f)
        totalOperator := lifted.toSubMeasurement.totalOperator
      } } }

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
def xRestrictedStrategy (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) : SymmetricStrategy params where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement := restrictAxisParallelMeasurement params strategy x
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

@[simp] theorem restrictAxisParallelMeasurement_outcomeOperator (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    ((restrictAxisParallelMeasurement params strategy x ℓ)
      .toSubMeasurement.outcomeOperator f) =
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x))
        .toSubMeasurement.outcomeOperator
          (liftAxisAnswer params x f) :=
  rfl

@[simp] theorem restrictDiagonalMeasurement_outcomeOperator (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params)
    (ℓ : DiagonalLine params) (f : DiagonalLinePolynomial params) :
    ((restrictDiagonalMeasurement params strategy x ℓ)
      .toSubMeasurement.outcomeOperator f) =
      (strategy.diagonalMeasurement
        (DiagonalLine.appendAtHeight params ℓ x))
        .toSubMeasurement.outcomeOperator
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

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in boundedness. -/
noncomputable def averagedPointEvaluationOperator (params : Parameters)
    (strategy : SymmetricStrategy params) (h : Polynomial params) : Operator := by
  classical
  let 𝒟 : Distribution (Point params) := uniformDistribution (Point params)
  let u₀ : Point params := Classical.choice (inferInstance : Nonempty (Point params))
  exact weightedOperatorSumOnSupport
    ((strategy.pointMeasurement u₀).toSubMeasurement.outcomeOperator (h u₀))
    𝒟.support 𝒟.weight
    (fun u => (strategy.pointMeasurement u).toSubMeasurement.outcomeOperator (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}`. -/
noncomputable def averagedSlicePointEvaluationOperator (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (x : Fq params) (g : Polynomial params) : Operator := by
  classical
  let 𝒟 : Distribution (Point params) := uniformDistribution (Point params)
  let u₀ : Point params := Classical.choice (inferInstance : Nonempty (Point params))
  exact weightedOperatorSumOnSupport
    ((strategy.pointMeasurement (appendPoint params u₀ x))
      .toSubMeasurement.outcomeOperator (g u₀))
    𝒟.support 𝒟.weight
    (fun u =>
      (strategy.pointMeasurement (appendPoint params u x))
        .toSubMeasurement.outcomeOperator (g u))

/-- TODO(tensor): replace this placeholder left placement by an honest tensor-product
embedding once the bipartite matrix API is available.
NOTE: duplicated from CommutativityPoints; should be factored into a shared
utility once the import graph permits it. -/
def leftPlacedSubMeasurement {α : Type*} (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.left"
  outcomeOperator := fun a => leftTensor (A.outcomeOperator a)
  totalOperator := leftTensor A.totalOperator

/-- TODO(tensor): replace this placeholder right placement by an honest tensor-product
embedding once the bipartite matrix API is available. -/
def rightPlacedSubMeasurement {α : Type*} (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.right"
  outcomeOperator := fun a => rightTensor (A.outcomeOperator a)
  totalOperator := rightTensor A.totalOperator

/-- TODO(tensor): this uses the placeholder `leftTensor` / `rightTensor` embeddings until
the project has an honest bipartite operator API. -/
noncomputable def tensorFailureExpectation {Outcome : Type*}
    (ψ : QuantumState) (Z : Operator) (H : SubMeasurement Outcome) : Error :=
  expectationValue ψ <|
    operatorMul
      (leftTensor Z)
      (rightTensor (operatorDifference (identityLike H.totalOperator) H.totalOperator))

/-- The uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def sliceHeightDistribution (params : Parameters) : Distribution (Fq params) :=
  uniformDistribution (Fq params)

/-- Average over the uniform choice of a slice height `x ∈ F_q`. -/
noncomputable def averageOverSlices (params : Parameters) (f : Fq params → Error) : Error :=
  averageOverDistribution (sliceHeightDistribution params) f

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
