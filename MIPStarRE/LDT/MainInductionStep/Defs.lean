import MIPStarRE.LDT.MakingMeasurementsProjective.Theorems
import MIPStarRE.LDT.Test.Strategy

/-!
# Section 6 — Definitions

This file contains restriction/lifting maps, section-local error terms,
averaging operators, and temporary tensor-placement helpers.

## References

- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift an axis-line answer from the restricted slice back to the ambient space. -/
def liftAxisAnswer (params : Parameters) [FieldModel params.q] (x : Fq params) :
    AxisLinePolynomial params → AxisLinePolynomial params.next :=
  fun f => AxisLinePolynomial.appendAtHeight params f x

/-- Restricted slice data keeps the point and axis-parallel measurements
complete, and reindexes the ambient diagonal measurement onto slice-preserving
lines.

For the diagonal branch we retain the ambient answer space
`DiagonalLinePolynomial params.next`. This keeps the restricted family a genuine
projective measurement instead of the earlier lossy submeasurement, while still
supporting the slice-local evaluation operators used in the induction-step
bookkeeping. -/
structure RestrictedSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The bipartite state carried by the restricted strategy. -/
  state : QuantumState (ι × ι)
  /-- The restricted strategy reuses the ambient state's normalization witness. -/
  isNormalized : state.IsNormalized
  /-- The restricted point measurement. -/
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  /-- The restricted axis-parallel line measurement. -/
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  /-- Reparametrizing an axis-parallel line agrees with evaluating at the new base point. -/
  axisParallelReparamInvariant :
    MIPStarRE.LDT.AxisParallelEvaluationReparamInvariant params axisParallelMeasurement
  /-- The restricted diagonal-line measurement. -/
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params.next) ι

namespace RestrictedSymStrat

-- TODO(#306): These sampled answer families duplicate the `SymStrat` API in
-- `MIPStarRE.LDT.Test.Strategy`; refactor around shared helpers once the
-- restricted-slice bookkeeping has stabilized.

/-- Sampled point answers in the axis-parallel lines test.
Point player receives `u` (base point) and answers at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u` (parameter `zeroCoord`). -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the `j`-restricted diagonal test.
Point player receives `u` and answers at `u`. -/
noncomputable def restrictedDiagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point (parameter `zeroCoord`). -/
noncomputable def restrictedDiagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Failure surrogate for the diagonal lines test.
Averages over restriction index `j`, then the
`j`-restricted diagonal test. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution
          (RestrictedDiagonalSample params j))
        (restrictedDiagonalPointAnswerFamily strategy j)
        (restrictedDiagonalLineAnswerFamily strategy j)

/-- Goodness data for a restricted strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The restricted axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest :
    strategy.axisParallelFailureProbability ≤ eps
  /-- The restricted self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest :
    strategy.selfConsistencyFailureProbability ≤ delta
  /-- The restricted diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest :
    strategy.diagonalFailureProbability ≤ gamma

end RestrictedSymStrat

private def axisLinePolynomialEquiv (params : Parameters) [FieldModel params.q] (x : Fq params) :
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
noncomputable def restrictAxisParallelMeasurement (params : Parameters) [FieldModel params.q]
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

private theorem restrictAxisParallelMeasurement_postprocess_eval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : AxisParallelLine params) (t a : Fq params) :
    (postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas)
      (fun f => f t)).outcome a =
      (postprocess ((strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f => f t)).outcome a := by
  classical
  let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
  calc
    (postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas)
        (fun f => f t)).outcome a
      = ∑ f : AxisLinePolynomial params,
          if f t = a then lifted.toSubMeas.outcome (liftAxisAnswer params x f) else 0 := by
            simp [
              postprocess, restrictAxisParallelMeasurement, lifted,
              liftAxisAnswer, Finset.sum_filter
            ]
            apply Finset.sum_congr rfl
            intro f hf
            by_cases h : f t = a <;> simp [h]
    _ = ∑ g : AxisLinePolynomial params.next,
          if g t = a then lifted.toSubMeas.outcome g else 0 := by
            simpa [axisLinePolynomialEquiv, liftAxisAnswer, lifted] using
              (Fintype.sum_equiv (axisLinePolynomialEquiv params x)
                (fun f : AxisLinePolynomial params =>
                  if f t = a then lifted.toSubMeas.outcome (liftAxisAnswer params x f) else 0)
                (fun g : AxisLinePolynomial params.next =>
                  if g t = a then lifted.toSubMeas.outcome g else 0)
                (by
                  intro f
                  simp [axisLinePolynomialEquiv, liftAxisAnswer,
                    AxisLinePolynomial.appendAtHeight_apply]))
    _ = (postprocess (lifted.toSubMeas) (fun f => f t)).outcome a := by
          simp [postprocess, lifted, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro g hg
          by_cases h : g t = a <;> simp [h]

private theorem restrictAxisParallelMeasurement_reparamInvariant
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    MIPStarRE.LDT.AxisParallelEvaluationReparamInvariant params
      (restrictAxisParallelMeasurement params strategy x) := by
  intro ℓ t a
  calc
    (postprocess (((restrictAxisParallelMeasurement params strategy x)
      (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a
      = (postprocess ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params (AxisParallelLine.rebaseAt ℓ t) x)).toSubMeas)
          (· zeroCoord)).outcome a := by
            simpa using
              restrictAxisParallelMeasurement_postprocess_eval params strategy x
                (AxisParallelLine.rebaseAt ℓ t) zeroCoord a
    _ = (postprocess ((strategy.axisParallelMeasurement
          (AxisParallelLine.rebaseAt (AxisParallelLine.appendAtHeight params ℓ x) t)).toSubMeas)
          (· zeroCoord)).outcome a := by
            simp
    _ = (postprocess ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
          (fun f => f t)).outcome a := by
            exact strategy.axisParallelReparamInvariant
              (AxisParallelLine.appendAtHeight params ℓ x) t a
    _ = (postprocess (((restrictAxisParallelMeasurement params strategy x) ℓ).toSubMeas)
          (fun f => f t)).outcome a := by
            symm
            simpa using
              restrictAxisParallelMeasurement_postprocess_eval params strategy x ℓ t a

/-- Restrict a diagonal-line measurement to the slice at height `x` by
reindexing the ambient family along slice-preserving lines. -/
noncomputable def restrictDiagonalMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params.next) ι :=
  fun ℓ => strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
noncomputable def xRestrictedStrategy (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : RestrictedSymStrat params ι where
  state := strategy.state
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement := restrictAxisParallelMeasurement params strategy x
  axisParallelReparamInvariant :=
    restrictAxisParallelMeasurement_reparamInvariant params strategy x
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

/-- Restricting a strategy does not change its bipartite state. -/
@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

/-- Restricting a strategy reuses the parent strategy's normalization witness. -/
@[simp] theorem xRestrictedStrategy_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- Restricting a strategy reindexes point questions by appending the slice height. -/
@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Restricting an axis-parallel measurement reindexes outcomes by slice extension. -/
@[simp] theorem restrictAxisParallelMeasurement_outcome (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas.outcome f =
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftAxisAnswer params x f) :=
  rfl

/-- Restricting a diagonal measurement only reindexes the ambient diagonal line. -/
@[simp] theorem restrictDiagonalMeasurement_outcome (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) (f : DiagonalLinePolynomial params.next) :
    (restrictDiagonalMeasurement params strategy x ℓ).toSubMeas.outcome f =
      (strategy.diagonalMeasurement
        (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas.outcome f :=
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

/-- The paper-faithful diagonal conditioning weight matches the axis-parallel
branch: one conditions away the new coordinate direction, which occurs with
probability `m / (m + 1)`.

Note: `references/ldt-paper/inductive_step.tex` uses the same `((m + 1) / m)`
loss for both the axis-parallel and diagonal branches (around line 374). The
earlier `q`-based model was only a temporary placeholder. -/
noncomputable def sliceDiagonalDirectionWeight (params : Parameters) : Error :=
  sliceTransverseDirectionWeight params

/-- Reciprocal loss incurred by the paper-faithful diagonal conditioning step. -/
noncomputable def sliceDiagonalConditioningLoss (params : Parameters) : Error :=
  sliceConditioningLoss params

end MIPStarRE.LDT.MainInductionStep
