import MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

/-!
Matching scaffold for Section 6 of the low individual degree paper in
`references/ldt-paper/inductive_step.tex`.

The declarations below follow the paper's theorem DAG: main induction, the
section-local self-improvement theorem, the section-local pasting theorem, and the
restricted-strategy bookkeeping lemma.
-/

namespace MIPStarRE.Paper2009LDT.Section6MainInductionStep

open MIPStarRE.Paper2009LDT

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
    ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeasurement.outcomeOperator f) =
      (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeasurement.outcomeOperator
        (liftAxisAnswer params x f) :=
  rfl

@[simp] theorem restrictDiagonalMeasurement_outcomeOperator (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params)
    (ℓ : DiagonalLine params) (f : DiagonalLinePolynomial params) :
    ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeasurement.outcomeOperator f) =
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeasurement.outcomeOperator
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

/-- Placeholder for the averaged point operator `E_u A^u_{h(u)}` appearing in boundedness. -/
def averagedPointEvaluationOperator (params : Parameters)
    (_strategy : SymmetricStrategy params) (_h : Polynomial params) : Operator :=
  { name := s!"Aavg({params.m},{params.q},{params.d})" }

/-- Placeholder for the slice-wise averaged point operator `E_u A^{u,x}_{g(u)}`. -/
def averagedSlicePointEvaluationOperator (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (x : Fq params) (_g : Polynomial params) : Operator :=
  { name := s!"AavgSlice({params.m},{params.q},{params.d},{x.1})" }

/-- Output package for the induction-level self-improvement theorem. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    (strategy : SymmetricStrategy params)
    (_G : SubMeasurement (Polynomial params))
    (H : ProjectiveSubMeasurement (Polynomial params))
    (Z : Operator) (eps delta gamma nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeasurement
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  pointConsistency :
    ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (selfImprovementInInductionError params eps delta gamma)
  strongSelfConsistency :
    PolynomialMeasurementStronglySelfConsistent params strategy.state H.toSubMeasurement
      (selfImprovementInInductionError params eps delta gamma)
  selfCloseness :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (selfImprovementInInductionError params eps delta gamma)
  bounded :
    BoundedByOperator strategy.state H.toSubMeasurement Z
      (selfImprovementInInductionError params eps delta gamma)
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      DominatesOperator Z (averagedPointEvaluationOperator params strategy h)

/-- Output package for the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (H : Measurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

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

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    (strategy : SymmetricStrategy params.next) : Type where
  axisParallel : Fq params → Error
  selfConsistency : Fq params → Error
  diagonal : Fq params → Error
  restrictedGood :
    ∀ x,
      (xRestrictedStrategy params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over slices. -/
noncomputable def averageRestrictedAxisParallelError (params : Parameters)
    {strategy : SymmetricStrategy params.next}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    {strategy : SymmetricStrategy params.next}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    {strategy : SymmetricStrategy params.next}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  averageOverSlices params profile.diagonal

/-- Source-style boundedness input for the induction-level pasting theorem. -/
structure PastingBoundednessInput (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator params strategy x g

/-- Bookkeeping package for the restricted-probabilities lemma. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma : Error) : Prop where
  profileExists :
    ∃ profile : RestrictedFailureProfile params strategy,
      weightedAverageOverSlices params
          (sliceTransverseDirectionWeight params) profile.axisParallel ≤ eps ∧
        averageRestrictedAxisParallelError params profile
          ≤ sliceConditioningLoss params * eps ∧
        averageRestrictedSelfConsistencyError params profile ≤ delta ∧
        weightedAverageOverSlices params
          (sliceTransverseDirectionWeight params) profile.diagonal ≤ gamma ∧
        averageRestrictedDiagonalError params profile
          ≤ sliceConditioningLoss params * gamma ∧
        sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps ∧
        sliceTransverseDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params),
      ConsistentWithPolynomialEvaluation params strategy.state
        (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
        G.toSubMeasurement
        (mainInductionError params k eps delta gamma) := by
  sorry

/-- `thm:self-improvement-in-induction-section`. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params))
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement) G nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params), ∃ Z : Operator,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  sorry

/-- `thm:ld-pasting-in-induction-section`. -/
theorem ldPastingInInductionSection
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next),
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  sorry

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.Paper2009LDT.Section6MainInductionStep
