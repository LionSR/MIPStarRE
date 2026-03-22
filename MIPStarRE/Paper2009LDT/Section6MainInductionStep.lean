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

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
def restrictAxisParallelMeasurement (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params) :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeasurement := { name := s!"{lifted.toSubMeasurement.name}.restrict({x.1})" } } }

/-- Restrict a diagonal-line measurement to the slice at height `x`. -/
def restrictDiagonalMeasurement (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params) :=
  fun ℓ =>
    let lifted := strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)
    { toMeasurement := { toSubMeasurement := { name := s!"{lifted.toSubMeasurement.name}.restrict({x.1})" } } }

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
def xRestrictedStrategy (params : Parameters)
    (strategy : SymmetricStrategy params.next) (x : Fq params) : SymmetricStrategy params where
  state := strategy.state
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement := restrictAxisParallelMeasurement params strategy x
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

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
  selfCloseness :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (constantSubMeasurementFamily H.toSubMeasurement)
      (selfImprovementInInductionError params eps delta gamma)
  bounded :
    BoundedByOperator strategy.state H.toSubMeasurement Z
      (selfImprovementInInductionError params eps delta gamma)

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

/-- Placeholder average restricted axis-parallel error over slices. -/
def averageRestrictedAxisParallelError (params : Parameters)
    (_strategy : SymmetricStrategy params.next) : Error := 0

/-- Placeholder average restricted self-consistency error over slices. -/
def averageRestrictedSelfConsistencyError (params : Parameters)
    (_strategy : SymmetricStrategy params.next) : Error := 0

/-- Placeholder average restricted diagonal-line error over slices. -/
def averageRestrictedDiagonalError (params : Parameters)
    (_strategy : SymmetricStrategy params.next) : Error := 0

/-- Bookkeeping package for the restricted-probabilities lemma. -/
structure RestrictedProbabilitiesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma : Error) : Prop where
  axisParallelAverage :
    averageRestrictedAxisParallelError params strategy
      ≤ (((params.m + 1 : ℕ) : Error) / (params.m : Error)) * eps
  selfConsistencyAverage :
    averageRestrictedSelfConsistencyError params strategy ≤ delta
  diagonalAverage :
    averageRestrictedDiagonalError params strategy
      ≤ (((params.m + 1 : ℕ) : Error) / (params.m : Error)) * gamma

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ) :
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
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ) :
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
