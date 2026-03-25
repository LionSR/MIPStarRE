import MIPStarRE.LDT.Pasting.Sandwich

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints

noncomputable section

/-- The final completeness lower bound used in the pasting statements. -/
noncomputable def ldPastingCompletenessLowerBound (params : Parameters)
    (kappa nu : Error) (k : ℕ) : Error :=
  1 - kappa * (1 + 1 / (100 * (params.m : Error))) - nu -
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Displayed error term for `lem:commutativity-switcheroo`. -/
noncomputable def commutativitySwitcherooError
    (zeta omega chi : Error) : Error :=
  6 * Real.rpow zeta (1 / (2 : Error)) +
    6 * Real.rpow omega (1 / (2 : Error)) +
    4 * Real.rpow chi (1 / (2 : Error))

/-- Displayed error term for `cor:commuting-with-G-complete`. -/
noncomputable def commutingWithGCompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  36 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `cor:commuting-with-G-incomplete`. -/
noncomputable def commutingWithGIncompleteError (params : Parameters)
    (gamma zeta : Error) : Error :=
  commutingWithGCompleteError params gamma zeta

/-- Displayed self-consistency error for `\widehat G`. -/
def gHatSelfConsistencyError (zeta : Error) : Error :=
  2 * zeta

/-- Displayed commutation error for `\widehat G`. -/
noncomputable def gHatCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  138 * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for commuting past `k` completed slices. -/
noncomputable def commuteGHalfSandwichError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)))

/-- Displayed error term for `lem:ld-sandwich-line-one-point`. -/
noncomputable def ldSandwichLineOnePointError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  43 * (k : Error) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:h-b-consistency`. -/
noncomputable def hBConsistencyError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:over-all-outcomes`. -/
noncomputable def overAllOutcomesError (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) : Error :=
  46 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- Displayed error term for `lem:from-H-to-G`. -/
noncomputable def fromHToGError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  46 * (k : Error) * (params.m : Error) *
    (Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The per-step recurrence loss from the proof of `lem:from-H-to-G`. -/
noncomputable def fromHToGRecurrenceError (params : Parameters)
    (gamma zeta : Error) (k : ℕ) : Error :=
  2 * Real.rpow (2 * zeta) (1 / (2 : Error)) +
    2 * Real.rpow (commuteGHalfSandwichError params gamma zeta k) (1 / (2 : Error))

/-- Output package for `thm:ld-pasting`. -/
structure LdPastingConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : Measurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedMeasurement :
    H = constructedPastedMeasurement params family k
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H.toSubMeasurement
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)

/-- Output package for `lem:ld-pasting-sub-measurement`. -/
structure LdPastingSubMeasurementConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (H : SubMeasurement (Polynomial params.next))
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedSubMeasurement :
    H = constructedPastedSubMeasurement params family k
  pointConsistency :
    ConsistentWithPolynomialEvaluation params.next strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      H
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)
  completeness :
    CompletenessAtLeast strategy.state H
      (ldPastingCompletenessLowerBound params kappa
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) k)

/-- Output package for `lem:g-complete-self-consistency`. -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params) (zeta : Error) : Prop where
  completePartSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (completePartLeftFamily params family)
      (completePartRightFamily params family)
      zeta

/-- Output package for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params) (zeta : Error) : Prop where
  completePartWitness :
    GCompleteSelfConsistencyStatement params ψ family zeta
  incompletePartSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta

/-- Output package for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type*} (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome)
    (zeta omega chi : Error) : Prop where
  aggregateCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family M)
      (switcherooAggregateRight params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Output package for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  pointWithCompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutingWithGCompleteError params gamma zeta)
  completePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Output package for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  completePartWitness :
    CommutingWithGCompleteStatement params ψ family gamma zeta
  pointWithIncompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft params family)
      (incompletePartPointProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)
  incompletePartCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft params family)
      (incompletePartTotalProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Output package for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  completePartSelfConsistencyWitness :
    GCompleteSelfConsistencyStatement params ψ family zeta
  incompletePartSelfConsistencyWitness :
    GBotSelfConsistencyStatement params ψ family zeta
  completePartCommutationWitness :
    CommutingWithGCompleteStatement params ψ family gamma zeta
  incompletePartCommutationWitness :
    CommutingWithGIncompleteStatement params ψ family gamma zeta
  completedSelfConsistency :
    StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)
  completedCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)

/-- Output package for `lem:commute-g-half-sandwich`. -/
structure CommuteGHalfSandwichStatement (params : Parameters)
    (ψ : QuantumState)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) (k : ℕ) : Prop where
  repeatedCommutation :
    StateDependentDistanceRel ψ
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k)

/-- Output package for `lem:ld-sandwich-line-one-point`. -/
structure LdSandwichLineOnePointStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error)
    (k i : ℕ) : Prop where
  linePointComparison :
    ConsistencyRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Output package for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsistencyRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params (constructedPastedSubMeasurement params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Output package for `lem:over-all-outcomes`. -/
structure OverAllOutcomesStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  totalOutcomeExpansion :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (constructedPastedMeasurementTotal params family k)
      (allOutcomesExpansionFamily params strategy family k)
      (overAllOutcomesError params eps delta gamma zeta k)

/-- Output package for `lem:from-H-to-G`. -/
structure FromHToGStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      StateDependentDistanceRel strategy.state (uniformDistribution Unit)
        (fromHToGRecurrenceLeftFamily params strategy family k ℓ)
        (fromHToGRecurrenceRightFamily params strategy family k ℓ)
        (fromHToGRecurrenceError params gamma zeta k)
  bernoulliPolynomialRewrite :
    StateDependentDistanceRel strategy.state (uniformDistribution Unit)
      (allOutcomesExpansionFamily params strategy family k)
      (bernoulliTailFromFamily params family k)
      (fromHToGError params gamma zeta k)

/-- Output package for `lem:chernoff-bernoulli-matrix`. -/
structure ChernoffBernoulliMatrixStatement
    (ψ : QuantumState)
    (theta : Error) (k d : ℕ) (X : Operator) (kappa : Error) : Prop where
  matrixTailBound :
    CompletenessAtLeast ψ (bernoulliTailSubMeasurement k d X)
      (1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2))

/-- Output package for `cor:ld-pasting-N-completeness`. -/
structure LdPastingNCompletenessStatement (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (kappa nu : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  completenessBound :
    CompletenessAtLeast strategy.state
      (constructedPastedSubMeasurement params family k)
      (ldPastingCompletenessLowerBound params kappa nu k)


end

end MIPStarRE.LDT.Pasting
