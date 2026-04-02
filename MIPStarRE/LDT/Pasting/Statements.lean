import MIPStarRE.LDT.Pasting.Sandwich

/-!
# Section 12 — Statements

Output structures for the low-degree pasting lemmas.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedMeasurement :
    H = constructedPastedMeasurement params family k
  pointConsistency :
    ConsWithPolyEval params.next strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.toSubMeas.liftLeft
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)

/-- Output package for `lem:ld-pasting-sub-measurement`. -/
structure LdPastingSubMeasConclusion (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  constructedSubMeas :
    H = constructedPastedSubMeas params family k
  pointConsistency :
    ConsWithPolyEval params.next strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.liftLeft
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)
  completeness :
    CompletenessAtLeast strategy.state H.liftLeft
      (ldPastingCompletenessLowerBound params kappa
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) k)

/-- Output package for `lem:g-complete-self-consistency`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  completePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (completePartLeftFamily params family)
      (completePartRightFamily params family)
      zeta

/-- Output package for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  completePartWitness :
    GCompleteSelfConsistencyStatement params ψbi family zeta
  incompletePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (incompletePartLeftFamily params family)
      (incompletePartRightFamily params family)
      zeta

/-- Output package for `lem:commutativity-switcheroo`. -/
structure CommutativitySwitcherooStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error) : Prop where
  aggregateCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family M)
      (switcherooAggregateRight params family M)
      (commutativitySwitcherooError zeta omega chi)

/-- Output package for `cor:commuting-with-G-complete`. -/
structure CommutingWithGCompleteStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pointWithCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutingWithGCompleteError params gamma zeta)
  completePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      (commutingWithGCompleteError params gamma zeta)

/-- Output package for `cor:commuting-with-G-incomplete`. -/
structure CommutingWithGIncompleteStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  completePartWitness :
    CommutingWithGCompleteStatement params ψbi family gamma zeta
  pointWithIncompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartPointProductLeft params family)
      (incompletePartPointProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)
  incompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (incompletePartTotalProductLeft params family)
      (incompletePartTotalProductRight params family)
      (commutingWithGIncompleteError params gamma zeta)

/-- Output package for `cor:G-hat-facts`. -/
structure GHatFactsStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  completePartSelfConsistencyWitness :
    GCompleteSelfConsistencyStatement params ψbi family zeta
  incompletePartSelfConsistencyWitness :
    GBotSelfConsistencyStatement params ψbi family zeta
  completePartCommutationWitness :
    CommutingWithGCompleteStatement params ψbi family gamma zeta
  incompletePartCommutationWitness :
    CommutingWithGIncompleteStatement params ψbi family gamma zeta
  completedSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)
  completedCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)

/-- Output package for `lem:commute-g-half-sandwich`. -/
structure CommuteGHalfSandwichStatement (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  repeatedCommutation :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k)

/-- Output package for `lem:ld-sandwich-line-one-point`. -/
structure LdSandwichLineOnePointStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) : Prop where
  linePointComparison :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (IdxSubMeas.liftLeft
        (ldSandwichLineOnePointLeftFamily params strategy family k i))
      (IdxSubMeas.liftLeft
        (ldSandwichLineOnePointRightFamily params strategy family k i))
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Output package for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (IdxSubMeas.liftLeft
        (hRestrictionToVerticalLine params
          (constructedPastedSubMeas params family k)))
      (IdxSubMeas.liftLeft
        (verticalLineMeasurementFamily params strategy))
      (hBConsistencyError params eps delta gamma zeta k)

/-- Output package for `lem:over-all-outcomes`. -/
structure OverAllOutcomesStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  totalOutcomeExpansion :
    SDDRel strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft
        (constructedPastedMeasurementTotal params family k))
      (IdxSubMeas.liftLeft
        (allOutcomesExpansionFamily params strategy family k))
      (overAllOutcomesError params eps delta gamma zeta k)

/-- Output package for `lem:from-H-to-G`. -/
structure FromHToGStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      SDDOpRel strategy.state (uniformDistribution Unit)
        (IdxOpFamily.liftLeft
          (fromHToGRecurrenceLeftFamily params strategy family k ℓ))
        (IdxOpFamily.liftLeft
          (fromHToGRecurrenceRightFamily params strategy family k ℓ))
        (fromHToGRecurrenceError params gamma zeta k)
  bernoulliPolynomialRewrite :
    SDDRel strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft
        (allOutcomesExpansionFamily params strategy family k))
      (IdxSubMeas.liftLeft
        (bernoulliTailFromFamily params family k))
      (fromHToGError params gamma zeta k)

/-- Positivity of the Bernoulli tail operator for a PSD contraction. -/
private theorem bernoulliTailOperator_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1) :
    0 ≤ bernoulliTailOperator k degree X := by
  unfold bernoulliTailOperator
  refine Finset.sum_nonneg fun r _ => ?_
  simpa using binomialOperatorTerm_nonneg (G := X) k r hXpsd hXleOne

/-- Output package for `lem:chernoff-bernoulli-matrix`. -/
structure ChernoffBernoulliMatrixStatement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1) : Prop where
  /-- Temporary field while the Bernoulli-tail contraction bound is still supplied
  separately by the theorem stub rather than proved from `hXpsd` and `hXleOne`. -/
  tail_le_one : bernoulliTailOperator k degree X ≤ 1
  matrixTailBound :
    CompletenessAtLeast ψ
      ({ outcome := fun _ => bernoulliTailOperator k degree X
         total := bernoulliTailOperator k degree X
         outcome_pos := by
           intro _
           exact bernoulliTailOperator_nonneg k degree X hXpsd hXleOne
         sum_eq_total := by
           simp
         total_le_one := by
           exact tail_le_one } : SubMeas Unit ι)
      (1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2))

/-- Output package for `cor:ld-pasting-N-completeness`. -/
structure LdPastingNCompletenessStatement (params : Parameters)
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (kappa nu : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  completenessBound :
    CompletenessAtLeast strategy.state
      (constructedPastedSubMeas params family k).liftLeft
      (ldPastingCompletenessLowerBound params kappa nu k)

end MIPStarRE.LDT.Pasting
