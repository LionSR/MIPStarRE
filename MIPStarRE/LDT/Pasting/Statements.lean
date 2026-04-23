import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies

/-!
# Section 12 — Statements

This file packages the Section 12 pasting conclusions into reusable proposition-valued
structures. It records the displayed error formulas and the statement bundles for the
switcheroo, completed-family, half-sandwich, recurrence, Chernoff, and final pasting steps.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
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

/-- Displayed error term for the pairwise complete-part commutation bound used in
`cor:G-hat-facts`.

This is exactly the upstream `thm:com-main` error term. The proof of
`cor:G-hat-facts` only weakens the exponent to `1/16` after adding the three
incomplete-part commutation contributions. -/
noncomputable def pairwiseCompletePartCommutationError (params : Parameters)
    (gamma zeta : Error) : Error :=
  Commutativity.comMainError params gamma zeta

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

/-- Analytic conclusion for `thm:ld-pasting` once a witness `H` has been fixed.

The theorem `ldPasting` separately records that the chosen witness is the
canonical construction `constructedPastedMeasurement params family k`, so this
structure stores only the paper-facing quantitative conclusion. -/
structure LdPastingConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here continues to use the induction-section error term, while `ν`
  -- tracks the completeness loss below.
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta)

/-- Analytic conclusion for `lem:ld-pasting-sub-measurement` once a witness `H`
has been fixed.

The theorem `ldPastingSubMeas` separately records that the chosen witness is the
canonical construction `constructedPastedSubMeas params family k`, so this
structure stores only the quantitative properties proved about that witness. -/
structure LdPastingSubMeasConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  -- Naming note: this is not a `ν` field from the paper. The point-consistency
  -- bound here is the paper's intermediate `ν`, while the completeness field
  -- carries the missing-mass term needed for the final `σ` after completion.
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H)
      (MainInductionStep.ldPastingInInductionNu params k
        eps delta gamma zeta)
  completeness :
    CompletenessAtLeast strategy.state H.liftLeft
      (ldPastingCompletenessLowerBound params kappa
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) k)

/-- Output package for `lem:g-complete-self-consistency`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GCompleteSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  /--
  Stores self-consistency of the full slice family `family.meas` because the
  `cor:G-hat-facts` decomposition expands `\widehat G` self-consistency into the
  original slice-family term plus the incomplete part, not the postprocessed
  complete-part family.
  -/
  completePartSelfConsistency :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Output package for `cor:g-bot-self-consistency`. -/
structure GBotSelfConsistencyStatement (params : Parameters)
    [FieldModel params.q]
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
    (params : Parameters) [FieldModel params.q]
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
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop where
  pairwiseCompletePartCommutation :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          orderedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          reversedProductOpFamily
            ((family.meas q.1).toSubMeas)
            ((family.meas q.2).toSubMeas))
      (pairwiseCompletePartCommutationError params gamma zeta)
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
    [FieldModel params.q]
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
    [FieldModel params.q]
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
    [FieldModel params.q]
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
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) : Prop where
  linePointComparison :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)

/-- Output package for `lem:h-b-consistency`. -/
structure HBConsistencyStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ) : Prop where
  lineConsistency :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k)

/-- Output package for `lem:over-all-outcomes`. -/
structure OverAllOutcomesStatement (params : Parameters)
    [FieldModel params.q]
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

/-- Scalar expectation of one stage-`ℓ` tail contribution from
`lem:from-H-to-G`, for a fixed remaining type `τ_{≥ℓ}`. -/
noncomputable def fromHToGTailStageMass (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) : Error :=
  ev ψbi (((IdxOpFamily.liftLeft
    (fromHToGTailStageFamily params family prefixLen τtail)) ()).total)

/-- Scalar expectation of the full stage-`ℓ` quantity from `lem:from-H-to-G`.

This is the paper's sum over all remaining tail types
`τ_{≥ℓ} ∈ {0,1}^{k-ℓ}`.  The next stage `ℓ + 1` sums over the shorter tails
`τ_{>ℓ}`, so the recurrence field in `FromHToGStatement` compares these
adjacent stage masses directly rather than quantifying over a fixed full
`τ : GHatType k`. -/
noncomputable def fromHToGStageMass (params : Parameters)
    [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  ∑ τtail : GHatType (k - ℓ),
    fromHToGTailStageMass params ψbi family ℓ τtail

/-- Scalar expectation of the left-hand side of `lem:from-H-to-G`, i.e. the
uniform average of the eligible pasted-sandwich total mass. -/
noncomputable def fromHToGAllOutcomesMass (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass ψbi ((IdxSubMeas.liftLeft
    (allOutcomesExpansionFamily params strategy family k)) ())

/-- Scalar expectation of the Bernoulli-tail polynomial `F(G)` on the bipartite
state from `lem:from-H-to-G`. -/
noncomputable def fromHToGBernoulliTailMass (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  subMeasMass ψbi ((IdxSubMeas.liftLeft
    (bernoulliTailFromFamily params family k)) ())

/-- Output package for `lem:from-H-to-G`.

The paper's displayed statement is a scalar approximation of expectation values,
not a new `≈_δ` relation between submeasurements.  Accordingly, this bundle
stores the adjacent stage-mass inequalities and the final all-outcomes vs.
Bernoulli-tail comparison. -/
structure FromHToGStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params strategy ψbi family k ℓ -
          fromHToGStageMass params strategy ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k
  bernoulliPolynomialRewrite :
    |fromHToGAllOutcomesMass params strategy ψbi family k -
        fromHToGBernoulliTailMass params ψbi family k| ≤
      fromHToGError params gamma zeta k

/-- Output package for `lem:chernoff-bernoulli-matrix`. -/
structure ChernoffBernoulliMatrixStatement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1) : Prop where
  /-- Temporary field while the Bernoulli-tail contraction bound is still
  deferred rather than derived inside the matrix Chernoff proof. -/
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
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (kappa nu : Error) (k : ℕ) : Prop where
  largeEnough : 400 * params.m * params.d ≤ k
  completenessBound :
    CompletenessAtLeast strategy.state
      (constructedPastedSubMeas params family k).liftLeft
      (ldPastingCompletenessLowerBound params kappa nu k)

end MIPStarRE.LDT.Pasting
