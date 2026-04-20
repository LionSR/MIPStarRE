import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

/-!
# Section 12 pasting: Bernoulli recurrence bridge

Recurrence-weight wrappers, the `fromHToG` bridge, and the Chernoff wrapper.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma outcomesByType_prependTypeBit_iff
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (b : Bool) (τ : GHatType k)
    (gs : GHatTupleOutcome params (k + 1)) :
    gs ∈ outcomesByType (prependTypeBit b τ) ↔
      (gs 0).isSome = b ∧ gHatTupleOutcomeTail gs ∈ outcomesByType τ := by
  constructor
  · intro h
    constructor
    · simpa [outcomesByType, prependTypeBit] using h 0
    · intro i
      simpa [outcomesByType, gHatTupleOutcomeTail, prependTypeBit] using h i.succ
  · rintro ⟨hhead, htail⟩ i
    cases i using Fin.cases with
    | zero => simpa [outcomesByType, prependTypeBit] using hhead
    | succ j => simpa [outcomesByType, gHatTupleOutcomeTail, prependTypeBit] using htail j

private lemma fromHToGRecurrenceRightFamily_eq_leftFamily_succ
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    fromHToGRecurrenceRightFamily params strategy family k ℓ τ =
      fromHToGRecurrenceLeftFamily params strategy family k (ℓ + 1) τ := by
  rfl

private lemma gHatTypeSuffix_zero
    {k : ℕ} (τ : GHatType k) :
    gHatTypeSuffix 0 τ = τ := by
  funext i
  simp [gHatTypeSuffix]

private lemma suffixBernoulliWeightOperator_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    suffixBernoulliWeightOperator params family k 0 τ =
      fromHToGRecurrenceWeight params family 0 τ := by
  simpa [suffixBernoulliWeightOperator, gHatTypeSuffix_zero] using
    (rfl : suffixBernoulliWeightOperator params family k 0 τ =
      fromHToGRecurrenceWeight params family 0 (gHatTypeSuffix 0 τ))

private lemma fromHToGRecurrenceWeight_zero_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family 0 τtail =
      if params.d + 1 ≤ gHatTypeWeight τtail then (1 : MIPStarRE.Quantum.Op ι) else 0 := by
  simp [fromHToGRecurrenceWeight, truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

private lemma suffixBernoulliWeightOperator_zero_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    suffixBernoulliWeightOperator params family k 0 τ =
      if params.d + 1 ≤ gHatTypeWeight τ then (1 : MIPStarRE.Quantum.Op ι) else 0 := by
  rw [suffixBernoulliWeightOperator_zero]
  simpa using fromHToGRecurrenceWeight_zero_eq_indicator params family τ

private lemma fromHToGRecurrenceWeight_zero_eq_one_of_eligible
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {tailLen : ℕ} (τtail : GHatType tailLen)
    (hτ : params.d + 1 ≤ gHatTypeWeight τtail) :
    fromHToGRecurrenceWeight params family 0 τtail = (1 : MIPStarRE.Quantum.Op ι) := by
  rw [fromHToGRecurrenceWeight_zero_eq_indicator]
  simp [hτ]

private lemma fromHToGRecurrenceWeight_zero_eq_zero_of_not_eligible
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {tailLen : ℕ} (τtail : GHatType tailLen)
    (hτ : ¬ params.d + 1 ≤ gHatTypeWeight τtail) :
    fromHToGRecurrenceWeight params family 0 τtail = 0 := by
  rw [fromHToGRecurrenceWeight_zero_eq_indicator]
  simp [hτ]

private lemma suffixBernoulliWeightOperator_zero_eq_one_of_eligible
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : params.d + 1 ≤ gHatTypeWeight τ) :
    suffixBernoulliWeightOperator params family k 0 τ = (1 : MIPStarRE.Quantum.Op ι) := by
  rw [suffixBernoulliWeightOperator_zero_eq_indicator]
  simp [hτ]

private lemma suffixBernoulliWeightOperator_zero_eq_zero_of_not_eligible
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : ¬ params.d + 1 ≤ gHatTypeWeight τ) :
    suffixBernoulliWeightOperator params family k 0 τ = 0 := by
  rw [suffixBernoulliWeightOperator_zero_eq_indicator]
  simp [hτ]

private lemma fromHToGRecurrenceLeftFamily_zero_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).outcome () =
      if params.d + 1 ≤ gHatTypeWeight τ then
        (fromHToGRecurrenceSuffixHSubMeas params family k 0 τ).total
      else 0 := by
  simp [fromHToGRecurrenceLeftFamily, fromHToGRecurrenceSuffixFamily,
    suffixBernoulliWeightOperator_zero_eq_indicator]

private lemma fromHToGRecurrenceLeftFamily_zero_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).total =
      if params.d + 1 ≤ gHatTypeWeight τ then
        (fromHToGRecurrenceSuffixHSubMeas params family k 0 τ).total
      else 0 := by
  simp [fromHToGRecurrenceLeftFamily, fromHToGRecurrenceSuffixFamily,
    suffixBernoulliWeightOperator_zero_eq_indicator]

private lemma fromHToGRecurrenceLeftFamily_zero_outcome_eq_suffix_of_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : params.d + 1 ≤ gHatTypeWeight τ) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).outcome () =
      (fromHToGRecurrenceSuffixHSubMeas params family k 0 τ).total := by
  rw [fromHToGRecurrenceLeftFamily_zero_outcome]
  simp [hτ]

private lemma fromHToGRecurrenceLeftFamily_zero_total_eq_suffix_of_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : params.d + 1 ≤ gHatTypeWeight τ) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).total =
      (fromHToGRecurrenceSuffixHSubMeas params family k 0 τ).total := by
  rw [fromHToGRecurrenceLeftFamily_zero_total]
  simp [hτ]

private lemma fromHToGRecurrenceLeftFamily_zero_outcome_eq_zero_of_not_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : ¬ params.d + 1 ≤ gHatTypeWeight τ) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).outcome () = 0 := by
  rw [fromHToGRecurrenceLeftFamily_zero_outcome]
  simp [hτ]

private lemma fromHToGRecurrenceLeftFamily_zero_total_eq_zero_of_not_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k)
    (hτ : ¬ params.d + 1 ≤ gHatTypeWeight τ) :
    ((fromHToGRecurrenceLeftFamily params strategy family k 0 τ) ()).total = 0 := by
  rw [fromHToGRecurrenceLeftFamily_zero_total]
  simp [hτ]

private lemma fromHToGRecurrenceLeftFamily_apply_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceLeftFamily params strategy family k ℓ τ) ()).outcome () =
      (fromHToGRecurrenceSuffixHSubMeas params family k ℓ τ).total *
        suffixBernoulliWeightOperator params family k ℓ τ := by
  rfl

private lemma fromHToGRecurrenceLeftFamily_apply_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceLeftFamily params strategy family k ℓ τ) ()).total =
      (fromHToGRecurrenceSuffixHSubMeas params family k ℓ τ).total *
        suffixBernoulliWeightOperator params family k ℓ τ := by
  rfl

private lemma fromHToGRecurrenceRightFamily_apply_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceRightFamily params strategy family k ℓ τ) ()).outcome () =
      (fromHToGRecurrenceSuffixHSubMeas params family k (ℓ + 1) τ).total *
        suffixBernoulliWeightOperator params family k (ℓ + 1) τ := by
  rfl

private lemma fromHToGRecurrenceRightFamily_apply_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    ((fromHToGRecurrenceRightFamily params strategy family k ℓ τ) ()).total =
      (fromHToGRecurrenceSuffixHSubMeas params family k (ℓ + 1) τ).total *
        suffixBernoulliWeightOperator params family k (ℓ + 1) τ := by
  rfl

private lemma allOutcomesExpansionFamily_apply
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    allOutcomesExpansionFamily params strategy family k () =
      postprocess (averagedEligibleSandwichSubMeas params family k) (fun _ => ()) := by
  rfl

private lemma bernoulliTailFromFamily_apply
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    bernoulliTailFromFamily params family k () =
      let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
      ({ outcome := fun _ => Y
         total := Y
         outcome_pos := by
           intro _
           let G := (IdxPolyFamily.averagedSubMeas family).total
           have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
           have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
           simpa [G] using bernoulliTailOperator_nonneg k params.d G hG hGle
         sum_eq_total := by simp
         total_le_one := by
           let G := (IdxPolyFamily.averagedSubMeas family).total
           have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
           have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
           simpa [Y, G] using bernoulliTailOperator_le_one k params.d G hG hGle } : SubMeas Unit ι) := by
  rfl

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
private lemma fromHToGRecurrenceWeight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail)ᴴ =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1

/-- One-step recurrence for `fromHToGRecurrenceWeight`: adding a new prefix bit
splits the weight into the `τ_ℓ = 1` and `τ_ℓ = 0` branches, each multiplied by
the appropriate Bernoulli factor `G` or `I - G`. -/
theorem fromHToGRecurrenceWeight_succ
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family (prefixLen + 1) τtail =
      fromHToGRecurrenceWeight params family prefixLen (prependTypeBit true τtail) *
          family.averagedSubMeas.total +
        fromHToGRecurrenceWeight params family prefixLen (prependTypeBit false τtail) *
          (1 - family.averagedSubMeas.total) :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.2

private lemma fromHToG_gHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    GHatFactsStatement params strategy.state family gamma zeta := by
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
  have hG : ∀ x, G x = (family.meas x).toSubMeas := by
    intro x
    rfl
  have hselfComplete :=
    gCompleteSelfConsistency params strategy.state family zeta hself
  have hselfIncomplete :=
    gBotSelfConsistency params strategy.state family zeta hselfComplete
  have hcomMain :=
    Commutativity.comMain params strategy eps delta gamma zeta
      strategy.isNormalized hgood family G hG hcons hself hbound
  have hcommComplete :=
    commutingWithGComplete params strategy family G gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
  have hcommIncomplete :=
    commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
  exact gHatFacts params strategy.state family gamma zeta
    hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
    hselfComplete hselfIncomplete hcommComplete hcommIncomplete

/-- `lem:from-H-to-G`.

The bipartite state in the goal `FromHToGStatement` and in the recurrence
hypothesis `hhalf` is taken to be `strategy.state` directly, matching the
paper's identification of `\ket{\psi_{\mathrm{bi}}}` with the symmetric
strategy's bipartite state (both are typed `QuantumState (ι × ι)` since
`SymStrat.state` is itself bipartite — see
`MIPStarRE/LDT/Test/Strategy.lean:75`). This keeps the Lean signature in
lockstep with the blueprint statement (`blueprint/src/chapter/ch09_pasting.tex:887–903`)
and lets `hself`/`hcons`/`hbound`, which are phrased over `strategy.state`,
be reused without an equality bridge. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params strategy.state family gamma zeta k) :
    FromHToGStatement params strategy strategy.state family gamma zeta k := by
  constructor -- FromHToGStatement
  · -- recurrenceStep: per-step Bernoulli-tail commutation
    intro ℓ hℓ τ
    constructor -- SDDOpRel
    /- Inductive step ℓ of the Bernoulli-tail recurrence (ld-pasting.tex
    lines 1346–1666). Three commutation sub-steps per induction step:
    (a) move rightmost Ĝ^{x_ℓ} to 2nd tensor factor (√(2ζ)),
    (b) commute leftmost Ĝ past remaining factors (√ν₄),
    (c) move leftmost to 2nd tensor factor (√(2ζ)).
    Per-step error: 2√(2ζ) + 2√ν₄ = fromHToGRecurrenceError. -/
    /- Outstanding gap (tracked in issue #395):
    `fromHToGRecurrenceLeftFamily` / `fromHToGRecurrenceRightFamily`
    (`Sandwich.lean:930-955`) are currently in collapsed form
    `allOutcomesExpansion.total * suffixBernoulliWeightOperator k ℓ τ` and
    `bernoulliTailFromFamily.total * suffixBernoulliWeightOperator k ℓ τ`;
    the paper's recurrence step relates the *intermediate* family
    `Ĥ^{x_≥ℓ} ⊗ S_{τ_≥ℓ}` to `Ĥ^{x_>ℓ} ⊗ S_{τ_>ℓ}` (eq:i-think-this-is-what-
    i'm-supposed-to-prove-2). To finish this case the families need to be
    refactored to expose the per-step Ĥ-on-suffix structure (a new
    `intermediateHSuffixFamily k ℓ` definition), then the three commutation
    sub-steps above can be discharged using `hhalf` (for √ν₄) and
    `cor:G-hat-facts` (for √(2ζ)), each composed via `sddOpRel_mono` /
    `sddOpRel_trans`, reusing `hself`/`hcons`/`hbound` directly against
    `strategy.state`. -/
    sorry
  · -- bernoulliPolynomialRewrite: aggregate k recurrence steps
    constructor -- SDDRel
    /- Aggregate k recurrence steps to show allOutcomesExpansion ≈ F(G).
    Total error ≤ k × per-step error ≤ fromHToGError. The chained
    `sddOpRel_trans` argument depends on the refactored families above
    so that `RightFamily ℓ` definitionally equals `LeftFamily (ℓ+1)`,
    enabling the telescoping in ld-pasting.tex lines 1354–1376. -/
    sorry

/-- `lem:chernoff-bernoulli-matrix`.

The core scalar inequality `ev ψ (F(X)) ≥ 1 - κ/(1-θ) - exp(-θ²k/2)` (paper
`ld-pasting.tex` lines 1670–1797) is taken as the explicit hypothesis
`hMatrixChernoff` rather than derived internally: its proof requires matrix
Chernoff infrastructure (additive Chernoff for sums of iid Bernoullis and
`Matrix.IsHermitian.spectral_theorem` composed with `ev`/`normalizedTrace`
expansion) that is not yet available in Mathlib. Once that infrastructure
lands, `hMatrixChernoff` can be discharged and removed from the signature. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := by
           intro _
           exact hXpsd
         sum_eq_total := by
           simp
         total_le_one := by
           exact hXleOne } : SubMeas Unit ι)
      (1 - kappa))
    (hMatrixChernoff :
      1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
        ev ψ (bernoulliTailOperator k degree X)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact hMatrixChernoff

end MIPStarRE.LDT.Pasting
