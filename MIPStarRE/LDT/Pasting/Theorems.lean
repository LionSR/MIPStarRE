import MIPStarRE.LDT.Pasting.Statements

/-!
# Section 12 — Theorems

Theorem stubs for low-degree pasting.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints

noncomputable section

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) d,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeasurement
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeasurement (Polynomial params.next) d,
      LdPastingSubMeasurementConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `prop:ld-dnoteq`. -/
theorem ldDnoteq
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  sorry

/-- `lem:looks-easy-but-took-me-a-while`. -/
lemma looksEasyButTookMeAWhile
    (lambda : Error) (d : ℕ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda * (1 - lambda ^ d)
      ≤ 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) (1 / ((d + 1 : ℕ) : Error)) := by
  sorry

/-- `lem:g-complete-self-consistency`. -/
lemma gCompleteSelfConsistency
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (zeta : Error)
    (hself : family.StronglySelfConsistent ψ zeta) :
    GCompleteSelfConsistencyStatement params ψ family zeta := by
  sorry

/-- `cor:g-bot-self-consistency`. -/
theorem gBotSelfConsistency
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (zeta : Error)
    (hcomplete : GCompleteSelfConsistencyStatement params ψ family zeta) :
    GBotSelfConsistencyStatement params ψ family zeta := by
  sorry

/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*}
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (M : IndexedProjectiveSubMeasurement (Fq params) Outcome d)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψ family zeta)
    (hselfM : StateDependentDistanceRel ψ
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : StateDependentDistanceRel ψ
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψ family M zeta omega chi := by
  sorry

/-- `cor:commuting-with-G-complete`. -/
theorem commutingWithGComplete
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (family : IndexedPolynomialFamily params d)
    (gamma zeta : Error)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  sorry

/-- `cor:commuting-with-G-incomplete`. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψ family gamma zeta) :
    CommutingWithGIncompleteStatement params ψ family gamma zeta := by
  sorry

/-- `cor:G-hat-facts`. -/
theorem gHatFacts
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (gamma zeta : Error)
    (hselfComplete : GCompleteSelfConsistencyStatement params ψ family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params ψ family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params ψ family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params ψ family gamma zeta) :
    GHatFactsStatement params ψ family gamma zeta := by
  sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    (ψ : QuantumState d)
    (family : IndexedPolynomialFamily params d)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hfacts : GHatFactsStatement params ψ family gamma zeta) :
    CommuteGHalfSandwichStatement params ψ family gamma zeta k := by
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i := by
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family eps delta gamma zeta k := by
  sorry

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  sorry

/-- `lem:from-H-to-G`. -/
lemma fromHToG
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params strategy.state family gamma zeta k) :
    FromHToGStatement params strategy family gamma zeta k := by
  sorry

/-- `lem:chernoff-bernoulli-matrix`. -/
lemma chernoffBernoulliMatrix {d : ℕ}
    (ψ : QuantumState d)
    (theta : Error) (k degree : ℕ) (X : Operator d) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : PositiveSemidefinite X)
    (hXleOne : PositiveSemidefinite (operatorComplement X))
    (hcomplete : CompletenessAtLeast ψ (operatorAsSubMeasurement X) (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa := by
  sorry

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    (strategy : SymmetricStrategy params.next d)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params d)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  sorry

end

end MIPStarRE.LDT.Pasting
