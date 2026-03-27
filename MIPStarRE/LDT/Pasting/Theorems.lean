import MIPStarRE.LDT.Pasting.Statements

/-!
# Section 12 — Theorems

Theorem stubs for low-degree pasting.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeas
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
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
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    GCompleteSelfConsistencyStatement params ψbi family zeta := by
  sorry

/-- `cor:g-bot-self-consistency`. -/
theorem gBotSelfConsistency
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcomplete : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    GBotSelfConsistencyStatement params ψbi family zeta := by
  sorry

/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : SDDRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψbi family M zeta omega chi := by
  sorry

/-- `cor:commuting-with-G-complete`. -/
theorem commutingWithGComplete
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    CommutingWithGCompleteStatement params ψbi family gamma zeta := by
  sorry

/-- `cor:commuting-with-G-incomplete`. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψbi family gamma zeta) :
    CommutingWithGIncompleteStatement params ψbi family gamma zeta := by
  sorry

/-- `cor:G-hat-facts`. -/
theorem gHatFacts
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hselfComplete : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params ψbi family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params ψbi family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params ψbi family gamma zeta) :
    GHatFactsStatement params ψbi family gamma zeta := by
  sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i := by
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
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
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  sorry

/-- `lem:from-H-to-G`. -/
lemma fromHToG
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params ψbi family gamma zeta k) :
    FromHToGStatement params strategy family gamma zeta k := by
  sorry

/-- `lem:chernoff-bernoulli-matrix`. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : 0 ≤ 1 - X)
    (hcomplete : CompletenessAtLeast ψ (operatorAsSubMeas X) (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa := by
  sorry

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
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
