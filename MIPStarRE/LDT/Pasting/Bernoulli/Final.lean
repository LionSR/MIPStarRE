import MIPStarRE.LDT.Pasting.Bernoulli.Recurrence

/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting wrappers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  -- Chain the three completeness-chain lemmas (§9.4 of the paper)
  have _hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound k
  constructor -- LdPastingNCompletenessStatement
  · exact hk -- largeEnough: 400 * m * d ≤ k
  · -- completenessBound
    constructor -- CompletenessAtLeast
    /- Paper: `cor:ld-pasting-N-completeness` (ld-pasting.tex lines 1798–1849).
    Chains: overAllOutcomes (ν₇) + fromHToG (ν₈) → SDDRel H vs F(G);
    chernoffBernoulliMatrix (θ = 1/(200m)): ev ψ F(G) ≥ 1-κ/(1-θ)-exp(...);
    SDDRel → mass transfer: ev ψ H ≥ ev ψ F(G) - √(ν₇+ν₈);
    parameter match: κ/(1-θ) ≤ κ(1+1/(100m)),
    exp(-θ²k/2) = exp(-k/(80000m²)).
    Requires: SDDRel → completeness transfer for Unit-indexed families. -/
    sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedSubMeas params family k, ?_⟩
  have hconsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  exact
    { largeEnough := hk
      constructedSubMeas := rfl
      pointConsistency := hconsistency
      completeness := hcompleteness.completenessBound }

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedMeasurement params family k, ?_⟩
  have hsubmeasConsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hconsistency :=
    hAConsistency_completed params strategy eps delta gamma kappa zeta
      strategy.isNormalized family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { largeEnough := hk
      constructedMeasurement := rfl
      pointConsistency := hconsistency }

end MIPStarRE.LDT.Pasting
