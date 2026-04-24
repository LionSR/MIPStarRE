import MIPStarRE.LDT.Pasting.Bernoulli.Recurrence
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich
import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency
import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes

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

/-- Arithmetic helper for `cor:ld-pasting-N-completeness`: absorb the
`overAllOutcomes` and `fromHToG` scalar losses into
`ldPastingInInductionNu`.

The proof uses that the `fromHToGError` tail sum is a sub-sum of the full
`overAllOutcomesError` sum, that `1 ≤ k` implies `k ≤ k^2`, and the slack
`46 + 46 ≤ 100`. -/
private lemma overAllOutcomesError_add_fromHToGError_le_ldPastingNu
    (params : Parameters)
    [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    overAllOutcomesError params eps delta gamma zeta k +
        fromHToGError params gamma zeta k ≤
      MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let kE : Error := (k : Error)
  let mE : Error := (params.m : Error)
  let ratio : Error := (params.d : Error) / (params.q : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let dqTerm : Error := Real.rpow ratio (1 / (32 : Error))
  let fullSum : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + dqTerm
  let tailSum : Error := gammaTerm + zetaTerm + dqTerm
  -- This is the `1 ≤ k` input that the downstream `nlinarith` call uses to
  -- trade the linear `k` term for `k^2`.
  have hkE_one : (1 : Error) ≤ kE := by
    dsimp [kE]
    exact_mod_cast hk_pos
  have hkE_nonneg : 0 ≤ kE := by positivity
  have hmE_nonneg : 0 ≤ mE := by positivity
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdqTerm_nonneg : 0 ≤ dqTerm := by
    dsimp [dqTerm]
    exact Real.rpow_nonneg hratio_nonneg _
  have htail_le_full : tailSum ≤ fullSum := by
    dsimp [tailSum, fullSum]
    linarith
  have hfull_nonneg : 0 ≤ fullSum := by
    dsimp [fullSum]
    linarith
  calc
    overAllOutcomesError params eps delta gamma zeta k +
        fromHToGError params gamma zeta k
      = 46 * (kE ^ (2 : ℕ)) * mE * fullSum + 46 * kE * mE * tailSum := by
          simp [overAllOutcomesError, fromHToGError, kE, mE, fullSum, tailSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]
    _ ≤ 46 * (kE ^ (2 : ℕ)) * mE * fullSum + 46 * kE * mE * fullSum := by
          gcongr
    _ ≤ 46 * (kE ^ (2 : ℕ)) * mE * fullSum + 46 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          have hk_sq : kE ≤ kE ^ (2 : ℕ) := by
            nlinarith
          have hscale_nonneg : 0 ≤ 46 * mE * fullSum := by
            positivity
          nlinarith
    _ ≤ 100 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          have hterm_nonneg : 0 ≤ (kE ^ (2 : ℕ)) * mE * fullSum := by
            positivity
          nlinarith
    _ = MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, kE, mE, fullSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]

/-- `cor:ld-pasting-N-completeness` once the Bernoulli-tail lower bound is
supplied explicitly.

This packages the downstream scalar algebra after `lem:over-all-outcomes` and
`lem:from-H-to-G`. The hypothesis `htail` is exactly the `θ = 1 / (200m)`
specialization of `lem:chernoff-bernoulli-matrix` for the averaged complete
operator `G = \mathbb E_x \sum_g G^x_g`; issue #597 tracks deriving that lower
bound internally. -/
theorem ldPastingNCompleteness_of_tailLowerBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k)
    (htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  have hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le family hcons hself hbound k
  have heps_nonneg : 0 ≤ eps :=
    eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta :=
    delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg : 0 ≤ gamma :=
    gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
  have hG : ∀ x, G x = (family.meas x).toSubMeas := by
    intro x
    rfl
  have hselfComplete :=
    gCompleteSelfConsistency params strategy.state family zeta
      strategy.permInvState hself
  have hselfIncomplete :=
    gBotSelfConsistency params strategy.state family zeta
      strategy.permInvState hselfComplete
  have hcomMain :=
    Commutativity.comMain params strategy eps delta gamma zeta
      strategy.isNormalized hgood family G hG hcons hself hbound
  have hcommComplete :=
    commutingWithGComplete params strategy family G gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
  have hcommIncomplete :=
    commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
  have hfacts := gHatFacts params strategy.state family gamma zeta
    hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
    hselfComplete hselfIncomplete hcommComplete hcommIncomplete
  have hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy.state family gamma zeta
      j hj hzeta_le hfacts
  have hFrom := fromHToG params strategy strategy.state family gamma zeta hfacts hhalf k
  have happrox_le :
      overAllOutcomesError params eps delta gamma zeta k +
          fromHToGError params gamma zeta k ≤ ν := by
    simpa [ν] using
      overAllOutcomesError_add_fromHToGError_le_ldPastingNu params
        eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  constructor
  · exact hk
  · constructor
    have hOAO_mass :
        overAllOutcomesPastedMass params strategy family k ≥
          overAllOutcomesExpansionMass params strategy family k -
            overAllOutcomesError params eps delta gamma zeta k := by
      have habs := abs_le.mp hOAO.totalOutcomeExpansion
      linarith
    have hFrom_mass :
        fromHToGAllOutcomesMass params strategy strategy.state family k ≥
          fromHToGBernoulliTailMass params strategy.state family k -
            fromHToGError params gamma zeta k := by
      have habs := abs_le.mp hFrom.bernoulliPolynomialRewrite
      linarith
    have hmass :
        overAllOutcomesPastedMass params strategy family k ≥
          1 - kappa * (1 + 1 / (100 * (params.m : Error))) - ν -
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      have hOAO_mass' :
          overAllOutcomesPastedMass params strategy family k ≥
            fromHToGAllOutcomesMass params strategy strategy.state family k -
              overAllOutcomesError params eps delta gamma zeta k := by
        simpa [overAllOutcomesExpansionMass, fromHToGAllOutcomesMass] using hOAO_mass
      linarith
    simpa [ν, ldPastingCompletenessLowerBound, overAllOutcomesPastedMass] using hmass

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
  have htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k := by
    /- Paper: this is the downstream Bernoulli-tail lower bound obtained by
    specializing `lem:chernoff-bernoulli-matrix` to `θ = 1/(200m)` and the
    averaged complete operator `G`.  The surrounding completeness chain is now
    reduced to this single scalar input; issue #597 tracks the missing spectral /
    Chernoff infrastructure needed to derive it inside Lean. -/
    sorry
  exact ldPastingNCompleteness_of_tailLowerBound params strategy
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound k hk_pos hk htail

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
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      H = constructedPastedSubMeas params family k ∧
        LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedSubMeas params family k, rfl, ?_⟩
  have hconsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  exact
    { largeEnough := hk
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
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      H = constructedPastedMeasurement params family k ∧
        LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedMeasurement params family k, rfl, ?_⟩
  have hsubmeasConsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  have hconsistency :=
    hAConsistency_completed params strategy eps delta gamma kappa zeta
      family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { largeEnough := hk
      pointConsistency := hconsistency }

end MIPStarRE.LDT.Pasting
