import MIPStarRE.LDT.Pasting.Bernoulli.Recurrence
import MIPStarRE.LDT.Pasting.Bernoulli.ScalarBounds
import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero
import MIPStarRE.LDT.Pasting.Defs.Tuples
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies
import MIPStarRE.LDT.Pasting.CommutingWithG.Complete
import MIPStarRE.LDT.Pasting.CommutingWithG.Incomplete
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich
import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency
import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes

/-!
# Section 12 pasting: final pasting theorems

Final completeness and pasting theorems.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On a swap-invariant bipartite state, left and right placements of the same
operator have the same expectation. -/
private lemma ev_leftTensor_eq_rightTensor_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (A : MIPStarRE.Quantum.Op ι) :
    ev ψ (leftTensor (ι₂ := ι) A) = ev ψ (rightTensor (ι₁ := ι) A) := by
  calc
    ev ψ (leftTensor (ι₂ := ι) A) = ev ψ (opTensor A (1 : MIPStarRE.Quantum.Op ι)) := by
      simp [leftTensor, opTensor]
    _ = ev ψ (opTensor (1 : MIPStarRE.Quantum.Op ι) A) := by
      exact ev_opTensor_swap_of_density_fixed ψ hfix A (1 : MIPStarRE.Quantum.Op ι)
    _ = ev ψ (rightTensor (ι₁ := ι) A) := by
      simp [rightTensor, opTensor]

/-- Arithmetic helper for `cor:ld-pasting-N-completeness`: absorb the
`overAllOutcomes` and `fromHToG` scalar losses into
`ldPastingInInductionNu`.

The proof uses that the corrected `fromHToGError` tail sum is a sub-sum of the
full `overAllOutcomesError` sum and the slack `46 + 46 ≤ 100`. -/
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
      = 46 * (kE ^ (2 : ℕ)) * mE * fullSum +
          46 * (kE ^ (2 : ℕ)) * mE * tailSum := by
          simp [overAllOutcomesError, fromHToGError, kE, mE, fullSum, tailSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]
    _ ≤ 46 * (kE ^ (2 : ℕ)) * mE * fullSum +
          46 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          gcongr
    _ ≤ 100 * (kE ^ (2 : ℕ)) * mE * fullSum := by
          have hterm_nonneg : 0 ≤ (kE ^ (2 : ℕ)) * mE * fullSum := by
            positivity
          nlinarith
    _ = MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, kE, mE, fullSum,
            epsTerm, deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio]

/-- Positivity of the paper's choice `θ = 1/(200m)`. -/
private lemma ldPasting_theta_pos (params : Parameters) :
    (0 : Error) < 1 / (200 * (params.m : Error)) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  positivity

/-- The paper's choice `θ = 1/(200m)` is strictly below `1`. -/
private lemma ldPasting_theta_lt_one (params : Parameters) :
    (1 / (200 * (params.m : Error)) : Error) < 1 := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
  field_simp [hden_pos.ne']
  nlinarith

/-- Paper arithmetic: for `θ = 1/(200m)`,
`1/(1-θ) ≤ 1 + 1/(100m)`. -/
private lemma ldPasting_theta_inv_le (params : Parameters) :
    (1 / (1 - 1 / (200 * (params.m : Error))) : Error) ≤
      1 + 1 / (100 * (params.m : Error)) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hden200_pos : 0 < 200 * (params.m : Error) := by positivity
  have hden100_pos : 0 < 100 * (params.m : Error) := by positivity
  have hdenMinus_pos : 0 < 200 * (params.m : Error) - 1 := by nlinarith
  have hdenMinus_ge : 100 * (params.m : Error) ≤ 200 * (params.m : Error) - 1 := by
    nlinarith
  calc
    (1 / (1 - 1 / (200 * (params.m : Error))) : Error)
        = (200 * (params.m : Error)) / (200 * (params.m : Error) - 1) := by
            field_simp [hden200_pos.ne', hdenMinus_pos.ne']
    _ = 1 + 1 / (200 * (params.m : Error) - 1) := by
            field_simp [hdenMinus_pos.ne']
            nlinarith
    _ ≤ 1 + 1 / (100 * (params.m : Error)) := by
            gcongr

/-- Paper arithmetic: the matrix-Chernoff exponential at `θ = 1/(200m)` is the
stated `exp(-k/(80000m²))` term. -/
private lemma ldPasting_chernoff_exponent_eq (params : Parameters) (k : ℕ) :
    -(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2 =
      -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
  have hden2_pos : (0 : Error) < 80000 * ((params.m : Error) ^ (2 : ℕ)) := by positivity
  field_simp [hden_pos.ne', hden2_pos.ne']
  ring

/-- The public size assumption `k ≥ 400md` implies the matrix-Chernoff size
condition `k ≥ 2d/θ` at `θ = 1/(200m)`. -/
private lemma ldPasting_chernoff_size (params : Parameters) (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    (2 * (params.d : Error)) / (1 / (200 * (params.m : Error))) ≤ (k : Error) := by
  have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hden_pos : (0 : Error) < 200 * (params.m : Error) := by positivity
  have hkE : (400 * params.m * params.d : Error) ≤ (k : Error) := by exact_mod_cast hk
  field_simp [hden_pos.ne']
  nlinarith

/-- Specialize `lem:chernoff-bernoulli-matrix` to the averaged complete operator
`G = 𝔼_x ∑_g G^x_g` and the paper's `θ = 1/(200m)`.

This is the previously residual Bernoulli-tail lower-bound step in
`cor:ld-pasting-N-completeness`: the matrix Chernoff lemma is applied on the left
register to `G ⊗ I`, then `bernoulliTailOperator_leftTensor` identifies its
conclusion and swap-invariance transfers it to the paper-shaped right-register
`fromHToGBernoulliTailMass`. -/
private lemma fromHToGBernoulliTailMass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (kappa : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
      fromHToGBernoulliTailMass params strategy.state family k := by
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  let X : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) G
  have hGpsd : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
  have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
  have hXpsd : 0 ≤ X := by
    dsimp [X]
    exact leftTensor_nonneg (ι₂ := ι) hGpsd
  have hXle : X ≤ 1 := by
    dsimp [X]
    exact leftTensor_le_one (ι₂ := ι) hGle
  have hbase :
      CompletenessAtLeast strategy.state
        ({ outcome := fun _ : Unit => X
           total := X
           outcome_pos := by intro _; exact hXpsd
           sum_eq_total := by simp
           total_le_one := hXle } : SubMeas Unit (ι × ι))
        (1 - kappa) := by
    refine ⟨?_⟩
    simpa [subMeasMass, X, G, SubMeas.liftLeft] using hcomplete.averageCompleteness.lowerBound
  have hchern := chernoffBernoulliMatrix strategy.state strategy.isNormalized
    (1 / (200 * (params.m : Error))) k params.d X kappa
    (ldPasting_theta_pos params) (ldPasting_theta_lt_one params)
    (ldPasting_chernoff_size params k hk) hXpsd hXle hbase
  have hmassLower := hchern.matrixTailBound.lowerBound
  have hmass_eq :
      subMeasMass strategy.state
        ({ outcome := fun _ : Unit => bernoulliTailOperator k params.d X
           total := bernoulliTailOperator k params.d X
           outcome_pos := by
             intro _
             exact bernoulliTailOperator_nonneg k params.d X hXpsd hXle
           sum_eq_total := by simp
           total_le_one := bernoulliTailOperator_le_one k params.d X hXpsd hXle } :
          SubMeas Unit (ι × ι)) =
        fromHToGBernoulliTailMass params strategy.state family k := by
    have hswap :
        ev strategy.state
            (leftTensor (ι₂ := ι)
              (bernoulliTailOperator k params.d family.averagedSubMeas.total)) =
          ev strategy.state
            (rightTensor (ι₁ := ι)
              (bernoulliTailOperator k params.d family.averagedSubMeas.total)) :=
      ev_leftTensor_eq_rightTensor_of_density_fixed strategy.state strategy.densityFixed _
    simp [fromHToGBernoulliTailMass, bernoulliTailFromFamily, subMeasMass,
      IdxSubMeas.liftRight, constSubMeasFamily, X, G, bernoulliTailOperator_leftTensor,
      hswap]
  have htailMass :
      1 - kappa / (1 - 1 / (200 * (params.m : Error))) -
          Real.exp (-(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2) ≤
        fromHToGBernoulliTailMass params strategy.state family k := by
    simpa [hmass_eq] using hmassLower
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hkappa_nonneg : 0 ≤ kappa := by
    have hlower := hcomplete.averageCompleteness.lowerBound
    have hupper := hmass_le_one
    linarith
  have hcoef :
      kappa / (1 - 1 / (200 * (params.m : Error))) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) := by
    have := mul_le_mul_of_nonneg_left (ldPasting_theta_inv_le params) hkappa_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hexp :
      Real.exp (-(((1 / (200 * (params.m : Error))) ^ (2 : ℕ)) * (k : Error)) / 2) =
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    rw [ldPasting_chernoff_exponent_eq]
  linarith

/-- Internal form of `cor:ld-pasting-N-completeness` from the two preceding
mass-comparison inputs.

This theorem isolates the scalar assembly after `lem:over-all-outcomes`,
`lem:from-H-to-G`, and the Bernoulli-tail lower bound have already been
established. -/
theorem ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hOAO : OverAllOutcomesStatement params strategy family eps delta gamma zeta k)
    (hFrom : FromHToGStatement params strategy strategy.state family gamma zeta k)
    (htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  have happrox_le :
      overAllOutcomesError params eps delta gamma zeta k +
          fromHToGError params gamma zeta k ≤ ν := by
    simpa [ν] using
      overAllOutcomesError_add_fromHToGError_le_ldPastingNu params
        eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  constructor
  constructor
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

-- The downstream completeness theorem elaborates the full `fromHToG` bridge facts.
/-- `cor:ld-pasting-N-completeness` once the Bernoulli-tail lower bound is
supplied explicitly.

This packages the downstream scalar algebra after `lem:over-all-outcomes` and
`lem:from-H-to-G`. The hypothesis `htail` is exactly the `θ = 1 / (200m)`
specialization of `lem:chernoff-bernoulli-matrix` for the averaged complete
operator `G = \mathbb E_x \sum_g G^x_g`, repackaged as the concrete
`fromHToGBernoulliTailMass` lower bound with error
`κ · (1 + 1/(100m)) + exp(-k / (80000 m²))`. -/
theorem ldPastingNCompleteness_of_tailLowerBound
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
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (_hk : 400 * params.m * params.d ≤ k)
    (htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  have hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k
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
  have hFrom := fromHToG params strategy family eps delta gamma zeta
    hgamma_nonneg hzeta_nonneg hgamma_le hzeta_le hdq_le
    hgood hcons hself hbound k
  exact ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail params strategy
    eps delta gamma kappa zeta heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg family k hk_pos hOAO hFrom htail

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
    (hd : 0 < params.d)
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
    exact fromHToGBernoulliTailMass_lower_bound params strategy kappa family hcomplete k hk
  exact ldPastingNCompleteness_of_tailLowerBound params strategy
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le hd
    family hcons hself hbound k hk_pos hk htail

/-- Internal form of `cor:ld-pasting-N-completeness` from the Section 11
commutativity conclusion. -/
theorem ldPastingNCompleteness_ofComMain_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      haxis
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hself_good
  have hOAO := overAllOutcomes_ofComMain_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hgamma_le
    hzeta_nonneg hzeta_le hdq_le hd family hcons hself hcom k
  have hFrom := fromHToG_ofComMain params strategy family gamma zeta
    hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hself hcom k
  have htail :
      1 - kappa * (1 + 1 / (100 * (params.m : Error))) -
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        fromHToGBernoulliTailMass params strategy.state family k := by
    exact fromHToGBernoulliTailMass_lower_bound params strategy kappa family hcomplete k hk
  exact ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail params strategy
    eps delta gamma kappa zeta heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg family k hk_pos hOAO hFrom htail

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
    hAConsistency_submeas params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcons hself hbound k hk_pos
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  exact
    { pointConsistency := hconsistency
      completeness := hcompleteness.completenessBound }

/-- Restricted nontrivial-regime Lean form of `thm:ld-pasting`.

The source theorem is `references/ldt-paper/ld-pasting.tex`, lines 12--50.
Lines 52--55 explain that the proof may assume the nontrivial regime
`eps, delta, gamma, zeta, d / q ≤ 1`, since the complementary cases are
trivial.  This declaration states the restricted assumptions
`gamma ≤ 1`, `zeta ≤ 1`, `params.d ≤ params.q`, `0 < params.d`, and `1 ≤ k`.
The unrestricted statement aligned with the paper is `ldPasting`; the
degree-zero complementary branch is handled separately by
`ldPastingDegreeZeroBranch`. -/
theorem ldPastingNontrivial
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
    hAConsistency_submeas params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcons hself hbound k hk_pos
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  have hconsistency :=
    hAConsistency_completed params strategy eps delta gamma kappa zeta
      family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { pointConsistency := hconsistency }

/-- Trivial consistency conclusion when the target pasting error is at least `1`.

The consistency defect of two submeasurements against a normalized bipartite
state is always at most `1`; hence a scalar lower bound
`1 ≤ ldPastingInInductionError ...` is enough to produce the final conclusion
with a distinguished trivial measurement. -/
lemma ldPasting_of_one_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (herror :
      1 ≤ MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  let H : Measurement (Polynomial params.next) ι :=
    Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
  refine ⟨H, ?_⟩
  refine { pointConsistency := ?_ }
  exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas))
    herror⟩

/-- Trivial consistency conclusion from the complementary scalar branches.

If `k` is positive, it suffices to show that the `ν` term in the pasting error
is at least `1`; if `k = 0`, the exponential term already gives the trivial
bound. -/
lemma ldPasting_of_one_le_nu_or_zero_k
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hnu :
      1 ≤ k →
        1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    have hkappa_nonneg := kappa_nonneg_of_complete params strategy family hcomplete
    by_cases hk_pos : 1 ≤ k
    · exact one_le_ldPastingError_of_one_le_nu params k eps delta gamma kappa zeta
        hkappa_nonneg (hnu hk_pos)
    · have hk_zero : k = 0 := by omega
      exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        hkappa_nonneg hk_zero)

/-- Complementary branch for `thm:ld-pasting` when `gamma > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeGammaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hgamma : 1 < gamma) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_gamma params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hgamma)

/-- Complementary branch for `thm:ld-pasting` when `zeta > 1`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is one
of the large-error cases in which the final consistency bound is trivial.
This is one of the proved complementary cases for `thm:ld-pasting`. -/
theorem ldPastingLargeZetaBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hzeta : 1 < zeta) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_zeta params strategy eps delta gamma zeta
        hgood k hk_pos hzeta)

/-- Complementary branch for `thm:ld-pasting` when `d > q`.

Paper origin: `references/ldt-paper/ld-pasting.tex:52-55`, where this is the
large-error case `(d/q) ≥ 1`.  This is one of the proved complementary cases
for `thm:ld-pasting`. -/
theorem ldPastingLargeDegreeRatioBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hdq : params.q < params.d) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_nu_or_zero_k params strategy eps delta gamma kappa zeta
    family hcomplete k (fun hk_pos =>
      one_le_ldPastingNu_of_large_degreeRatio params strategy eps delta gamma zeta
        hgood family hcons k hk_pos hdq)

/-- Complementary branch for `thm:ld-pasting` when `k = 0`.

This branch is a boundary case for the reduction to the nontrivial theorem,
whose proof assumes `1 ≤ k`.  The scalar calculation showing that the
exponential term gives the trivial bound is proved in `ScalarBounds.lean`. -/
theorem ldPastingZeroKBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hk_zero : k = 0) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  exact ldPasting_of_one_le_error params strategy eps delta gamma kappa zeta family k (by
    exact one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
      (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)

/-- Degree-zero complementary branch for the unrestricted source theorem.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  The paper's
large-error reduction names the cases
`eps, delta, gamma, zeta, d/q ≥ 1`; it does not explicitly add `0 < d` as a
hypothesis of `thm:ld-pasting`.  Thus the Lean theorem should not add `0 < d`
as an assumption of that cited theorem.

Issue #1622 recorded the need for a direct proof of this degree-zero branch; see
`docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex`.  The existing
nontrivial argument cannot simply be reused: its `hBConsistency` aggregation
passes from distinct sampled heights to independent sampled heights and absorbs
the resulting `k^2/q` loss through the displayed `(d/q)^(1/32)` term.  When
`d = 0`, that term is zero, so the branch requires a separate argument rather
than an additional hypothesis on `ldPasting`. -/
theorem ldPastingDegreeZeroBranch
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (_hk : 400 * params.m * params.d ≤ k)
    (hd_zero : params.d = 0)
    (_hk_pos : 1 ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    degreeZeroPastedPointConsistency params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hd_zero k
  exact ⟨H, { pointConsistency := hH }⟩

/-- Projection from the restricted nontrivial construction.

The restricted construction theorem `ldPastingNontrivial` proves the nontrivial
analytic regime for the canonical pasted measurement.  This auxiliary statement
records the projection from the restricted construction theorem to the conclusion
needed by the unrestricted theorem, without changing the statement of
`thm:ld-pasting`. -/
theorem ldPastingNontrivialPublicBranch
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
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  obtain ⟨H, _hHdef, hH⟩ :=
    ldPastingNontrivial params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  exact ⟨H, hH⟩

/-- Paper-aligned form of `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex`, lines 12--50.  The
following lines 52--55 explain that the proof may restrict to the regime
`eps, delta, gamma, zeta, d / q ≤ 1`, because the complementary cases are
trivial.  The restricted theorem `ldPastingNontrivial` proves the nontrivial
regime, and the large-`gamma`, large-`zeta`, large-`d / q`, and `k = 0`
complementary branches are proved above, including the degree-zero case, so
this declaration keeps the unrestricted paper statement visible without adding
the non-paper assumptions from the restricted theorem.  The former obstruction is documented in
`docs/paper-gaps/issue-1622-ld-pasting-degree-zero.tex`. -/
theorem ldPasting
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  by_cases hgamma_le : gamma ≤ 1
  · by_cases hzeta_le : zeta ≤ 1
    · by_cases hdq_le : params.d ≤ params.q
      · by_cases hd : 0 < params.d
        · by_cases hk_pos : 1 ≤ k
          · exact ldPastingNontrivialPublicBranch params strategy eps delta gamma kappa zeta
              hgood hgamma_le hzeta_le hdq_le hd family hcomplete hcons hself hbound
              k hk_pos hk
          · have hk_zero : k = 0 := by omega
            exact ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
        · have hd_zero : params.d = 0 := Nat.eq_zero_of_not_pos hd
          by_cases hk_pos : 1 ≤ k
          · exact ldPastingDegreeZeroBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hd_zero hk_pos
          · have hk_zero : k = 0 := by omega
            exact ldPastingZeroKBranch params strategy eps delta gamma kappa zeta
              hgood family hcomplete hcons hself hbound k hk hk_zero
      · have hdq : params.q < params.d := by omega
        exact ldPastingLargeDegreeRatioBranch params strategy eps delta gamma kappa zeta
          hgood family hcomplete hcons hself hbound k hk hdq
    · have hzeta : 1 < zeta := lt_of_not_ge hzeta_le
      exact ldPastingLargeZetaBranch params strategy eps delta gamma kappa zeta
        hgood family hcomplete hcons hself hbound k hk hzeta
  · have hgamma : 1 < gamma := lt_of_not_ge hgamma_le
    exact ldPastingLargeGammaBranch params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk hgamma

end MIPStarRE.LDT.Pasting
