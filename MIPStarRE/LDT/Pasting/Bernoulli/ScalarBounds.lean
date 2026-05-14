import MIPStarRE.LDT.Pasting.Bernoulli.Recurrence

/-!
# Section 12 pasting: scalar bounds for complementary Bernoulli branches

This file collects the elementary scalar estimates used by the complementary
branches of `thm:ld-pasting`.  These estimates correspond to the large-error
reduction in `references/ldt-paper/ld-pasting.tex`, lines 52--55.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar `κ` in a complete family is nonnegative. -/
lemma kappa_nonneg_of_complete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {kappa : Error}
    (hcomplete : family.Complete strategy.state kappa) :
    0 ≤ kappa := by
  have hmass_le_one : subMeasMass strategy.state family.averagedSubMeas.liftLeft ≤ 1 := by
    unfold subMeasMass SubMeas.liftLeft
    have hle : leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      exact leftTensor_le_one (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total_le_one
    simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
      ev_mono strategy.state _ _ hle
  have hlower := hcomplete.averageCompleteness.lowerBound
  linarith

/-- The coefficient multiplying `κ` in the pasting error is nonnegative. -/
lemma ldPasting_kappa_coefficient_nonneg (params : Parameters) :
    0 ≤ (1 : Error) + 1 / (100 * (params.m : Error)) := by
  have hm_one : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hm_pos : (0 : Error) < (params.m : Error) := lt_of_lt_of_le zero_lt_one hm_one
  have hden_pos : (0 : Error) < 100 * (params.m : Error) := by positivity
  have hfrac_nonneg : 0 ≤ (1 : Error) / (100 * (params.m : Error)) :=
    div_nonneg zero_le_one hden_pos.le
  linarith

/-- The ratio `d / q` is nonnegative in the error scalar field. -/
lemma ldPasting_degreeRatio_nonneg
    (params : Parameters)
    [FieldModel params.q] :
    0 ≤ ((params.d : Error) / (params.q : Error)) := by
  exact div_nonneg (by exact_mod_cast Nat.zero_le params.d) (le_of_lt params.q_cast_pos)

/-- A unit lower bound on `ν` gives a unit lower bound on the final pasting error. -/
lemma one_le_ldPastingError_of_one_le_nu
    (params : Parameters)
    (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hkappa_nonneg : 0 ≤ kappa)
    (hnu :
      1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :
    1 ≤ MainInductionStep.ldPastingInInductionError params k
      eps delta gamma kappa zeta := by
  have hkappa_term_nonneg :
      0 ≤ kappa * (1 + 1 / (100 * (params.m : Error))) :=
    mul_nonneg hkappa_nonneg (ldPasting_kappa_coefficient_nonneg params)
  have hexp_nonneg :
      0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
    le_of_lt (Real.exp_pos _)
  change
    1 ≤ kappa * (1 + 1 / (100 * (params.m : Error))) +
        2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta +
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
  nlinarith

/-- If `k = 0`, the exponential term alone gives the trivial pasting bound. -/
lemma one_le_ldPastingError_of_k_eq_zero
    (params : Parameters)
    (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hkappa_nonneg : 0 ≤ kappa)
    (hk_zero : k = 0) :
    1 ≤ MainInductionStep.ldPastingInInductionError params k
      eps delta gamma kappa zeta := by
  subst k
  have hkappa_term_nonneg :
      0 ≤ kappa * (1 + 1 / (100 * (params.m : Error))) :=
    mul_nonneg hkappa_nonneg (ldPasting_kappa_coefficient_nonneg params)
  have hkappa_term_nonneg' :
      0 ≤ kappa * (1 + ((params.m : Error))⁻¹ * 100⁻¹) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hkappa_term_nonneg
  simp [MainInductionStep.ldPastingInInductionError,
    MainInductionStep.ldPastingInInductionNu]
  nlinarith

/-- The `ν` term is at least one when `γ > 1` and `k ≥ 1`. -/
lemma one_le_ldPastingNu_of_large_gamma
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hgamma : 1 < gamma) :
    1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let kE : Error := (k : Error)
  let mE : Error := (params.m : Error)
  let ratio : Error := (params.d : Error) / (params.q : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let dqTerm : Error := Real.rpow ratio (1 / (32 : Error))
  let fullSum : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + dqTerm
  let coeff : Error := 100 * (kE ^ (2 : ℕ)) * mE
  have hkE_one : (1 : Error) ≤ kE := by
    dsimp [kE]
    exact_mod_cast hk_pos
  have hmE_one : (1 : Error) ≤ mE := by
    dsimp [mE]
    exact_mod_cast params.hm
  have hcoeff_one : (1 : Error) ≤ coeff := by
    dsimp [coeff]
    nlinarith [sq_nonneg kE, hkE_one, hmE_one]
  have hcoeff_nonneg : 0 ≤ coeff := le_trans zero_le_one hcoeff_one
  have heps_nonneg : 0 ≤ eps := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta := delta_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_one : 1 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact le_of_lt (Real.one_lt_rpow hgamma (by norm_num))
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdqTerm_nonneg : 0 ≤ dqTerm := by
    dsimp [dqTerm, ratio]
    exact Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  have hfullSum_one : (1 : Error) ≤ fullSum := by
    dsimp [fullSum]
    nlinarith
  have hprod : (1 : Error) ≤ coeff * fullSum := by
    simpa using
      (mul_le_mul hcoeff_one hfullSum_one zero_le_one hcoeff_nonneg :
        (1 : Error) * 1 ≤ coeff * fullSum)
  simpa [MainInductionStep.ldPastingInInductionNu, coeff, fullSum, epsTerm,
    deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio, kE, mE] using hprod

/-- The `ν` term is at least one when `ζ > 1` and `k ≥ 1`. -/
lemma one_le_ldPastingNu_of_large_zeta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hzeta : 1 < zeta) :
    1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let kE : Error := (k : Error)
  let mE : Error := (params.m : Error)
  let ratio : Error := (params.d : Error) / (params.q : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let dqTerm : Error := Real.rpow ratio (1 / (32 : Error))
  let fullSum : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + dqTerm
  let coeff : Error := 100 * (kE ^ (2 : ℕ)) * mE
  have hkE_one : (1 : Error) ≤ kE := by
    dsimp [kE]
    exact_mod_cast hk_pos
  have hmE_one : (1 : Error) ≤ mE := by
    dsimp [mE]
    exact_mod_cast params.hm
  have hcoeff_one : (1 : Error) ≤ coeff := by
    dsimp [coeff]
    nlinarith [sq_nonneg kE, hkE_one, hmE_one]
  have hcoeff_nonneg : 0 ≤ coeff := le_trans zero_le_one hcoeff_one
  have heps_nonneg : 0 ≤ eps := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg : 0 ≤ gamma := gamma_nonneg_of_isGood params.next strategy hgood
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_one : 1 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact le_of_lt (Real.one_lt_rpow hzeta (by norm_num))
  have hdqTerm_nonneg : 0 ≤ dqTerm := by
    dsimp [dqTerm, ratio]
    exact Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  have hfullSum_one : (1 : Error) ≤ fullSum := by
    dsimp [fullSum]
    nlinarith
  have hprod : (1 : Error) ≤ coeff * fullSum := by
    simpa using
      (mul_le_mul hcoeff_one hfullSum_one zero_le_one hcoeff_nonneg :
        (1 : Error) * 1 ≤ coeff * fullSum)
  simpa [MainInductionStep.ldPastingInInductionNu, coeff, fullSum, epsTerm,
    deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio, kE, mE] using hprod

/-- The `ν` term is at least one when `d / q > 1` and `k ≥ 1`. -/
lemma one_le_ldPastingNu_of_large_degreeRatio
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hdq : params.q < params.d) :
    1 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let kE : Error := (k : Error)
  let mE : Error := (params.m : Error)
  let ratio : Error := (params.d : Error) / (params.q : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let dqTerm : Error := Real.rpow ratio (1 / (32 : Error))
  let fullSum : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + dqTerm
  let coeff : Error := 100 * (kE ^ (2 : ℕ)) * mE
  have hkE_one : (1 : Error) ≤ kE := by
    dsimp [kE]
    exact_mod_cast hk_pos
  have hmE_one : (1 : Error) ≤ mE := by
    dsimp [mE]
    exact_mod_cast params.hm
  have hcoeff_one : (1 : Error) ≤ coeff := by
    dsimp [coeff]
    nlinarith [sq_nonneg kE, hkE_one, hmE_one]
  have hcoeff_nonneg : 0 ≤ coeff := le_trans zero_le_one hcoeff_one
  have heps_nonneg : 0 ≤ eps := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg : 0 ≤ gamma := gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have hratio_gt_one : 1 < ratio := by
    dsimp [ratio]
    have hdq_cast : (params.q : Error) < (params.d : Error) := by exact_mod_cast hdq
    exact (one_lt_div params.q_cast_pos).2 hdq_cast
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
  have hdqTerm_one : 1 ≤ dqTerm := by
    dsimp [dqTerm]
    exact le_of_lt (Real.one_lt_rpow hratio_gt_one (by norm_num))
  have hfullSum_one : (1 : Error) ≤ fullSum := by
    dsimp [fullSum]
    nlinarith
  have hprod : (1 : Error) ≤ coeff * fullSum := by
    simpa using
      (mul_le_mul hcoeff_one hfullSum_one zero_le_one hcoeff_nonneg :
        (1 : Error) * 1 ≤ coeff * fullSum)
  simpa [MainInductionStep.ldPastingInInductionNu, coeff, fullSum, epsTerm,
    deltaTerm, gammaTerm, zetaTerm, dqTerm, ratio, kE, mE] using hprod

end MIPStarRE.LDT.Pasting
