import MIPStarRE.LDT.Pasting.SwitcherooCompletion.CompletePart

/-!
# Section 12 pasting: commuting-with-G complete part

Complete-part commuting-with-`G` bounds.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
-- Variant of firstSwitcherooError bound using eighthSum; heavy sqrt/rpow chain.
private lemma firstSwitcherooError_le_eighth_stage
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (_hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (Commutativity.comMainError params gamma zeta)
      ≤ 36 * (params.m : Error) *
        (Real.rpow gamma (1 / (8 : Error)) +
          Real.rpow zeta (1 / (8 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hq_pos : (0 : Error) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let quarterSum : Error :=
    Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))
  let eighthSum : Error :=
    Real.rpow gamma (1 / (8 : Error)) +
      Real.rpow zeta (1 / (8 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
  have heighth_nonneg : 0 ≤ eighthSum := by
    dsimp [eighthSum]
    positivity
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : Error)) ≤ Real.rpow zeta (1 / (8 : Error)) := by
    have hpow : (1 / (8 : Error)) ≤ (1 / (2 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have hgamma_eight_sq :
      (Real.rpow gamma (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (4 : Error)) := by
    calc
      (Real.rpow gamma (1 / (8 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (8 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (4 : Error)) := by norm_num
  have hzeta_eight_sq :
      (Real.rpow zeta (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (4 : Error)) := by
    calc
      (Real.rpow zeta (1 / (8 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (8 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (4 : Error)) := by norm_num
  have hratio_eight_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^
              (2 : Error) := by norm_num
      _ =
          Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (8 : Error)) * (2 : Error)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
            norm_num
  have hquarter_le_eighth_sq : quarterSum ≤ eighthSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (8 : Error))
    let b : Error := Real.rpow zeta (1 / (8 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_eight_sq, hzeta_eight_sq, hratio_eight_sq] at hsq
    simpa [a, b, c, quarterSum, eighthSum] using hsq
  have hsqrt_quarter : Real.sqrt quarterSum ≤ eighthSum := by
    have heighth_nonneg : 0 ≤ eighthSum := by
      dsimp [eighthSum]
      positivity
    exact (Real.sqrt_le_iff).2 ⟨heighth_nonneg, by simpa using hquarter_le_eighth_sq⟩
  have hsqrt30_le_six : Real.sqrt (30 : Error) ≤ 6 := by
    have hsq : (Real.sqrt (30 : Error)) ^ (2 : ℕ) ≤ (6 : Error) ^ (2 : ℕ) := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (30 : Error) by positivity), hsq]
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt_com :
      Real.sqrt (Commutativity.comMainError params gamma zeta) ≤
        6 * (params.m : Error) * eighthSum := by
    have hquarter_nonneg : 0 ≤ quarterSum := by
      dsimp [quarterSum]
      positivity
    have hsplit_m_quarter :
        Real.sqrt ((params.m : Error) * quarterSum) =
          Real.sqrt (params.m : Error) * Real.sqrt quarterSum := by
      rw [Real.sqrt_mul hm_nonneg]
    calc
      Real.sqrt (Commutativity.comMainError params gamma zeta)
          = Real.sqrt (30 : Error) *
              Real.sqrt ((params.m : Error) * quarterSum) := by
              simp [Commutativity.comMainError, quarterSum]
              ring
      _ = Real.sqrt (30 : Error) * (Real.sqrt (params.m : Error) * Real.sqrt quarterSum) := by
            rw [hsplit_m_quarter]
      _ = Real.sqrt (30 : Error) * Real.sqrt (params.m : Error) * Real.sqrt quarterSum := by
            ring
      _ ≤ 6 * (params.m : Error) * eighthSum := by
            gcongr
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * (params.m : Error) * eighthSum := by
    have hgamma8_nonneg : 0 ≤ Real.rpow gamma (1 / (8 : Error)) := by
      exact Real.rpow_nonneg hgamma_nonneg _
    have hratio8_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
      exact Real.rpow_nonneg hratio_nonneg _
    have hsum1 :
        Real.rpow zeta (1 / (8 : Error)) ≤
          Real.rpow gamma (1 / (8 : Error)) + Real.rpow zeta (1 / (8 : Error)) := by
      linarith
    have hsum2 :
        Real.rpow gamma (1 / (8 : Error)) + Real.rpow zeta (1 / (8 : Error)) ≤ eighthSum := by
      have hsum2' :
          Real.rpow gamma (1 / (8 : Error)) + Real.rpow zeta (1 / (8 : Error)) ≤
            Real.rpow gamma (1 / (8 : Error)) + Real.rpow zeta (1 / (8 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
        linarith
      simpa [eighthSum] using hsum2'
    have hterm : Real.rpow zeta (1 / (2 : Error)) ≤ eighthSum := by
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    calc
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * eighthSum := by
        gcongr
      _ ≤ 12 * ((params.m : Error) * eighthSum) := by
        nlinarith [hm_ge_one, heighth_nonneg]
      _ = 12 * (params.m : Error) * eighthSum := by ring
  have hchi_term :
      4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
        24 * (params.m : Error) * eighthSum := by
    have hsqrt_com' :
        Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
          6 * (params.m : Error) * eighthSum := by
      simpa [Real.sqrt_eq_rpow] using hsqrt_com
    nlinarith [hsqrt_com']
  calc
    commutativitySwitcherooError zeta zeta (Commutativity.comMainError params gamma zeta)
      = 12 * Real.rpow zeta (1 / (2 : Error)) +
          4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) := by
            simp [commutativitySwitcherooError]
            ring
    _ ≤ 12 * (params.m : Error) * eighthSum +
          24 * (params.m : Error) * eighthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = 36 * (params.m : Error) * eighthSum := by ring
    _ = 36 * (params.m : Error) *
          (Real.rpow gamma (1 / (8 : Error)) +
            Real.rpow zeta (1 / (8 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) := by
            simp [eighthSum]

/-- The paper's scalar inequality
`12·√ζ + 4·√θ₁ ≤ ν₂`, where `θ₁ = θ(ζ, ζ, comMainError)` is the first switcheroo
error. The proof uses `firstSwitcherooError_le_eighth_stage` to bound `θ₁` by
`36m · eighthSum`, then a sqrt/rpow chain to land on `ν₂ = commutingWithGCompleteError`. -/
private lemma secondSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (Commutativity.comMainError params gamma zeta))
      ≤ commutingWithGCompleteError params gamma zeta := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hq_pos : (0 : Error) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let eighthSum : Error :=
    Real.rpow gamma (1 / (8 : Error)) +
      Real.rpow zeta (1 / (8 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hgamma_sixteen_sq :
      (Real.rpow gamma (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (8 : Error)) := by
    calc
      (Real.rpow gamma (1 / (16 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (16 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (16 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (8 : Error)) := by norm_num
  have hzeta_sixteen_sq :
      (Real.rpow zeta (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (8 : Error)) := by
    calc
      (Real.rpow zeta (1 / (16 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (16 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (16 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (8 : Error)) := by norm_num
  have hratio_sixteen_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) ^
              (2 : Error) := by norm_num
      _ =
          Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (16 : Error)) * (2 : Error)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) := by
            norm_num
  have heighth_le_sixteenth_sq : eighthSum ≤ sixteenthSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (16 : Error))
    let b : Error := Real.rpow zeta (1 / (16 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_sixteen_sq, hzeta_sixteen_sq, hratio_sixteen_sq] at hsq
    simpa [a, b, c, eighthSum, sixteenthSum] using hsq
  have hsqrt_eighth : Real.sqrt eighthSum ≤ sixteenthSum := by
    exact (Real.sqrt_le_iff).2 ⟨hsixteenth_nonneg, by simpa using heighth_le_sixteenth_sq⟩
  have hsqrt_theta1 :
      Real.rpow
        (commutativitySwitcherooError zeta zeta
          (Commutativity.comMainError params gamma zeta))
        (1 / (2 : Error)) ≤ 6 * (params.m : Error) * sixteenthSum := by
    have hsqrt36 : Real.sqrt (36 : Error) = 6 := by norm_num
    have hsqrt_theta1' :
        Real.sqrt
          (commutativitySwitcherooError zeta zeta
            (Commutativity.comMainError params gamma zeta))
          ≤ 6 * (params.m : Error) * sixteenthSum := by
      calc
        Real.sqrt
            (commutativitySwitcherooError zeta zeta
              (Commutativity.comMainError params gamma zeta))
          ≤ Real.sqrt (36 * (params.m : Error) * eighthSum) := by
              have htheta1_bound :=
                firstSwitcherooError_le_eighth_stage params gamma zeta
                  hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
              exact Real.sqrt_le_sqrt htheta1_bound
        _ = Real.sqrt (36 : Error) * Real.sqrt ((params.m : Error) * eighthSum) := by
              rw [show (36 * (params.m : Error) * eighthSum) =
                (36 : Error) * ((params.m : Error) * eighthSum) by ring]
              rw [Real.sqrt_mul (by positivity)]
        _ = 6 * (Real.sqrt (params.m : Error) * Real.sqrt eighthSum) := by
              rw [hsqrt36, Real.sqrt_mul hm_nonneg]
        _ ≤ 6 * ((params.m : Error) * Real.sqrt eighthSum) := by
              gcongr
        _ ≤ 6 * ((params.m : Error) * sixteenthSum) := by
              gcongr
        _ = 6 * (params.m : Error) * sixteenthSum := by ring
    simpa [Real.sqrt_eq_rpow] using hsqrt_theta1'
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (2 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
    exact Real.rpow_nonneg hgamma_nonneg _
  have hratio16_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    exact Real.rpow_nonneg hratio_nonneg _
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * (params.m : Error) * sixteenthSum := by
    have hsum1 :
        Real.rpow zeta (1 / (16 : Error)) ≤
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) := by
      linarith
    have hsum2 :
        Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤ sixteenthSum := by
      have hsum2' :
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        linarith
      simpa [sixteenthSum] using hsum2'
    have hterm : Real.rpow zeta (1 / (2 : Error)) ≤ sixteenthSum := by
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    calc
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * sixteenthSum := by
        gcongr
      _ ≤ 12 * ((params.m : Error) * sixteenthSum) := by
        nlinarith [hm_ge_one, hsixteenth_nonneg]
      _ = 12 * (params.m : Error) * sixteenthSum := by ring
  have hchi_term :
      4 * Real.rpow
        (commutativitySwitcherooError zeta zeta
          (Commutativity.comMainError params gamma zeta))
        (1 / (2 : Error)) ≤ 24 * (params.m : Error) * sixteenthSum := by
    nlinarith [hsqrt_theta1]
  calc
    commutativitySwitcherooError zeta zeta
      (commutativitySwitcherooError zeta zeta
        (Commutativity.comMainError params gamma zeta))
      = 12 * Real.rpow zeta (1 / (2 : Error)) +
          4 * Real.rpow
            (commutativitySwitcherooError zeta zeta
              (Commutativity.comMainError params gamma zeta))
            (1 / (2 : Error)) := by
              simp [commutativitySwitcherooError]
              ring
    _ ≤ 12 * (params.m : Error) * sixteenthSum +
          24 * (params.m : Error) * sixteenthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]
          ring

/-- `cor:commuting-with-G-complete`. -/
theorem commutingWithGComplete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hcom : Commutativity.ComMainConclusion params strategy family G gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    CommutingWithGCompleteStatement params strategy.state family gamma zeta := by
  have hswitch₁ :
      CommutativitySwitcherooStatement params strategy.state family family.meas
        zeta zeta (pairwiseCompletePartCommutationError params gamma zeta) := by
    simpa [pairwiseCompletePartCommutationError] using
      commutativitySwitcheroo params strategy.state strategy.isNormalized
        strategy.densityFixed
        family family.meas zeta zeta
        (Commutativity.comMainError params gamma zeta)
        hself hself.completePartSelfConsistency hcom.fullSliceCommutation
  have hpoint_raw :
      SDDOpRel strategy.state
        (uniformDistribution (SlicePairQuestion params))
        (completePartPointProductLeft params family)
        (completePartPointProductRight params family)
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) := by
    have hswap :=
      sddOpRel_swap_questions params strategy.state
        (switcherooAggregateLeft params family family.meas)
        (switcherooAggregateRight params family family.meas)
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta))
        hswitch₁.aggregateCommutation
    have hsymm :=
      MIPStarRE.LDT.Preliminaries.sddOpRel_symm strategy.state
        (uniformDistribution (SlicePairQuestion params))
        (fun q => (switcherooAggregateLeft params family family.meas) (q.2, q.1))
        (fun q => (switcherooAggregateRight params family family.meas) (q.2, q.1))
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta))
        hswap
    simpa [switcherooAggregateLeft, switcherooAggregateRight,
      completePartPointProductLeft, completePartPointProductRight,
      completePartSubMeas, multiplyByTotalOnRight, multiplyByTotalOnLeft]
      using hsymm
  have hpoint :
      SDDOpRel strategy.state
        (uniformDistribution (SlicePairQuestion params))
        (completePartPointProductLeft params family)
        (completePartPointProductRight params family)
        (commutingWithGCompleteError params gamma zeta) :=
    MIPStarRE.LDT.Preliminaries.sddOpRel_mono strategy.state
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      (commutativitySwitcherooError zeta zeta
        (pairwiseCompletePartCommutationError params gamma zeta))
      (commutingWithGCompleteError params gamma zeta)
      hpoint_raw
      (firstSwitcherooError_le_commutingWithGCompleteError params gamma zeta
        hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q)
  have hswitch₂ :
      CommutativitySwitcherooStatement params strategy.state family
        (completePartProjFamily params family)
        zeta zeta
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) := by
    apply commutativitySwitcheroo params strategy.state strategy.isNormalized
      strategy.densityFixed family
      (completePartProjFamily params family) zeta zeta
      (commutativitySwitcherooError zeta zeta
        (pairwiseCompletePartCommutationError params gamma zeta))
    · exact hself
    · exact completePartProjFamily_selfConsistency params strategy family zeta hself
    · exact pointWithCompletePart_as_switcheroo_input params strategy.state family
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)) hpoint_raw
  have htotal_raw :
      SDDOpRel strategy.state
        (uniformDistribution (SlicePairQuestion params))
        (completePartTotalProductLeft params family)
        (completePartTotalProductRight params family)
        (commutativitySwitcherooError zeta zeta
          (commutativitySwitcherooError zeta zeta
            (pairwiseCompletePartCommutationError params gamma zeta))) := by
    exact completePartAggregateCommutation_as_total params strategy.state family
      (commutativitySwitcherooError zeta zeta
        (commutativitySwitcherooError zeta zeta
          (pairwiseCompletePartCommutationError params gamma zeta)))
      hswitch₂.aggregateCommutation
  refine
    { pairwiseCompletePartCommutation := by
        simpa [pairwiseCompletePartCommutationError,
          Commutativity.fullSliceProductLeft, Commutativity.fullSliceProductRight,
          Commutativity.leftOrderedProductOpFamily] using hcom.fullSliceCommutation
      pointWithCompletePartCommutation := hpoint
      completePartCommutation :=
        MIPStarRE.LDT.Preliminaries.sddOpRel_mono strategy.state
          (uniformDistribution (SlicePairQuestion params))
          (completePartTotalProductLeft params family)
          (completePartTotalProductRight params family)
          (commutativitySwitcherooError zeta zeta
            (commutativitySwitcherooError zeta zeta
              (pairwiseCompletePartCommutationError params gamma zeta)))
          (commutingWithGCompleteError params gamma zeta)
          htotal_raw
          (secondSwitcherooError_le_commutingWithGCompleteError params gamma zeta
            hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q) }

end MIPStarRE.LDT.Pasting
