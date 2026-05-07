import MIPStarRE.LDT.Pasting.SwitcherooCompletion.SecondTerm

/-!
# Section 12 pasting: complete-part reductions

Complete-part aggregate commutation and scalar error bounds.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expand the left aggregate family after replacing the slice family by its
completed one-outcome form. -/
private lemma switcherooAggregateLeft_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateLeft params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductLeft params family q).outcome () := by
  simp [switcherooAggregateLeft, completePartProjFamily,
    completePartTotalProductLeft, multiplyByTotalOnRight,
    multiplyByTotalOnLeft, OpFamily.leftPlacedOpFamily]

/-- Expand the right aggregate family after replacing the slice family by its
completed one-outcome form. -/
private lemma switcherooAggregateRight_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateRight params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductRight params family q).outcome () := by
  simp [switcherooAggregateRight, completePartProjFamily,
    completePartTotalProductRight, multiplyByTotalOnRight,
    multiplyByTotalOnLeft, OpFamily.leftPlacedOpFamily]

private lemma qSDDOp_congr_unit_outcome
    (ψbi : QuantumState (ι × ι))
    (A B A' B' : OpFamily Unit (ι × ι))
    (hA : A.outcome () = A'.outcome ())
    (hB : B.outcome () = B'.outcome ()) :
    qSDDOp ψbi A B = qSDDOp ψbi A' B' := by
  unfold qSDDOp qSDDCore
  simp [hA, hB]

/-- When the left/right aggregate families are re-expressed using the
completed one-outcome form, the aggregate commutation bound translates to the
complete-part total-product commutation bound. -/
lemma completePartAggregateCommutation_as_total
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family (completePartProjFamily params family))
      (switcherooAggregateRight params family (completePartProjFamily params family))
      gamma) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      gamma := by
  rcases hcomm with ⟨hcomm⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          qSDDOp ψbi
            (completePartTotalProductLeft params family q)
            (completePartTotalProductRight params family q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q =>
            qSDDOp ψbi
              (switcherooAggregateLeft params family (completePartProjFamily params family) q)
              (switcherooAggregateRight params family
                (completePartProjFamily params family) q)) := by
                apply avgOver_congr
                intro q
                symm
                exact qSDDOp_congr_unit_outcome ψbi
                  _ _ _ _
                  (switcherooAggregateLeft_completePart_outcome params family q)
                  (switcherooAggregateRight_completePart_outcome params family q)
    _ ≤ gamma := hcomm

set_option maxHeartbeats 1000000 in -- large sqrt/rpow proof, see issue #894
/-- Variant of the first switcheroo scalar bound using the intermediate
`eighthSum`; shared with `CommutingWithG/Complete`. -/
lemma firstSwitcherooError_le_eighth_stage
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma)
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

set_option maxHeartbeats 1000000 in -- large sqrt/rpow proof, see issue #894
/-- Many sqrt/rpow manipulations for `12 * sqrt zeta + 4 * sqrt (ν_com) ≤ ν₂`.
This shows that the first-switcheroo error (the `commutativitySwitcherooError`)
is bounded above by the complete-part commuting-with-G error. -/
lemma firstSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (Commutativity.comMainError params gamma zeta)
      ≤ commutingWithGCompleteError params gamma zeta := by
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
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have heighth_gamma :
      Real.rpow gamma (1 / (8 : Error)) ≤ Real.rpow gamma (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
  have heighth_zeta :
      Real.rpow zeta (1 / (8 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have heighth_ratio :
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) ≤
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have heighth_le_sixteenth : eighthSum ≤ sixteenthSum := by
    dsimp [eighthSum, sixteenthSum]
    exact add_le_add (add_le_add heighth_gamma heighth_zeta) heighth_ratio
  calc
    commutativitySwitcherooError zeta zeta (Commutativity.comMainError params gamma zeta)
      ≤ 36 * (params.m : Error) * eighthSum := by
          exact firstSwitcherooError_le_eighth_stage params gamma zeta
            hgamma_nonneg hzeta_nonneg hzeta hd_le_q
    _ ≤ 36 * (params.m : Error) * sixteenthSum := by
          gcongr
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]

end MIPStarRE.LDT.Pasting
