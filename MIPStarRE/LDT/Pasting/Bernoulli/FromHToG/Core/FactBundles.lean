import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.AveragesAndOps
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.StageMass
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup

/-!
# Section 12 pasting: exact identities and error-bound lemma

Exact recurrence identities and the paper-total error absorption lemma that
assemble the final `fromHToG` telescope conclusion.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact bookkeeping at the end of the adjacent-stage bridge.

This isolates the paper's `S`-recurrence step
`references/ldt-paper/ld-pasting.tex:1417--1425` and its use in the final
collapse at lines `1657--1661`: once the analytic move-right / commute /
move-right approximations have reached the branch-split expression, the
recurrence weight is exactly the next-stage weight. -/
structure FromHToGAdjacentStageExactFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) : Prop where
  completeBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total
  incompleteBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total
  tailWeightRecurrence :
    ∀ (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen),
      fromHToGTailStageMass params ψbi family (prefixLen + 1) τtail =
        ev ψbi (leftTensor (ι₂ := ι)
          (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
            rightTensor (ι₁ := ι)
            (fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit true τtail) * family.averagedSubMeas.total +
              fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total)))

/-- Collect the exact `S`-recurrence identities proved in
`Core/AveragesAndOps` and `Core/StageMass`. -/
lemma fromHToGAdjacentStageExactFacts_of_weights
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    FromHToGAdjacentStageExactFacts params ψbi family where
  completeBranchAverage :=
    fromHToG_completePart_average_total_eq params family
  incompleteBranchAverage :=
    fromHToG_incompletePart_average_total_eq params family
  tailWeightRecurrence :=
    fromHToGTailStageMass_succ_weight_recurrence params ψbi family

set_option maxHeartbeats 800000 in
-- The scalar proof expands several `rpow` square identities and a nonlinear
-- square comparison mirroring `ld-pasting.tex:1372--1375`.
/-- The paper's scalar absorption line for `lem:from-H-to-G`.

Under the side conditions needed for the `√(2ζ)` term (`γ, ζ ≥ 0` and
`ζ ≤ 1`), the paper-total error from
`references/ldt-paper/ld-pasting.tex:1372--1375` is bounded by the displayed
`fromHToGError`.  The proof follows the paper arithmetic: bound
`√(2ζ)` by `2 ζ^(1/32)`, bound `√426` by `21`, and use
`√(γ^(1/16)+ζ^(1/16)+(d/q)^(1/16)) ≤ γ^(1/32)+ζ^(1/32)+(d/q)^(1/32)`. -/
lemma fromHToGPaperTotalError_le
    (params : Parameters) (gamma zeta : Error) (k : ℕ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1) :
    fromHToGPaperTotalError params gamma zeta k ≤
      fromHToGError params gamma zeta k := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_nonneg : 0 ≤ (k : Error) := by positivity
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  let thirtysecondSum : Error :=
    Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : Error)) :=
    Real.rpow_nonneg hgamma_nonneg _
  have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hratio32_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
    Real.rpow_nonneg hratio_nonneg _
  have hthirtysecond_nonneg : 0 ≤ thirtysecondSum := by
    dsimp [thirtysecondSum]
    positivity
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hgamma32_sq :
      (Real.rpow gamma (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (16 : Error)) := by
    calc
      (Real.rpow gamma (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (16 : Error)) := by norm_num
  have hzeta32_sq :
      (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (16 : Error)) := by
    calc
      (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (16 : Error)) := by norm_num
  have hratio32_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
          (2 : ℕ)
          = (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
              (2 : Error) := by norm_num
      _ = Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
            norm_num
  have hsixteenth_le_thirtysecond_sq : sixteenthSum ≤ thirtysecondSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (32 : Error))
    let b : Error := Real.rpow zeta (1 / (32 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma32_sq, hzeta32_sq, hratio32_sq] at hsq
    simpa [a, b, c, sixteenthSum, thirtysecondSum] using hsq
  have hzeta_le_sixteenth : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
    simpa using Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le_one (by norm_num) hpow
  have hsqrt_two_zeta :
      Real.sqrt (2 * zeta) ≤ 2 * Real.rpow zeta (1 / (32 : Error)) := by
    have hzeta16_nonneg : 0 ≤ Real.rpow zeta (1 / (16 : Error)) :=
      Real.rpow_nonneg hzeta_nonneg _
    have hzeta32_sq' :
        (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) =
          Real.rpow zeta (1 / (16 : Error)) := hzeta32_sq
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · calc
        2 * zeta ≤ 4 * Real.rpow zeta (1 / (16 : Error)) := by
          nlinarith [hzeta_le_sixteenth, hzeta16_nonneg]
        _ = (2 * Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) := by
          rw [mul_pow, hzeta32_sq']
          norm_num
  have hzeta32_le_sum : Real.rpow zeta (1 / (32 : Error)) ≤ thirtysecondSum := by
    have htail : 0 ≤ Real.rpow gamma (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      exact add_nonneg hgamma32_nonneg hratio32_nonneg
    dsimp [thirtysecondSum]
    rw [show gamma ^ (1 / (32 : Error)) + zeta ^ (1 / (32 : Error)) +
        (((params.d : Error) / (params.q : Error))) ^ (1 / (32 : Error)) =
        zeta ^ (1 / (32 : Error)) +
          (gamma ^ (1 / (32 : Error)) +
            (((params.d : Error) / (params.q : Error))) ^ (1 / (32 : Error))) by ring]
    exact (le_add_of_nonneg_right htail :
      Real.rpow zeta (1 / (32 : Error)) ≤ Real.rpow zeta (1 / (32 : Error)) +
        (Real.rpow gamma (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))))
  have hfirst :
      (k : Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    calc
      (k : Error) * (2 * Real.sqrt (2 * zeta))
          ≤ (k : Error) * (2 * (2 * Real.rpow zeta (1 / (32 : Error)))) := by
            gcongr
      _ = 4 * (k : Error) * Real.rpow zeta (1 / (32 : Error)) := by ring
      _ ≤ 4 * (k : Error) * ((params.m : Error) * thirtysecondSum) := by
            have hzeta32_le_msum :
                Real.rpow zeta (1 / (32 : Error)) ≤
                  (params.m : Error) * thirtysecondSum := by
              calc
                Real.rpow zeta (1 / (32 : Error)) ≤ thirtysecondSum := hzeta32_le_sum
                _ = 1 * thirtysecondSum := by ring
                _ ≤ (params.m : Error) * thirtysecondSum := by
                      exact mul_le_mul_of_nonneg_right hm_ge_one hthirtysecond_nonneg
            gcongr
      _ = 4 * (k : Error) * (params.m : Error) * thirtysecondSum := by ring
  have hcomm_sqrt :
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k) ≤
        21 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    have hright_nonneg : 0 ≤ 21 * (k : Error) * (params.m : Error) * thirtysecondSum := by
      positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hright_nonneg
    · have hm_sq_ge : (params.m : Error) ≤ (params.m : Error) ^ (2 : ℕ) := by
        nlinarith [hm_ge_one]
      calc
        commuteGHalfSandwichError params gamma zeta k
            = 426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * sixteenthSum := by
              simp [commuteGHalfSandwichError, sixteenthSum]
        _ ≤ 441 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
              norm_num
        _ ≤ 441 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
        _ = (21 * (k : Error) * (params.m : Error) * thirtysecondSum) ^ (2 : ℕ) := by
              ring
  have hsecond :
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k) ≤
        42 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    nlinarith [hcomm_sqrt]
  by_cases hk0 : k = 0
  · subst k
    simp [fromHToGPaperTotalError, fromHToGRecurrenceError, fromHToGError]
  have hk_ge_one_nat : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
  have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_ge_one_nat
  have hk_le_sq : (k : Error) ≤ (k : Error) ^ (2 : ℕ) := by nlinarith
  have hfirst_quad :
      (k : Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
    have hmul :
        4 * (k : Error) * (params.m : Error) * thirtysecondSum ≤
          4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
      have hcoeff_nonneg : 0 ≤ 4 * (params.m : Error) * thirtysecondSum := by positivity
      have hmul' := mul_le_mul_of_nonneg_left hk_le_sq hcoeff_nonneg
      nlinarith
    exact le_trans hfirst hmul
  have hsecond_quad :
      (k : Error) * (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k)) ≤
        42 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
    have hmul := mul_le_mul_of_nonneg_left hsecond hk_nonneg
    nlinarith
  calc
    fromHToGPaperTotalError params gamma zeta k
        = (k : Error) * (2 * Real.sqrt (2 * zeta)) +
            (k : Error) * (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k)) := by
          simp [fromHToGPaperTotalError, fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring
    _ ≤ 4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum +
          42 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
          exact add_le_add hfirst_quad hsecond_quad
    _ = fromHToGError params gamma zeta k := by
          simp [fromHToGError, thirtysecondSum]
          ring

end MIPStarRE.LDT.Pasting
