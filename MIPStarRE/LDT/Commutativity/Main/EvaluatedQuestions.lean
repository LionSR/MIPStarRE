import MIPStarRE.LDT.Commutativity.Main.Auxiliary

/-!
# Section 11 commutativity: evaluated-question transport

Core Schwartz–Zippel transport on the evaluated-question space, comparing
full-polynomial and point-evaluated outcomes.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Core Schwartz-Zippel transport on the evaluated-question space.

This is the substantive remaining step: compare the full polynomial outcomes
with their point-evaluated postprocessings while paying the two `md/q`
Schwartz-Zippel losses and the self-consistency bookkeeping. -/
lemma fullSliceCommutation_of_evaluated_on_evaluated_questions
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (comMainError params gamma zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  theorem `thm:com-main`, especially the passage from
  `eq:evaluate-gcom-at-points` to `eq:evaluate-gcom-at-points-part-dos`
  and the final displayed error estimate.

  The paper-faithful transport below passes from the full polynomial products
  down to the evaluated products on the sampled points.

  The paper first reduces to the small-parameter regime
  `γ ≤ 1`, `ζ ≤ 1`, and `d / q ≤ 1`; otherwise `comMainError` is already large
  enough while the raw `sddErrorOp` is trivially bounded.

  In the small-parameter case, the proof uses two Schwartz-Zippel
  marginalizations together with `closenessOfIP` and the evaluated
  commutation estimate obtained from `hEval`, producing the displayed error
  chain that is then absorbed into `comMainError`.
  -/
  -- WLOG: reduce to the small-parameter regime (paper lines 260–276).
  -- When max(γ, ζ, d/q) ≥ 1, comMainError ≥ 30m ≥ 30 while
  -- sddErrorOp ≤ 4 by the sub-measurement bound, so the inequality
  -- holds trivially.
  by_cases hsmall :
      gamma ≤ 1 ∧ zeta ≤ 1 ∧
        (↑params.d : Error) / (↑params.q : Error) ≤ 1
  · -- Small-parameter case: γ, ζ, d/q ≤ 1.
    obtain ⟨hgamma_le, hzeta_le, hdq_le⟩ := hsmall
    -- Step 1: The Schwartz-Zippel transport.
    -- Bound the full-product sddErrorOp by corrections from:
    -- (a) The x switch-sandwich transport (`4√ζ`) and the y scalar
    --     marginalization (`2md/q + 4√ζ`)
    -- (b) The evaluated commutation via the strong `hEval` transport
    --     (≤ √(commDataProcessedGError))
    -- giving total ≤ 16√ζ + 4md/q + 2√(commDataProcessedGError).
    --
    -- Proof sketch:
    -- * Expand qSDDOp into quartic trace terms
    --   (BAB + ABA - BABA - ABAB) using projectivity
    -- * Use BAB = ABA and BABA = ABAB symmetry (swap x↔y, g↔h)
    -- * For each of ABA and ABAB, apply the marginalization chain
    --   to relate full-polynomial sums to evaluated sums
    -- * Use submeasurement bounds (Σ_g G^x_g ≤ I) to control
    --   quartic terms: ABA ≤ 1
    -- * The ABAB term uses hEval through closenessOfIP to obtain
    --   √(commDataProcessedGError)
    have hTransport :
        sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q)) ≤
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (commDataProcessedGError params gamma zeta) := by
      -- Compose the four scalar lemmas.  Paper chain:
      -- * `fullSliceCommutation_qSDDOp_avg_eq` rewrites the pulled-back
      --   `sddErrorOp` as `2 · (fullABA − fullABAB)` (paper lines 286-290).
      -- * Triangle on the real line:
      --     `|fullABA − fullABAB|
      --        ≤ |fullABA − evalABA| + |evalABA − evalABAB|
      --          + |evalABAB − fullABAB|`
      -- * `fullSlice_scalar_marginalize_x`: the first-term switch-sandwich
      --   wrapper costs `4√ζ`.
      -- * `fullSlice_scalar_marginalize_y`: the paper-faithful second-term
      --   wrapper splits into the proved x-prefix `md/q + √ζ`, the proved
      --   line-359 bridge `√ζ`, the proved line-360 bridge `√ζ`, and the proved
      --   y-tail `md/q + √ζ`, for a total of `2md/q + 4√ζ`.
      -- * `fullSlice_closenessOfIP_CAB_hEval_sqrt`: the direct evaluated-side
      --   route gives `|evalABA − evalABAB| ≤ √ν`.
      -- Summing gives `|fullABA − fullABAB| ≤ 8√ζ + 2(md/q) + √ν`,
      -- and multiplying by `2` produces `16√ζ + 4(md/q) + 2√ν`.
      have hExpand :=
        fullSliceCommutation_qSDDOp_avg_eq params strategy family
      have hMargX :=
        fullSlice_scalar_marginalize_x params strategy family zeta hnorm hself
      have hMargY :=
        fullSlice_scalar_marginalize_y params strategy family zeta hnorm hself
      have hClose :=
        fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta
          hnorm hEval
      -- Triangle inequality on the three intermediate quantities.
      have hTri :
          |fullSliceABAAvg params strategy family -
              fullSliceABABAvg params strategy family| ≤
            |fullSliceABAAvg params strategy family -
                evaluatedSliceABAAvg params strategy family| +
              |evaluatedSliceABAAvg params strategy family -
                  evaluatedSliceABABAvg params strategy family| +
              |evaluatedSliceABABAvg params strategy family -
                  fullSliceABABAvg params strategy family| := by
        have h1 :
            fullSliceABAAvg params strategy family -
                fullSliceABABAvg params strategy family =
              (fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family) +
                (evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family) := by
          ring
        calc
          |fullSliceABAAvg params strategy family -
              fullSliceABABAvg params strategy family|
            = |(fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family) +
                (evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family)| := by
                  rw [h1]
          _ ≤ |(fullSliceABAAvg params strategy family -
                  evaluatedSliceABAAvg params strategy family) +
                (evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family)| +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family| :=
                abs_add_le _ _
          _ ≤ (|fullSliceABAAvg params strategy family -
                    evaluatedSliceABAAvg params strategy family| +
                  |evaluatedSliceABAAvg params strategy family -
                      evaluatedSliceABABAvg params strategy family|) +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family| := by
                gcongr
                exact abs_add_le _ _
      -- Symmetry of `abs`: `|evalABAB - fullABAB| = |fullABAB - evalABAB|`.
      have hMargY' :
          |evaluatedSliceABABAvg params strategy family -
              fullSliceABABAvg params strategy family| ≤
            2 * ((↑params.m : Error) * ↑params.d / ↑params.q) +
              4 * Real.sqrt zeta := by
        rw [abs_sub_comm]
        exact hMargY
      -- `sddErrorOp = 2 · (fullABA − fullABAB) ≤ 2 · |fullABA − fullABAB|`.
      have hTwoAbs :
          sddErrorOp strategy.state
            (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q)) ≤
          2 *
            |fullSliceABAAvg params strategy family -
                fullSliceABABAvg params strategy family| := by
        rw [hExpand]
        have := le_abs_self
          (fullSliceABAAvg params strategy family -
            fullSliceABABAvg params strategy family)
        linarith
      calc
        sddErrorOp strategy.state
            (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
          ≤ 2 *
              |fullSliceABAAvg params strategy family -
                  fullSliceABABAvg params strategy family| := hTwoAbs
        _ ≤ 2 *
              (|fullSliceABAAvg params strategy family -
                    evaluatedSliceABAAvg params strategy family| +
                |evaluatedSliceABAAvg params strategy family -
                    evaluatedSliceABABAvg params strategy family| +
                |evaluatedSliceABABAvg params strategy family -
                    fullSliceABABAvg params strategy family|) := by
              linarith [hTri]
        _ ≤ 2 *
              (4 * Real.sqrt zeta +
                Real.sqrt
                  (commDataProcessedGError params gamma zeta) +
                (2 * ((↑params.m : Error) * ↑params.d / ↑params.q) +
                  4 * Real.sqrt zeta)) := by
              linarith [hMargX, hMargY', hClose]
        _ = 16 * Real.sqrt zeta +
              4 * (↑params.m * ↑params.d / ↑params.q) +
              2 * Real.sqrt
                (commDataProcessedGError params gamma zeta) := by ring
    -- Step 2: Error arithmetic (using small-parameter hypotheses).
    -- Show:
    --   16√ζ + 4md/q + 2√(48m(√γ + √ζ))
    --     ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    --
    -- Key estimates (all require γ, ζ, d/q ≤ 1):
    -- * 2√(48m(√γ + √ζ)) ≤ 2√(48m)(γ^¼ + ζ^¼) ≤ 14m(γ^¼ + ζ^¼)
    --   using √(a+b) ≤ √a + √b and √m ≤ m (for m ≥ 1)
    -- * 16√ζ ≤ 16m·ζ^¼ (ζ ≤ 1 ⇒ ζ^½ ≤ ζ^¼; m ≥ 1)
    -- * 4md/q ≤ 6m(d/q)^¼ (d/q ≤ 1 ⇒ x ≤ x^¼)
    -- * Total: 14m·γ^¼ + 30m·ζ^¼ + 6m·(d/q)^¼
    --         ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    have hArith :
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (commDataProcessedGError params gamma zeta) ≤
        comMainError params gamma zeta := by
      unfold commDataProcessedGError comMainError
      -- Useful numerical facts
      have hm_ge : (1 : Error) ≤ (params.m : Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : Error) < ↑params.q :=
        Nat.cast_pos.mpr params.hq
      have hdq_nn : 0 ≤ (↑params.d : Error) / ↑params.q :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hg4 : 0 ≤ Real.rpow gamma (1 / (4 : Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hz4 : 0 ≤ Real.rpow zeta (1 / (4 : Error)) :=
        Real.rpow_nonneg hzeta_nonneg _
      have hdq4 : 0 ≤ Real.rpow
          ((↑params.d : Error) / ↑params.q) (1 / (4 : Error)) :=
        Real.rpow_nonneg hdq_nn _
      -- Step 1: sqrt ζ ≤ ζ^(1/4)
      have h_sqrt_z : Real.sqrt zeta ≤
          Real.rpow zeta (1 / (4 : Error)) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hzeta_nonneg hzeta_le (by norm_num) (by norm_num)
      -- Step 2: d/q ≤ (d/q)^(1/4)
      have h_dq : (↑params.d : Error) / ↑params.q ≤
          Real.rpow ((↑params.d : Error) / ↑params.q)
            (1 / (4 : Error)) := by
        conv_lhs =>
          rw [show (↑params.d : Error) / ↑params.q =
            Real.rpow ((↑params.d : Error) / ↑params.q) 1
            from (Real.rpow_one _).symm]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hdq_nn hdq_le (by norm_num) (by norm_num)
      -- Step 3: (γ^(1/4))² = γ^(1/2) and (ζ^(1/4))² = ζ^(1/2)
      have hg4_sq :
          (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ) =
            Real.rpow gamma (1 / (2 : Error)) := by
        calc (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ)
            = (Real.rpow gamma (1 / (4 : Error))) ^
                (2 : Error) := by norm_num
          _ = Real.rpow gamma
                (1 / (4 : Error) * 2) := by
              symm; exact Real.rpow_mul hgamma_nonneg _ _
          _ = Real.rpow gamma
                (1 / (2 : Error)) := by norm_num
      have hz4_sq :
          (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ) =
            Real.rpow zeta (1 / (2 : Error)) := by
        calc (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ)
            = (Real.rpow zeta (1 / (4 : Error))) ^
                (2 : Error) := by norm_num
          _ = Real.rpow zeta
                (1 / (4 : Error) * 2) := by
              symm; exact Real.rpow_mul hzeta_nonneg _ _
          _ = Real.rpow zeta
                (1 / (2 : Error)) := by norm_num
      -- Step 4: √(48m(γ^½+ζ^½)) ≤ √(48m)·(γ^¼+ζ^¼)
      -- Using γ^½ = (γ^¼)² and a²+b² ≤ (a+b)²
      have hsqrt_cdpg :
          Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : Error)) +
              Real.rpow zeta (1 / (2 : Error)))) ≤
          Real.sqrt (48 * ↑params.m) *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error))) := by
        rw [← hg4_sq, ← hz4_sq]
        have hsq_le :
            (Real.rpow gamma (1 / (4 : Error))) ^ (2 : ℕ) +
              (Real.rpow zeta (1 / (4 : Error))) ^ (2 : ℕ) ≤
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error))) ^
                (2 : ℕ) := by
          nlinarith [hg4, hz4]
        calc Real.sqrt (48 * ↑params.m *
              ((Real.rpow gamma (1 / (4 : Error))) ^
                  (2 : ℕ) +
                (Real.rpow zeta (1 / (4 : Error))) ^
                  (2 : ℕ)))
            ≤ Real.sqrt (48 * ↑params.m *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) ^ (2 : ℕ)) := by
              apply Real.sqrt_le_sqrt
              exact mul_le_mul_of_nonneg_left hsq_le
                (by positivity)
          _ = Real.sqrt (48 * ↑params.m) *
                Real.sqrt
                  ((Real.rpow gamma (1 / (4 : Error)) +
                    Real.rpow zeta
                      (1 / (4 : Error))) ^
                    (2 : ℕ)) := by
              rw [Real.sqrt_mul (by positivity)]
          _ = Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by
              rw [Real.sqrt_sq (by linarith)]
      -- Step 5: 2·√(48m) ≤ 14m (since 192m ≤ 196m²
      --   for m ≥ 1)
      have hsqrt_48m :
          Real.sqrt (48 * ↑params.m) ≤
            7 * ↑params.m := by
        rw [show 7 * (↑params.m : Error) =
          Real.sqrt ((7 * ↑params.m) ^ 2) from
          (Real.sqrt_sq (by linarith)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [hm_ge]
      -- Combine the three parts
      have hA : 16 * Real.sqrt zeta ≤
          16 * ↑params.m *
            Real.rpow zeta (1 / (4 : Error)) := by
        nlinarith [h_sqrt_z, hm_ge, hz4]
      have hB :
          4 * (↑params.m * ↑params.d / ↑params.q) ≤
          6 * ↑params.m * Real.rpow
            ((↑params.d : Error) / ↑params.q)
            (1 / (4 : Error)) := by
        have hrw :
            ↑params.m * ↑params.d / ↑params.q =
              ↑params.m *
                ((↑params.d : Error) / ↑params.q) := by
          ring
        rw [hrw]
        nlinarith [h_dq, hm_ge, hdq4]
      have hC :
          2 * Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : Error)) +
              Real.rpow zeta (1 / (2 : Error)))) ≤
          14 * ↑params.m *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta
                (1 / (4 : Error))) := by
        calc 2 * Real.sqrt (48 * ↑params.m *
              (Real.rpow gamma (1 / (2 : Error)) +
                Real.rpow zeta (1 / (2 : Error))))
            ≤ 2 * (Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error)))) :=
              mul_le_mul_of_nonneg_left hsqrt_cdpg
                (by norm_num)
          _ = 2 * Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by ring
          _ ≤ 14 * ↑params.m *
                (Real.rpow gamma (1 / (4 : Error)) +
                  Real.rpow zeta
                    (1 / (4 : Error))) := by
              exact mul_le_mul_of_nonneg_right
                (by linarith [hsqrt_48m])
                (by linarith)
      -- 14m·g4 + 30m·z4 + 6m·dq4 ≤ 30m·(g4+z4+dq4)
      nlinarith [hA, hB, hC, hg4, hz4, hdq4, hm_ge]
    exact ⟨le_trans hTransport hArith⟩
  · -- Large-parameter case: max(γ, ζ, d/q) > 1.
    -- The bound is trivial: sddErrorOp ≤ 4 (by the triangle
    -- inequality for vectors and the sub-measurement property;
    -- paper lines 263–271), while comMainError ≥ 30m ≥ 30 > 4
    -- (since rpow x (1/4) ≥ 1 when x ≥ 1, and m ≥ 1).
    have hleft :=
      fullSliceProductLeft_to_zero_le_one params strategy family hnorm
    have hright :=
      zero_to_fullSliceProductRight_le_one params strategy family hnorm
    have hfour :
        SDDOpRel strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          4 := by
      have htri :=
        MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
          strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => fullSliceProductLeft params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          (fun _ => zeroFullSliceOpFamily (ι := ι) params)
          (fun q => fullSliceProductRight params strategy family
            (fullSliceQuestionOfEvaluatedSlice params q))
          1 1 hleft hright
      refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
        strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (2 * (1 + 1)) 4 ?_ htri
      norm_num
    have hcom_ge_four : 4 ≤ comMainError params gamma zeta := by
      unfold comMainError
      have hm_ge : (1 : Error) ≤ (params.m : Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : Error) < (params.q : Error) := Nat.cast_pos.mpr params.hq
      have hdq_nonneg : 0 ≤ (params.d : Error) / (params.q : Error) :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hnotsmall :
          1 < gamma ∨ 1 < zeta ∨ 1 < (params.d : Error) / (params.q : Error) := by
        have : ¬ (gamma ≤ 1 ∧ zeta ≤ 1 ∧
            (params.d : Error) / (params.q : Error) ≤ 1) := hsmall
        by_cases hg : gamma ≤ 1
        · by_cases hz : zeta ≤ 1
          · by_cases hdq : (params.d : Error) / (params.q : Error) ≤ 1
            · exact False.elim (this ⟨hg, hz, hdq⟩)
            · exact Or.inr <| Or.inr <| lt_of_not_ge hdq
          · exact Or.inr <| Or.inl <| lt_of_not_ge hz
        · exact Or.inl <| lt_of_not_ge hg
      have hsum_ge_one :
          1 ≤
            Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
        rcases hnotsmall with hg | hz | hdq
        · have hγ : 1 ≤ Real.rpow gamma (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hg.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : Error)) := Real.rpow_nonneg hzeta_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hζ : 1 ≤ Real.rpow zeta (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hz.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hdq' :
              1 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
            simpa using Real.one_le_rpow hdq.le (show (0 : Error) ≤ 1 / (4 : Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : Error)) := Real.rpow_nonneg hzeta_nonneg _
          linarith
      calc
        (4 : Error) ≤ 30 := by norm_num
        _ ≤ 30 * (params.m : Error) := by nlinarith
        _ ≤ 30 * (params.m : Error) *
            (Real.rpow gamma (1 / (4 : Error)) +
              Real.rpow zeta (1 / (4 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))) := by
                nlinarith
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      4 (comMainError params gamma zeta) hcom_ge_four hfour

end MIPStarRE.LDT.Commutativity
