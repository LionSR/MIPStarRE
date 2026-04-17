import MIPStarRE.LDT.Commutativity.Transport

/-!
# Section 11 commutativity: final theorems

Final full-slice commutation and `comMain` conclusions.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354).

Schwartz-Zippel marginalization on the `x` variable: replacing the full
polynomial sum `∑_g G^x_g` by the point-evaluated sum `E_u ∑_a G^x_[g(u)=a]`
inside the ABA term costs at most `params.m · params.d / params.q`.

TODO(#361): apply `schwartzZippel_individualDegree` from
`MIPStarRE/LDT/Preliminaries/Polynomials.lean` to the polynomial-agreement
collision term `1[g(u) = g'(u)]`, then bound the off-diagonal fiber sum using
the sub-measurement property of `G^x`. -/
private lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Paper `eq:evaluate-gcom-at-points-part-dos`
(`commutativity-G.tex` lines 369-385).

Schwartz-Zippel marginalization on the `y` variable: replacing the full
polynomial sum `∑_h G^y_h` by the point-evaluated sum `E_v ∑_b G^y_[h(v)=b]`
inside the ABAB term costs at most `params.m · params.d / params.q`.  Symmetric
in structure to `fullSlice_scalar_marginalize_x`; the paper's difference-
expression label at line 379 is idiosyncratic, so we cite the enclosing
approximation statement. -/
private lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396).

Using `hEval` together with the six `closenessOfIP` steps in the paper:
two on the ABA side (line 301: `2√ζ`) and four on the ABAB side
(line 334: `√ζ`, lines 359-360: `2√ζ`, line 396: `√ζ`), plus the final
`closenessOfIP` with `hEval` as the `A≈B` input (line 394: `√ν_evaluation`),
the evaluated-slice scalar commutator is bounded by
`6√ζ + √(commDataProcessedGError)`.

The `hEval` hypothesis is bound into the fourth step via
`fullSlice_closenessOfIP_CAB_hEval` inputs; the first six steps use
`item:commuting-self-consistency` from `_hself`.

TODO(#361): invoke `closenessOfIP` (`Preliminaries/CauchySchwarz.lean:342`) six
times, each with `normalizationCondition_sandwich_bound` discharging the `C`
normalization condition, and chain the `√ζ` / `√ν` contributions. -/
private lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hgamma_nonneg : 0 ≤ gamma) (_hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) := by
  sorry

-- Heavy sqrt/rpow arithmetic in hArith step.
set_option maxHeartbeats 800000 in
/-- Core Schwartz-Zippel transport on the evaluated-question space.

This is the substantive remaining step: compare the full polynomial outcomes
with their point-evaluated postprocessings while paying the two `md/q`
Schwartz-Zippel losses and the self-consistency bookkeeping. -/
private lemma fullSliceCommutation_of_evaluated_on_evaluated_questions
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
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

  The remaining work is the paper-faithful transport from the full polynomial
  products down to the evaluated products on the sampled points.

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
    -- (a) Two Schwartz-Zippel marginalizations (each ≤ md/q)
    -- (b) Multiple closenessOfIP applications (each ≤ √ζ)
    -- (c) The evaluated commutation via closenessOfIP
    --     (≤ √(commDataProcessedGError))
    -- giving total ≤ 12√ζ + 4md/q + 2√(commDataProcessedGError).
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
        12 * Real.sqrt zeta +
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
      -- * `fullSlice_scalar_marginalize_x`: `|fullABA − evalABA| ≤ md/q`
      --   (paper line 342).
      -- * `fullSlice_scalar_marginalize_y`: `|fullABAB − evalABAB| ≤ md/q`
      --   (paper line 373).
      -- * `fullSlice_closenessOfIP_CAB_hEval`: using `hEval` and the six
      --   `closenessOfIP` steps on the evaluated side,
      --   `|evalABA − evalABAB| ≤ 6√ζ + √ν` (paper lines 301, 334, 359-360,
      --   394, 396).
      -- Summing gives `|fullABA − fullABAB| ≤ 6√ζ + 2(md/q) + √ν`,
      -- and multiplying by `2` produces `12√ζ + 4(md/q) + 2√ν`.
      have hExpand :=
        fullSliceCommutation_qSDDOp_avg_eq params strategy family
      have hMargX :=
        fullSlice_scalar_marginalize_x params strategy family
      have hMargY :=
        fullSlice_scalar_marginalize_y params strategy family
      have hClose :=
        fullSlice_closenessOfIP_CAB_hEval params strategy family gamma zeta
          hgamma_nonneg hzeta_nonneg _hself hEval
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
            (↑params.m : Error) * ↑params.d / ↑params.q := by
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
              (((↑params.m : Error) * ↑params.d / ↑params.q) +
                (6 * Real.sqrt zeta +
                  Real.sqrt
                    (commDataProcessedGError params gamma zeta)) +
                ((↑params.m : Error) * ↑params.d / ↑params.q)) := by
              have := abs_nonneg
                (fullSliceABAAvg params strategy family -
                  fullSliceABABAvg params strategy family)
              linarith [hMargX, hMargY', hClose]
        _ = 12 * Real.sqrt zeta +
              4 * (↑params.m * ↑params.d / ↑params.q) +
              2 * Real.sqrt
                (commDataProcessedGError params gamma zeta) := by ring
    -- Step 2: Error arithmetic (using small-parameter hypotheses).
    -- Show:
    --   12√ζ + 4md/q + 2√(48m(√γ + √ζ))
    --     ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    --
    -- Key estimates (all require γ, ζ, d/q ≤ 1):
    -- * 2√(48m(√γ + √ζ)) ≤ 2√(48m)(γ^¼ + ζ^¼) ≤ 14m(γ^¼ + ζ^¼)
    --   using √(a+b) ≤ √a + √b and √m ≤ m (for m ≥ 1)
    -- * 12√ζ ≤ 12ζ^¼ ≤ 12m·ζ^¼ (ζ ≤ 1 ⇒ ζ^½ ≤ ζ^¼; m ≥ 1)
    -- * 4md/q ≤ 4m(d/q)^¼ (d/q ≤ 1 ⇒ x ≤ x^¼)
    -- * Total: 14m·γ^¼ + 26m·ζ^¼ + 4m·(d/q)^¼
    --         ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    have hArith :
        12 * Real.sqrt zeta +
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
      have hA : 12 * Real.sqrt zeta ≤
          12 * ↑params.m *
            Real.rpow zeta (1 / (4 : Error)) := by
        nlinarith [h_sqrt_z, hm_ge, hz4]
      have hB :
          4 * (↑params.m * ↑params.d / ↑params.q) ≤
          4 * ↑params.m * Real.rpow
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
      -- 14m·g4 + 26m·z4 + 4m·dq4 ≤ 30m·(g4+z4+dq4)
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

/-- The remaining `thm:com-main` lift from evaluated commutation back to
full-slice commutation.

This is the paper's two-step Schwartz-Zippel marginalization argument:
first compare `G^x_g` with `G^x_[g(u)=a]`, then compare `G^y_h` with
`G^y_[h(v)=b]`, while using slice strong self-consistency to move between the
full and evaluated placements and finally absorb the scalar bookkeeping into
`comMainError`. -/
private lemma fullSliceCommutation_of_evaluated
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta) := by
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta
        hnorm hgamma_nonneg hzeta_nonneg _hself hEval)

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family G gamma zeta := by
  let hEval :=
    commDataProcessedG params strategy eps delta gamma zeta hnorm hgood family G
      hG hcons hself hbound
  have hSpecialized :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) := by
    constructor
    rw [evaluationSpecialization_sddErrorOp_eq]
    exact hEval.evaluatedSliceCommutation.squaredDistanceBound
  have hzeta_nonneg : 0 ≤ zeta :=
    le_trans (sddError_nonneg _ _ _ _)
      hself.sliceSelfConsistency.squaredDistanceBound
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ =>
          bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  refine
    { evaluatedCommutation := hEval
      evaluationSpecialization := hSpecialized
      fullSliceCommutation := by
        exact
          fullSliceCommutation_of_evaluated
            params strategy family gamma zeta
            hnorm hgamma_nonneg hzeta_nonneg
            hself hSpecialized }

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) :
    NormalizationConditionStatement P Q := by
  have hherm :
      ∀ a : OutcomeA,
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp <|
        by
          simpa [normalizationConditionSandwichedTotalOperator] using
            SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
      ).isHermitian.eq
  refine
    { sandwichedHermitianSquare := ?_
      sandwichedBoundedByIdentity := ?_ }
  · simp [normalizationConditionAdjointSquareOperator,
      normalizationConditionSquareOperator,
      normalizationConditionAdjointSquareFamily,
      normalizationConditionSquareFamily, hherm]
  · simpa [normalizationConditionSquareOperator, normalizationConditionIdentityBound] using
      (normalizationConditionSquareFamily P Q).total_le_one


end MIPStarRE.LDT.Commutativity
