import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.BadMass
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Averaging

/-!
# Line interpolation: H-B consistency error aggregation

Fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds,
and the final bad-mass aggregation lemma that drives `lem:h-b-consistency`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hBConsistency_fixed_u_defect_le_avgOver_distinct
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy u) ≤
        avgOver (distinctTupleDistribution params k)
          (fun xs =>
            qBipartiteConsDefect strategy.state
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u)) := by
  have hleft :
      hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u =
        averageIdxSubMeas
          (distinctTupleDistribution params k)
          (fun xs => hRestrictionToVerticalLine params (
              pastedInterpolationFamily params family k xs) u)
          (distinctTupleDistribution_weight_sum_le_one params k) := by
    simpa [constructedPastedSubMeas] using
      hRestrictionToVerticalLine_averageIdxSubMeas (params := params) u
        (distinctTupleDistribution params k)
        (pastedInterpolationFamily params family k)
        (distinctTupleDistribution_weight_sum_le_one params k)
  rw [hleft]
  exact qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
    (distinctTupleDistribution params k)
    (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
    (verticalLineMeasurementFamily params strategy u)
    (distinctTupleDistribution_weight_sum_le_one params k)

lemma hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add
    (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) :
    hBConsistencyError params eps delta gamma zeta k =
      (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  simp [hBConsistencyError, ldSandwichLineOnePointError]
  ring

lemma avgOver_sum_fin
    {α : Type*} (𝒟 : Distribution α) (k : ℕ) (f : α → Fin k → Error) :
    avgOver 𝒟 (fun a => ∑ i : Fin k, f a i) =
      ∑ i : Fin k, avgOver 𝒟 (fun a => f a i) :=
  avgOver_sum 𝒟 f

lemma one_div_q_le_rpow_degreeRatio
    (params : Parameters) [FieldModel params.q]
    (hd : 0 < params.d) :
    1 / (params.q : Error)
      ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
  let x : Error := ((params.d : Error) / (params.q : Error))
  have hq_pos : 0 < (params.q : Error) := by exact_mod_cast params.hq
  have hx_nonneg : 0 ≤ x := by positivity
  have hqx : 1 / (params.q : Error) ≤ x := by
    have hd_ge_one : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
    simpa [x] using div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  by_cases hx_le_one : x ≤ 1
  · have hx_le_rpow : x ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hx_nonneg hx_le_one (by norm_num : 0
            ≤ (1 / (32 : Error)))
          (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
    exact le_trans hqx hx_le_rpow
  · have h1_le_x : (1 : Error) ≤ x := le_of_not_ge hx_le_one
    have hq_le_one : 1 / (params.q : Error) ≤ 1 := by
      have hq_ge_one : (1 : Error) ≤ (params.q : Error) := by exact_mod_cast params.hq
      have hq_ne : (params.q : Error) ≠ 0 := by positivity
      field_simp [hq_ne]
      nlinarith
    have h1_le_rpow : (1 : Error) ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow (show 0 ≤ (1 : Error) by positivity) h1_le_x (show 0
            ≤ (1 / (32 : Error)) by positivity))
    exact le_trans hq_le_one h1_le_rpow

lemma dnoteq_term_le_hBConsistency_extra
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hqterm : 1 / (params.q : Error) ≤ S := by
    have hlast := one_div_q_le_rpow_degreeRatio params hd
    have htail_nonneg :
        0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (Real.rpow_nonneg heps_nonneg _)
            (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hgamma_nonneg _))
        (Real.rpow_nonneg hzeta_nonneg _)
    dsimp [S] at *
    nlinarith
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hS_le_mS : S ≤ (params.m : Error) * S := by
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
    nlinarith
  have hqterm' : 1 / (params.q : Error) ≤ (params.m : Error) * S :=
    le_trans hqterm hS_le_mS
  have hk_nonneg : 0 ≤ ((k : Error) ^ (2 : ℕ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hqterm' hk_nonneg
  simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma hBConsistency_error_bound
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ hBConsistencyError params eps delta gamma zeta k := by
  rw [hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add]
  have hextra := dnoteq_term_le_hBConsistency_extra params eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

lemma avgOver_distinct_pasted_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      qBipartiteConsDefect strategy.state
        (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
        (verticalLineMeasurementFamily params strategy u))
      ≤ avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  have hsupport : (distinctTupleDistribution params k).support = support := by
    simp [distinctTupleDistribution, support]
  have hweight :
      ∀ xs, (distinctTupleDistribution params k).weight xs =
        if xs ∈ support then 1 / (support.card : Error) else 0 := by
    intro xs
    simp [distinctTupleDistribution, support]
  unfold avgOver
  rw [hsupport]
  simp_rw [hweight]
  refine Finset.sum_le_sum ?_
  intro xs hxs
  have hinj : Function.Injective xs := (Finset.mem_filter.mp hxs).2
  simp only [hxs, one_div, ite_true]
  exact mul_le_mul_of_nonneg_left
    (pastedInterpolation_verticalLine_defect_le_badMass params strategy family u xs hinj)
    (by positivity)

lemma avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
            exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
              (fun xs => hBConsistencyBadMass params strategy family u xs)
              (fun xs => hBConsistencyBadMass_nonneg params strategy family u xs)
              (fun xs => hBConsistencyBadMass_le_one params strategy family u xs)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            gcongr
            exact ldDnoteq params k

lemma avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
  let defect : Fin k → SandwichedLineQuestion params k → Error := fun i q =>
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            ∑ i : Fin k, defect i (u, xs))) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_mono _ _ _ (fun xs =>
                hBConsistencyBadMass_le_linePointDefectSum params strategy family u xs))
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ i : Fin k,
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          apply avgOver_congr
          intro u
          exact avgOver_sum_fin (uniformDistribution (PointTuple params k)) k
            (fun xs i => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          exact avgOver_sum_fin (uniformDistribution (Point params)) k
            (fun u i => avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs)))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k))
            (fun q => defect i q) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [SandwichedLineQuestion] using
            (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ i : Fin k, ldSandwichLineOnePointError params eps delta gamma zeta k := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact (hline i.1 i.2).linePointComparison.offDiagonalBound
    _ = (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
          simp

/-- Aggregate the one-point line comparison statements over all inserted vertical
lines and absorb the distinct-tuple loss into the displayed `hBConsistency`
error.

This is the reusable bad-mass aggregation from `ld-pasting.tex` lines
1186--1202 (also used in the proof of `lem:h-b-consistency`). -/
lemma avgOver_distinct_badMass_le_hBConsistencyError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs)) ≤
      hBConsistencyError params eps delta gamma zeta k := by
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error)) := by
          exact avgOver_mono _ _ _ (fun u =>
            avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
              params strategy family u)
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          rw [avgOver_add]
          simpa using avgOver_uniform_const (α := Point params)
            (((k : Error) ^ (2 : ℕ)) / (params.q : Error))
    _ ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          gcongr
          exact avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
            params strategy family eps delta gamma zeta k hline
    _ ≤ hBConsistencyError params eps delta gamma zeta k := by
          exact hBConsistency_error_bound params eps delta gamma zeta k hd
            heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

end MIPStarRE.LDT.Pasting
