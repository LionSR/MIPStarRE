import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Preliminaries.Triangles.Consistency

/-!
# Section 12 pasting: core bounds

Initial pasting bounds and scalar estimates.

## References

- arXiv:2009.12982, Section 12 (pasting).
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lem:ld-gbcon`.

This is the direct consistency transfer from the slice family `G^x` to the
vertical line answers `B^u`, obtained by composing the hypothesis
`item:ld-pasting-consistency` with the conditioned axis-parallel test relation. -/
theorem ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let 𝒟 := uniformDistribution (Point params.next)
  let μ : Error := ((params.next.m : ℕ) : Error) * eps
  let ν : Error := 8 * (params.m : Error) * eps + 4 * delta
  let pointSub : IdxSubMeas (Point params.next) (Fq params) ι :=
    IdxProjMeas.toIdxSubMeas strategy.pointMeasurement
  let rawMeas : IdxMeas (Point params.next) (Fq params) ι :=
    rawVerticalLineMeasurementFamily params strategy
  let rawSub : IdxSubMeas (Point params.next) (Fq params) ι :=
    rawVerticalLineAnswerFamily params strategy
  let pointL : IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
    IdxSubMeas.liftLeft pointSub
  let pointR : IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
    IdxSubMeas.liftRight pointSub
  let rawL : IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
    IdxSubMeas.liftLeft rawSub
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hraw_cons :
      ConsRel strategy.state 𝒟 pointSub rawSub μ := by
    simpa [𝒟, μ, pointSub, rawMeas, rawSub] using
      rawVerticalLineConsistency params strategy eps delta gamma hgood
  have hraw_cons_swap :
      ConsRel strategy.state 𝒟 rawSub pointSub μ :=
    PermInvState.consRel_swap strategy.permInvState 𝒟 pointSub rawSub μ hraw_cons
  have hraw_approx :
      Preliminaries.BipartiteSDDRel strategy.state 𝒟 rawSub pointSub (2 * μ) := by
    simpa [𝒟, μ, pointSub, rawMeas, rawSub] using
      (Preliminaries.simeqToApprox strategy.state 𝒟 rawMeas
        (IdxProjMeas.toIdxMeas strategy.pointMeasurement) μ hraw_cons_swap)
  have hraw_sdd_leftRight :
      SDDRel strategy.state 𝒟 rawL pointR (2 * μ) := by
    exact ⟨hraw_approx.leftRightSquaredDistanceBound⟩
  have hraw_sdd_rightLeft :
      SDDRel strategy.state 𝒟 pointR rawL (2 * μ) := by
    exact Preliminaries.sddRel_symm strategy.state 𝒟 rawL pointR (2 * μ)
      hraw_sdd_leftRight
  have hself_rel : BipartiteSSCRel strategy.state 𝒟 pointSub delta :=
    ⟨hgood.selfConsistencyTest⟩
  have hself_sdd : SDDRel strategy.state 𝒟 pointL pointR (2 * delta) := by
    exact Preliminaries.twoNotionsOfSelfConsistency strategy.state 𝒟 pointSub delta
      ⟨strategy.permInvState, hself_rel⟩
  have hpoint_raw_sdd_raw :
      SDDRel strategy.state 𝒟 pointL rawL (2 * ((2 * delta) + (2 * μ))) := by
    exact Preliminaries.stateDependentDistanceRel_triangle strategy.state 𝒟
      pointL pointR rawL (2 * delta) (2 * μ) hself_sdd hraw_sdd_rightLeft
  have hnext_le_nat : params.next.m ≤ 2 * params.m := by
    have hm1 : 1 ≤ params.m := Nat.succ_le_of_lt params.hm
    simpa [Parameters.next, two_mul, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hm1 params.m
  have hnext_le : ((params.next.m : ℕ) : Error) ≤ 2 * (params.m : Error) := by
    exact_mod_cast hnext_le_nat
  have hpoint_raw_sdd_le : 2 * ((2 * delta) + (2 * μ)) ≤ ν := by
    have hraw_le : μ ≤ 2 * (params.m : Error) * eps := by
      exact mul_le_mul_of_nonneg_right hnext_le heps_nonneg
    linarith
  have hpoint_raw_sdd : SDDRel strategy.state 𝒟 pointL rawL ν := by
    exact Preliminaries.stateDependentDistanceRel_mono strategy.state 𝒟
      pointL rawL (2 * ((2 * delta) + (2 * μ))) ν hpoint_raw_sdd_le
      hpoint_raw_sdd_raw
  have hraw_family :
      ConsRel strategy.state 𝒟 rawSub family.evaluatedAtNextPoint
        (zeta + Real.sqrt ν) := by
    simpa [𝒟, ν, pointSub, rawMeas, rawSub, pointL, rawL] using
      (Preliminaries.triangleSub strategy.state 𝒟 strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params.next))
        (IdxProjMeas.toIdxMeas strategy.pointMeasurement) rawMeas
        family.evaluatedAtNextPoint zeta ν hcons.pointConsistency hpoint_raw_sdd)
  have hfamily_raw :
      ConsRel strategy.state 𝒟 family.evaluatedAtNextPoint rawSub
        (zeta + Real.sqrt ν) :=
    PermInvState.consRel_swap strategy.permInvState 𝒟 rawSub
      family.evaluatedAtNextPoint (zeta + Real.sqrt ν) hraw_family
  have hfamily_lifted :
      ConsRel strategy.state 𝒟 family.evaluatedAtNextPoint
        (liftedVerticalLineAnswerFamily params strategy)
        (zeta + Real.sqrt ν) := by
    simpa [rawSub, rawVerticalLineAnswerFamily_eq_lifted params strategy] using hfamily_raw
  simpa [𝒟, ν, IdxPolyFamily.evaluatedAtNextPoint, evaluateFiberFamilyAtNextPoint,
    liftedVerticalLineAnswerFamily] using hfamily_lifted

/-- `prop:ld-dnoteq`. -/
theorem ldDnoteq
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  let bad : Finset (PointTuple params k) :=
    { xs ∈ Finset.univ | ¬ Function.Injective xs }
  have hsupport_card : support.card = params.q.descFactorial k := by
    rw [← Fintype.card_coe]
    let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
      Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
    simpa [support, Finset.mem_filter] using
      (Fintype.card_congr e).trans (Fintype.card_embedding_eq)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  have hqpow_ne : ((params.q : Error) ^ k) ≠ 0 := by positivity
  by_cases hk : k ≤ params.q
  · have hsupport_nonempty : support.Nonempty := by
      refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp
      · intro i j hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)
    have hsupport_card_ne : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport_nonempty
    have hsupport_pos : 0 < (support.card : Error) := by
      exact_mod_cast Nat.pos_of_ne_zero hsupport_card_ne
    have hsupport_le_pow_nat : support.card ≤ params.q ^ k := by
      rw [hsupport_card]
      exact Nat.descFactorial_le_pow _ _
    have hweight_le :
        1 / ((params.q : Error) ^ k) ≤ 1 / (support.card : Error) := by
      exact one_div_le_one_div_of_le hsupport_pos
        (by exact_mod_cast hsupport_le_pow_nat)
    have hpartition_card :
        support.card + bad.card = params.q ^ k := by
      simpa [support, bad, PointTuple, Fintype.card_fun, Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (PointTuple params k)))
          (p := fun xs : PointTuple params k => Function.Injective xs))
    have hpartition_cast :
        (support.card : Error) + bad.card = (params.q : Error) ^ k := by
      exact_mod_cast hpartition_card
    have hgood :
        ∑ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      have hconst :
          ∀ xs ∈ support,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
              = (1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k)) := by
        intro xs hxs
        rw [show (uniformDistribution (PointTuple params k)).weight xs =
            1 / ((params.q : Error) ^ k) by
              simp [uniformDistribution, PointTuple, Fintype.card_fin]]
        rw [show (distinctTupleDistribution params k).weight xs =
            if xs ∈ support then 1 / (support.card : Error) else 0 by
              simp [distinctTupleDistribution, support]]
        rw [if_pos hxs]
        rw [abs_of_nonpos (sub_nonpos.mpr hweight_le)]
        ring
      calc
        ∑ xs ∈ support,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
            = ∑ xs ∈ support, ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
                exact Finset.sum_congr rfl hconst
        _ =
            (support.card : Error) *
              ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hsupport_card_ne, hqpow_ne]
    have hbad :
        ∑ xs ∈ bad,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      calc
        ∑ xs ∈ bad,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
            = ∑ xs ∈ bad, (1 / ((params.q : Error) ^ k)) := by
                apply Finset.sum_congr rfl
                intro xs hxs
                have hnotinj : ¬ Function.Injective xs := (Finset.mem_filter.mp hxs).2
                rw [show (uniformDistribution (PointTuple params k)).weight xs =
                    1 / ((params.q : Error) ^ k) by
                      simp [uniformDistribution, PointTuple, Fintype.card_fin]]
                rw [show (distinctTupleDistribution params k).weight xs =
                    if xs ∈ support then 1 / (support.card : Error) else 0 by
                      simp [distinctTupleDistribution, support]]
                rw [if_neg fun hmem => hnotinj ((Finset.mem_filter.mp hmem).2)]
                simp
        _ = (bad.card : Error) / ((params.q : Error) ^ k) := by
              simp [div_eq_mul_inv]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hqpow_ne]
              nlinarith [hpartition_cast]
    have htv_eq :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      rw [totalVariationDistance]
      have hdisj : Disjoint support bad := by
        simpa [support, bad] using
          (Finset.disjoint_filter_filter_not
            (Finset.univ : Finset (PointTuple params k))
            (Finset.univ : Finset (PointTuple params k))
            (fun xs : PointTuple params k => Function.Injective xs))
      have hsupp_union :
          (uniformDistribution (PointTuple params k)).support
            ∪ (distinctTupleDistribution params k).support
            = support ∪ bad := by
        simp [uniformDistribution, distinctTupleDistribution, support, bad,
          Finset.filter_union_filter_not_eq]
      rw [hsupp_union, Finset.sum_union hdisj]
      simp [hgood, hbad]
      ring
    have hratio_prod :
        (support.card : Error) / ((params.q : Error) ^ k)
          = ∏ i ∈ Finset.range k, (((params.q - i : ℕ) : Error) / params.q) := by
      rw [hsupport_card, Nat.descFactorial_eq_prod_range]
      rw [show ((∏ i ∈ Finset.range k, (params.q - i) : ℕ) : Error)
          = ∏ i ∈ Finset.range k, ((params.q - i : ℕ) : Error) by
            rw [Finset.prod_natCast]]
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib]
      simp
    have hfactor :
        ∀ i ∈ Finset.range k,
          (((params.q - i : ℕ) : Error) / params.q) = 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : i ≤ params.q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      rw [Nat.cast_sub hi_le]
      field_simp [hq_ne]
    have hfactor_nonneg :
        ∀ i ∈ Finset.range k, 0 ≤ 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : (i : Error) ≤ params.q := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      have hq_pos : 0 < (params.q : Error) := by positivity
      have hdiv_le_one : (i : Error) / params.q ≤ 1 := by
        have hfrac_le : (i : Error) / params.q ≤ (params.q : Error) / params.q := by
          exact div_le_div_of_nonneg_right hi_le (by positivity)
        have hqq : (params.q : Error) / params.q = 1 := by
          field_simp [hq_ne]
        rw [hqq] at hfrac_le
        exact hfrac_le
      nlinarith
    have hfactor_le_one :
        ∀ i ∈ Finset.range k, 1 - (i : Error) / params.q ≤ 1 := by
      intro i hi
      exact sub_le_self _ (by positivity)
    have hprefix_le_one :
        ∀ i ∈ Finset.range k,
          ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) ≤ 1 := by
      intro i hi
      calc
        ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∏ j ∈ Finset.range k with j < i, (1 : Error) := by
              exact Finset.prod_le_prod
                (fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1)
                (fun j hj => hfactor_le_one j (Finset.mem_filter.mp hj).1)
        _ = 1 := by simp
    have hsum_le :
        ∑ i ∈ Finset.range k,
          ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_nonneg : 0 ≤ (i : Error) / params.q := by positivity
      have hprefix_nonneg :
          0 ≤ ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) := by
        exact Finset.prod_nonneg fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1
      calc
        ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ((i : Error) / params.q) * 1 := by
              exact mul_le_mul_of_nonneg_left (hprefix_le_one i hi) hi_nonneg
        _ = (i : Error) / params.q := by ring
    have hcollision_le :
        1 - ∏ i ∈ Finset.range k, (1 - (i : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      have hprod_expand :=
        (Finset.prod_one_sub_ordered (s := Finset.range k)
          (f := fun i => (i : Error) / params.q))
      rw [hprod_expand]
      nlinarith
    have hsum_id :
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
      calc
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (∑ i ∈ Finset.range k, (i : Error)) / params.q := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
              rw [← Nat.cast_sum]
              simp [Finset.sum_range_id]
    have hsum_sq :
        (((k * (k - 1) / 2 : ℕ) : Error) / params.q)
          ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
      have hnat : k * (k - 1) / 2 ≤ k * k := by
        refine le_trans (Nat.div_le_self _ _) ?_
        exact Nat.mul_le_mul_left k (Nat.sub_le _ _)
      have hcast : (((k * (k - 1) / 2 : ℕ) : Error)) ≤ (k : Error) * k := by
        exact_mod_cast hnat
      simpa [pow_two] using div_le_div_of_nonneg_right hcast (by positivity)
    rw [htv_eq]
    rw [hratio_prod]
    rw [Finset.prod_congr rfl hfactor]
    exact le_trans hcollision_le (by simpa [hsum_id] using hsum_sq)
  · have hkq : params.q < k := lt_of_not_ge hk
    have hsupport_empty : support = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hsupport_card]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hkq
    have htv_eq_half :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 / 2 := by
      rw [totalVariationDistance]
      simp [uniformDistribution, distinctTupleDistribution, support, hsupport_empty]
    have hbound_ge_one : 1 ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
      have hk_pos_nat : 0 < k := lt_trans params.hq hkq
      have hk_ge_q : (params.q : Error) ≤ k := by exact_mod_cast hkq.le
      have hk_sq_ge_q : (params.q : Error) ≤ (k : Error) ^ (2 : ℕ) := by
        have hk_sq_ge_k : (k : Error) ≤ (k : Error) ^ (2 : ℕ) := by
          have hk_one : (1 : Error) ≤ k := by exact_mod_cast hk_pos_nat
          nlinarith
        exact le_trans hk_ge_q hk_sq_ge_k
      calc
        1 = (params.q : Error) / params.q := by
              field_simp [hq_ne]
        _ ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
              exact div_le_div_of_nonneg_right hk_sq_ge_q (by positivity)
    rw [htv_eq_half]
    nlinarith [hbound_ge_one]

/-- `lem:looks-easy-but-took-me-a-while`. -/
lemma looksEasyButTookMeAWhile
    (lambda : Error) (d : ℕ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda * (1 - lambda ^ d)
      ≤ 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) (1 / ((d + 1 : ℕ) : Error)) := by
  by_cases hl_boundary : lambda = 0 ∨ lambda = 1
  · -- Boundary cases `lambda = 0` and `lambda = 1` share the same proof pattern.
    have hz : 0 ≤ (0 : Error) ^ (1 / ((d + 1 : ℕ) : Error)) := Real.zero_rpow_nonneg _
    rcases hl_boundary with hzero | hone
    · subst hzero
      simpa using hz
    · subst hone
      simpa using hz
  · -- Interior case: `lambda ≠ 0` and `lambda ≠ 1`, hence `0 < lambda < 1`.
    push_neg at hl_boundary
    have hlpos : 0 < lambda := lt_of_le_of_ne h0 (Ne.symm hl_boundary.1)
    let e : Error := 1 / ((d + 1 : ℕ) : Error)
    have hd1_ne : (((d + 1 : ℕ) : Error)) ≠ 0 := by positivity
    have he_mul : (((d + 1 : ℕ) : Error)) * e = 1 := by
      dsimp [e]
      field_simp [hd1_ne]
    have he_mul' : e * (((d + 1 : ℕ) : Error)) = 1 := by
      simpa [mul_comm] using he_mul
    have hgeom :
        (∑ i ∈ Finset.range d, lambda ^ i) * (1 - lambda) = 1 - lambda ^ d := by
      simpa [mul_comm] using geom_sum_mul_neg lambda d
    have hsum_le : ∑ i ∈ Finset.range d, lambda ^ i ≤ d := by
      calc
        ∑ i ∈ Finset.range d, lambda ^ i ≤ ∑ _i ∈ Finset.range d, (1 : Error) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact pow_le_one₀ h0 h1
        _ = d := by simp
    have hlin : 1 - lambda ^ d ≤ (d : Error) * (1 - lambda) := by
      rw [← hgeom]
      exact mul_le_mul_of_nonneg_right hsum_le (sub_nonneg.mpr h1)
    have hone_sub_nonneg : 0 ≤ 1 - lambda ^ d := by
      exact sub_nonneg.mpr (pow_le_one₀ h0 h1)
    have hone_sub_le_one : 1 - lambda ^ d ≤ 1 := by
      exact sub_le_self _ (pow_nonneg h0 _)
    have hpow_small : (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := by
      calc
        (1 - lambda ^ d) ^ (d + 1) = (1 - lambda ^ d) ^ d * (1 - lambda ^ d) := by
          rw [pow_succ]
        _ ≤ 1 * (1 - lambda ^ d) := by
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ hone_sub_nonneg hone_sub_le_one)
            hone_sub_nonneg
        _ = 1 - lambda ^ d := by ring
    have hd_nat : d ≤ 2 ^ (d + 1) := by
      refine le_trans (Nat.le_of_lt d.lt_two_pow_self) ?_
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by decide)
    have hd_cast : (d : Error) ≤ (2 : Error) ^ (d + 1) := by
      exact_mod_cast hd_nat
    have hone_rpow_pow : (Real.rpow (1 - lambda) e) ^ (d + 1) = 1 - lambda := by
      rw [← Real.rpow_natCast]
      change ((1 - lambda) ^ e) ^ (((d + 1 : ℕ) : Error)) = 1 - lambda
      rw [← Real.rpow_mul (sub_nonneg.mpr h1)]
      change (1 - lambda) ^ (e * (((d + 1 : ℕ) : Error))) = 1 - lambda
      rw [he_mul', Real.rpow_one]
    have hmain_pow : (1 - lambda ^ d) ^ (d + 1) ≤ (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
      calc
        (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := hpow_small
        _ ≤ (d : Error) * (1 - lambda) := hlin
        _ ≤ (2 : Error) ^ (d + 1) * (1 - lambda) := by
          exact mul_le_mul_of_nonneg_right hd_cast (sub_nonneg.mpr h1)
        _ = (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
          rw [mul_pow, hone_rpow_pow]
    have hroot :
        1 - lambda ^ d ≤ 2 * Real.rpow (1 - lambda) e := by
      exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d)
        (mul_nonneg zero_le_two (Real.rpow_nonneg (sub_nonneg.mpr h1) _)) hmain_pow
    have hlambda_rpow : Real.rpow (lambda ^ (d + 1)) e = lambda := by
      rw [← Real.rpow_natCast]
      change (lambda ^ (((d + 1 : ℕ) : Error))) ^ e = lambda
      rw [← Real.rpow_mul h0]
      change lambda ^ ((((d + 1 : ℕ) : Error)) * e) = lambda
      rw [he_mul, Real.rpow_one]
    have hmul_rpow :
        Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e =
          Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e := by
      exact Real.mul_rpow (pow_nonneg h0 _) (sub_nonneg.mpr h1)
    calc
      lambda * (1 - lambda ^ d) ≤ lambda * (2 * Real.rpow (1 - lambda) e) := by
        exact mul_le_mul_of_nonneg_left hroot h0
      _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
        calc
          lambda * (2 * Real.rpow (1 - lambda) e) = 2 * (lambda * Real.rpow (1 - lambda) e) := by
            ring
          _ = 2 * (Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e) := by
            nth_rw 1 [← hlambda_rpow]
          _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
            rw [← hmul_rpow]

end MIPStarRE.LDT.Pasting
