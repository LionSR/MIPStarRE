import MIPStarRE.LDT.Pasting.Statements

/-!
# Section 12 pasting: distinct tuple distribution bound

The total variation distance between the uniform distribution on all point tuples
and the distribution restricted to distinct tuples.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators

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

end MIPStarRE.LDT.Pasting
