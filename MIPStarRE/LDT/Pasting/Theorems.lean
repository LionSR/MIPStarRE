import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Preliminaries.SelfConsistency

/-!
# Section 12 — Theorems

Theorem stubs for low-degree pasting.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `thm:ld-pasting`. -/
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
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

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

/-- `lem:g-complete-self-consistency`. -/
private lemma qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hperm : PermInvState ψbi)
    (family : IdxPolyFamily params ι)
    (x : Fq params) :
    qSDD ψbi
        ((completePartSubMeas params family x).liftLeft)
        ((completePartSubMeas params family x).liftRight)
      ≤
    qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight) =
        2 * (ev ψbi (leftTensor (ι₂ := ι) T) - ev ψbi (opTensor T T)) := by
    calc
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight)
        = ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
            (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
              unfold qSDD qSDDCore completePartSubMeas
              simp [SubMeas.liftLeft, SubMeas.liftRight, postprocess, T, P.sum_eq_total]
              rw [P.sum_eq_total]
      _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
            ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
              have hLherm : (leftTensor (ι₂ := ι) T)ᴴ = leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (rightTensor (ι₁ := ι) T)ᴴ = rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                    (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))
                  = ev ψbi (((leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) T -
                        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T) -
                      (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) T -
                        rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
                      ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
      _ = 2 * (ev ψbi (leftTensor (ι₂ := ι) T) - ev ψbi (opTensor T T)) := by
            rw [hTT, hperm.swap_ev T]
            ring_nf
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        2 *
          (ev ψbi (leftTensor (ι₂ := ι) T) -
            ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
    have hsum_left :
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) =
          ev ψbi (leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))
          = ev ψbi (∑ a, leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => leftTensor (ι₂ := ι) (P.outcome g))]
        _ = ev ψbi (leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = ev ψbi (leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (2 *
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) -
                ev ψbi (opTensor (P.outcome g) (P.outcome g)))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = ev ψbi
                      (((leftTensor (ι₂ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          leftTensor (ι₂ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)) -
                        (rightTensor (ι₁ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          rightTensor (ι₁ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [SubMeas.liftLeft, SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
                _ = 2 *
                      (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) -
                        ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
                          rw [P.proj g, hperm.swap_ev (P.outcome g)]
                          ring
      _ = 2 *
            ∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) -
                ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              rw [← Finset.mul_sum]
      _ = 2 *
            ((∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) -
              ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              rw [Finset.sum_sub_distrib]
      _ = 2 *
            (ev ψbi (leftTensor (ι₂ := ι) T) -
              ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              rw [hsum_left]
  have hmatch :
      ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) ≤
        ev ψbi (opTensor T T) := by
    simpa [T, P, qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas, postprocess,
      completePartSubMeas, leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith

lemma gCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hperm : PermInvState ψbi)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    GCompleteSelfConsistencyStatement params ψbi family zeta := by
  /-
  Paper reference: `lem:g-complete-self-consistency` in
  `references/ldt-paper/ld-pasting.tex`.
  This is exactly the slice strong self-consistency hypothesis, repackaged under
  the Section 12 statement name.
  -/
  exact ⟨hself.sliceSelfConsistency⟩

/-- `cor:g-bot-self-consistency`. -/
theorem gBotSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hperm : PermInvState ψbi)
    (hcomplete : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    GBotSelfConsistencyStatement params ψbi family zeta := by
  refine {
    completePartWitness := hcomplete
    incompletePartSelfConsistency := ?_
  }
  rcases hcomplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
  have hcomplete_total :
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family)
        ≤ zeta := by
    unfold sddError at *
    calc
      avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((completePartLeftFamily params family) x)
              ((completePartRightFamily params family) x))
        ≤ avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
              apply avgOver_mono
              intro x
              simpa [completePartLeftFamily, completePartRightFamily,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas] using
                qSDD_completePart_le_slice params ψbi hperm family x
      _ ≤ zeta := hcomplete_bound
  refine ⟨?_⟩
  calc
    sddError ψbi
        (uniformDistribution (SliceQuestion params))
        (incompletePartLeftFamily params family)
        (incompletePartRightFamily params family)
      =
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            let T : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family x).total
            have hdiff :
                leftTensor (ι₂ := ι) (1 - T) - rightTensor (ι₁ := ι) (1 - T) =
                  - (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              simp [T, leftTensor, rightTensor, sub_eq_add_neg]
              ring
            have hcomplete_outcome :
                (postprocess ((family.meas x).toSubMeas) (fun _ => ())).outcome () =
                  (postprocess ((family.meas x).toSubMeas) (fun _ => ())).total := by
              rw [← (postprocess ((family.meas x).toSubMeas) (fun _ => ())).sum_eq_total]
              simp
            have hcomplete_outcome_T :
                (postprocess ((family.meas x).toSubMeas) (fun _ => ())).outcome () = T := by
              rw [hcomplete_outcome, postprocess_total]
              rfl
            calc
              qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)
                =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))ᴴ) *
                      (leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))) := by
                          simp [qSDD, qSDDCore, incompletePartLeftFamily,
                            incompletePartRightFamily, incompletePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T]
              _ =
                  ev ψbi
                    ((-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))ᴴ *
                      (-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))) := by
                          rw [hdiff]
              _ =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                      (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
                          have hswap :
                              ((rightTensor (ι₁ := ι) T)ᴴ - (leftTensor (ι₂ := ι) T)ᴴ) *
                                  (rightTensor (ι₁ := ι) T - leftTensor (ι₂ := ι) T) =
                                ((leftTensor (ι₂ := ι) T)ᴴ - (rightTensor (ι₁ := ι) T)ᴴ) *
                                  (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
                            noncomm_ring
                          simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
              _ =
                  qSDD ψbi
                    ((completePartLeftFamily params family) x)
                    ((completePartRightFamily params family) x) := by
                          simp [qSDD, qSDDCore, completePartLeftFamily,
                            completePartRightFamily, completePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T, hcomplete_outcome_T]
    _ ≤ zeta := hcomplete_total

/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψbi family M zeta omega chi := by
  /-
  Paper reference: `lem:commutativity-switcheroo` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the main aggregate-commutation step upgrading commutation with each
  `G^x_g` to commutation with the total `G^x`.
  -/
  sorry

/-- `cor:commuting-with-G-complete`. -/
theorem commutingWithGComplete
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error)
    (hcom : Commutativity.ComMainConclusion params strategy family G gamma zeta)
    (hself : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    CommutingWithGCompleteStatement params ψbi family gamma zeta := by
  sorry

/-- `cor:commuting-with-G-incomplete`. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψbi family gamma zeta) :
    CommutingWithGIncompleteStatement params ψbi family gamma zeta := by
  refine {
    completePartWitness := hcomm
    pointWithIncompletePartCommutation := ?_
    incompletePartCommutation := ?_
  }
  · rcases hcomm.pointWithCompletePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartPointProductLeft params family)
          (incompletePartPointProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartPointProductLeft params family)
            (completePartPointProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro g _hg
              have hdiff :
                  (incompletePartPointProductLeft params family q).outcome g -
                      (incompletePartPointProductRight params family q).outcome g =
                    -((completePartPointProductLeft params family q).outcome g -
                      (completePartPointProductRight params family q).outcome g) := by
                let A : MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome g
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : A * (1 - B) - (1 - B) * A = -(A * B - B * A) := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, h₂] using hentry
                · simp [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, h₂]
              rw [hdiff]
              have hswap :
                  (((completePartPointProductRight params family q).outcome g)ᴴ -
                        ((completePartPointProductLeft params family q).outcome g)ᴴ) *
                      ((completePartPointProductRight params family q).outcome g -
                        (completePartPointProductLeft params family q).outcome g) =
                    (((completePartPointProductLeft params family q).outcome g)ᴴ -
                        ((completePartPointProductRight params family q).outcome g)ᴴ) *
                      ((completePartPointProductLeft params family q).outcome g -
                        (completePartPointProductRight params family q).outcome g) := by
                noncomm_ring
              simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound
  · rcases hcomm.completePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartTotalProductLeft params family)
          (incompletePartTotalProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartTotalProductLeft params family)
            (completePartTotalProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro u _hu
              cases u
              have hq1 :
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                    (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total := by
                rw [← (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).sum_eq_total]
                simp
              have hq2 :
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total := by
                rw [← (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).sum_eq_total]
                simp
              have hdiff :
                  (incompletePartTotalProductLeft params family q).outcome () -
                      (incompletePartTotalProductRight params family q).outcome () =
                    (completePartTotalProductLeft params family q).outcome () -
                      (completePartTotalProductRight params family q).outcome () := by
                let A : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : (1 - A) * (1 - B) - (1 - B) * (1 - A) = A * B - B * A := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, hq1, hq2, h₂] using hentry
                · simp [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, hq1, h₂]
              rw [hdiff]
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound

/-- `cor:G-hat-facts`. -/
theorem gHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hselfComplete : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params ψbi family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params ψbi family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params ψbi family gamma zeta) :
    GHatFactsStatement params ψbi family gamma zeta := by
  refine {
    completePartSelfConsistencyWitness := hselfComplete
    incompletePartSelfConsistencyWitness := hselfIncomplete
    completePartCommutationWitness := hcommComplete
    incompletePartCommutationWitness := hcommIncomplete
    completedSelfConsistency := ?_
    completedCommutation := ?_
  }
  · -- TODO(#199): `completedSelfConsistency`: split gHat sum over
    -- `Option (Polynomial params)` into complete + incomplete parts and
    -- bound by `2 * zeta`.
    -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    rcases hselfComplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
    rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hincomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (gHatSelfConsistencyLeftFamily params family)
          (gHatSelfConsistencyRightFamily params family)
        =
          avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                  ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                  ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x) +
                qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            rw [Fintype.sum_option]
            have hcomplete_total :
                (completePartSubMeas params family x).total = (family.meas x).total := by
              simp [completePartSubMeas, postprocess_total]
            simpa [gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
              gHatIdxMeas, completeSubMeas, incompletePartLeftFamily,
              incompletePartRightFamily, incompletePartSubMeas, leftPlacedSubMeas,
              rightPlacedSubMeas, SubMeas.liftLeft, SubMeas.liftRight,
              IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas,
              hcomplete_total, add_comm, add_left_comm, add_assoc]
      _ =
          sddError ψbi
            (uniformDistribution (SliceQuestion params))
            (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
            (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) +
          sddError ψbi
            (uniformDistribution (SliceQuestion params))
            (incompletePartLeftFamily params family)
            (incompletePartRightFamily params family) := by
              rw [sddError, sddError, avgOver_add]
      _ ≤ zeta + zeta := add_le_add hcomplete_bound hincomplete_bound
      _ = gHatSelfConsistencyError zeta := by
            simp [gHatSelfConsistencyError, two_mul]
  · -- TODO(#199): `completedCommutation`: split gHat pair-product over
    -- `GHatOutcome × GHatOutcome` into complete + incomplete quadrants
    -- and bound by `gHatCommutationError`.
    -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  /-
  Deferred core argument from `lem:commute-g-half-sandwich` in
  `references/ldt-paper/ld-pasting.tex`.
  The proof iterates the `\widehat G` commutation bound across the half-sandwich.
  -/
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i := by
  /-
  Deferred core argument from `lem:ld-sandwich-line-one-point` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the one-point comparison between the sandwiched completed-slice outcome
  and the vertical-line measurement.
  -/
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family eps delta gamma zeta k := by
  /-
  Deferred packaging argument after `lem:ld-sandwich-line-one-point` in
  `references/ldt-paper/ld-pasting.tex`; this is the `lem:h-b-consistency`
  aggregation over all slice locations.
  -/
  sorry

/-- `cor:h-a-consistency`.

This restates the pasted-submeasurement consistency with the point measurement
using the paper's displayed `ν` error term. -/
theorem hAConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hHB : HBConsistencyStatement params strategy family eps delta gamma zeta k) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next (constructedPastedSubMeas params family k))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) := by
  sorry

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  /-
  Deferred core argument from `lem:over-all-outcomes` in
  `references/ldt-paper/ld-pasting.tex`.
  The proof expands the total mass of the pasted measurement across all completed
  outcome types `τ`.
  -/
  sorry

/-- `lem:from-H-to-G`. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params ψbi family gamma zeta k) :
    FromHToGStatement params strategy family gamma zeta k := by
  /-
  Deferred core argument from `lem:from-H-to-G` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the Bernoulli-tail recurrence converting the all-outcomes expansion to
  the averaged complete operator `G`.
  -/
  sorry

/-- `lem:chernoff-bernoulli-matrix`. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := by
           intro _
           exact hXpsd
         sum_eq_total := by
           simp
         total_le_one := by
           exact hXleOne } : SubMeas Unit ι)
      (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  /-
  Deferred matrix Chernoff/Bernoulli-tail contraction argument from
  `lem:chernoff-bernoulli-matrix` in `references/ldt-paper/ld-pasting.tex`.
  -/
  sorry

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  /-
  Paper reference: `cor:ld-pasting-N-completeness` in
  `references/ldt-paper/ld-pasting.tex`.
  This combines `overAllOutcomes`, `fromHToG`, and the matrix Chernoff bound.
  -/
  sorry

end MIPStarRE.LDT.Pasting
