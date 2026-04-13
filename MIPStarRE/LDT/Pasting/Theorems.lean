import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.MainInductionStep.Statements
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  sorry

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
  /-
  Paper reference: `references/ldt-paper/ld-pasting.tex`, `lem:ld-gbcon`.
  The proof is the displayed chain leading to equation `eq:ld-gbcon` in the
  blueprint: combine good-strategy consistency, `simeqToApprox`, and
  `triangleSub`.
  -/
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
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ev ψbi (opTensor T T) := by
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
                    (rightTensor_nonneg (ι₁ := ι)
                    (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
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
      _ = ev ψbi (leftTensor (ι₂ := ι) T) +
            ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ev ψbi (opTensor T T) := by
            simpa [hTT]
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
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
    have hsum_right :
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) =
          ev ψbi (rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g))
          = ev ψbi (∑ a, rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => rightTensor (ι₁ := ι) (P.outcome g))]
        _ = ev ψbi (rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = ev ψbi (rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
              ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
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
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          simpa [P.proj g]
      _ = (∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rfl
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
    (_hperm : PermInvState ψbi)
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
                qSDD_completePart_le_slice params ψbi family x
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

private lemma switcherooSelfConsistency_bip
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (omega : Error)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega) :
    Preliminaries.BipartiteSDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxProjSubMeas.toIdxSubMeas M)
      (IdxProjSubMeas.toIdxSubMeas M)
      omega := by
  constructor
  simpa [switcherooSelfConsistencyLeft, switcherooSelfConsistencyRight,
    IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    hselfM.squaredDistanceBound

private lemma switcherooCompletePartSelfConsistency_bip
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    Preliminaries.BipartiteSDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxProjSubMeas.toIdxSubMeas family.meas)
      (IdxProjSubMeas.toIdxSubMeas family.meas)
      zeta := by
  constructor
  simpa [IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    hselfG.completePartSelfConsistency.squaredDistanceBound

private lemma avgOver_uniform_slicePair
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Fq params → Error) :
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q => f q.1 q.2) =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => avgOver (uniformDistribution (SliceQuestion params)) (fun y => f x y)) := by
  have hq : ((Fintype.card (Fq params) : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q => f q.1 q.2)
      = ∑ x : Fq params, ∑ y : Fq params,
          (1 / ((Fintype.card (Fq params) * Fintype.card (Fq params) : ℕ) : Error)) * f x y := by
            simpa [avgOver, uniformDistribution, SlicePairQuestion, Fintype.card_prod] using
              (Fintype.sum_prod_type'
                (f := fun x : Fq params => fun y : Fq params =>
                  (1 / ((Fintype.card (Fq params) * Fintype.card (Fq params) : ℕ) : Error)) *
                    f x y))
    _ = ∑ x : Fq params, (1 / (Fintype.card (Fq params) : Error)) *
          ((1 / (Fintype.card (Fq params) : Error)) * ∑ y : Fq params, f x y) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          calc
            ∑ y : Fq params,
                (1 / ((Fintype.card (Fq params) * Fintype.card (Fq params) : ℕ) : Error)) * f x y
              = (1 / ((Fintype.card (Fq params) * Fintype.card (Fq params) : ℕ) : Error)) *
                  ∑ y : Fq params, f x y := by
                    rw [← Finset.mul_sum]
            _ = (1 / (Fintype.card (Fq params) : Error)) *
                  ((1 / (Fintype.card (Fq params) : Error)) * ∑ y : Fq params, f x y) := by
                    field_simp [hq]
                    rw [Nat.cast_mul]
                    ring
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x => avgOver (uniformDistribution (SliceQuestion params)) (fun y => f x y)) := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma avgOver_uniform_slicePair_swapOrder
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Fq params → Error) :
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q => f q.1 q.2) =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun y => avgOver (uniformDistribution (SliceQuestion params)) (fun x => f x y)) := by
  calc
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q => f q.1 q.2)
      = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q => f q.2 q.1) := by
          simpa [SlicePairQuestion] using
            (CommutativityPoints.avgOver_uniform_equiv
              (α := SlicePairQuestion params)
              (β := SlicePairQuestion params)
              (Equiv.prodComm (Fq params) (Fq params))
              (fun q => f q.1 q.2))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun y => avgOver (uniformDistribution (SliceQuestion params)) (fun x => f x y)) := by
          simpa using (avgOver_uniform_slicePair params (f := fun y x => f x y))

/-- If `|f q| ≤ c` pointwise and the distribution has total weight at most `1`, then
its weighted average is bounded by `c`. -/
private lemma avgOver_abs_le_of_bound
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f : Question → Error)
    (c : Error)
    (hc : 0 ≤ c)
    (hf : ∀ q, |f q| ≤ c) :
    |avgOver 𝒟 f| ≤ c := by
  calc
    |avgOver 𝒟 f|
      = |∑ q ∈ 𝒟.support, 𝒟.weight q * f q| := rfl
    _ ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * f q| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |f q| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support, 𝒟.weight q * c := by
          refine Finset.sum_le_sum ?_
          intro q _
          exact mul_le_mul_of_nonneg_left (hf q) (𝒟.nonnegative q)
    _ = c * ∑ q ∈ 𝒟.support, 𝒟.weight q := by
          calc
            ∑ q ∈ 𝒟.support, 𝒟.weight q * c
              = ∑ q ∈ 𝒟.support, c * 𝒟.weight q := by
                  refine Finset.sum_congr rfl ?_
                  intro q _
                  ring
            _ = c * ∑ q ∈ 𝒟.support, 𝒟.weight q := by
                  rw [Finset.mul_sum]
    _ ≤ c * 1 := by
          exact mul_le_mul_of_nonneg_left h𝒟 hc
    _ = c := by ring

private lemma avgOver_abs_le_avgOver_abs
    {α : Type*} [DecidableEq α]
    (𝒟 : Distribution α) (f : α → Error) :
    |avgOver 𝒟 f| ≤ avgOver 𝒟 (fun a => |f a|) := by
  unfold avgOver
  calc
    |∑ a ∈ 𝒟.support, 𝒟.weight a * f a|
      ≤ ∑ a ∈ 𝒟.support, |𝒟.weight a * f a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a * |f a| := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative a)]
    _ = avgOver 𝒟 (fun a => |f a|) := by
          rfl

/-- The usual `Σₐ Aₐ† Aₐ ≤ I` bound for a submeasurement. -/
private lemma subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- The total of a submeasurement is bounded between `0` and `1`. -/
private lemma subMeas_total_opBounded01
    {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    Preliminaries.OpBounded01 A.total := by
  constructor
  · exact A.total_nonneg
  · exact sub_nonneg.mpr A.total_le_one

/-- The total operator of a projective submeasurement is idempotent. -/
private lemma projSubMeas_total_sq
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome ι) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total := by
  simpa using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P

/-- Expand the switcheroo aggregate defect into the four terms used in the paper. -/
private lemma switcherooAggregate_qSDDOp_expand
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    qSDDOp ψbi
      (switcherooAggregateLeft params family M q)
      (switcherooAggregateRight params family M q)
      =
        ∑ o : Outcome,
          (ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)) +
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  have hGsq : G * G = G := by
    simpa [G, completePartSubMeas, postprocess_total] using
      projSubMeas_total_sq (family.meas q.1)
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro o _
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hMosq : Mo * Mo = Mo := by
    simpa [Mo] using (M q.2).proj o
  have hGherm : (leftTensor (ι₂ := ι) G)ᴴ = leftTensor (ι₂ := ι) G := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι)
          (SubMeas.total_nonneg (completePartSubMeas params family q.1)))).isHermitian.eq
  have hMoherm : (leftTensor (ι₂ := ι) Mo)ᴴ = leftTensor (ι₂ := ι) Mo := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((M q.2).outcome_pos o))).isHermitian.eq
  calc
    ev ψbi
        ((((switcherooAggregateLeft params family M q).outcome o -
              (switcherooAggregateRight params family M q).outcome o)ᴴ) *
          ((switcherooAggregateLeft params family M q).outcome o -
            (switcherooAggregateRight params family M q).outcome o))
      = ev ψbi
          ((((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
                (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))ᴴ) *
            ((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
              (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))) := by
            simp [switcherooAggregateLeft, switcherooAggregateRight,
              multiplyByTotalOnLeft, multiplyByTotalOnRight,
              OpFamily.leftPlacedOpFamily, completePartSubMeas, G, Mo,
              leftTensor_mul_leftTensor, Matrix.conjTranspose_mul]
    _ = ev ψbi
          (((leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
                (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo)) *
            ((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
              (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))) := by
            simp [hGherm, hMoherm]
    _ = ev ψbi
          ((leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G *
                leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) +
            (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo *
                leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
            (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G *
                leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
            (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo *
                leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo)) := by
            congr 1
            noncomm_ring
    _ = ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo) +
            leftTensor (ι₂ := ι) (G * Mo * G) -
            leftTensor (ι₂ := ι) (Mo * G * Mo * G) -
            leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            simp [leftTensor_mul_leftTensor, hGsq, hMosq, mul_assoc]
    _ =
        ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo)) +
        ev ψbi
          (leftTensor (ι₂ := ι) (G * Mo * G)) -
        ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo * G)) -
        ev ψbi
          (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            rw [ev_sub, ev_sub, ev_add]
    _ =
        ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                (M q.2).outcome o)) +
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (completePartSubMeas params family q.1).total)) -
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                (M q.2).outcome o * (completePartSubMeas params family q.1).total)) -
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (completePartSubMeas params family q.1).total * (M q.2).outcome o)) := by
            simp [G, Mo]

/-- The common comparison scalar `⟨ψ, G ⊗ M ψ⟩` from the switcheroo proof. -/
private noncomputable def switcherooAggregateTarget
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
          rightTensor (ι₁ := ι) ((M q.2).outcome o))

/-- The first positive term in the switcheroo expansion. -/
private noncomputable def switcherooAggregateFirstTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o))


private lemma switcherooAggregateFirstTerm_eq_leftSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateFirstTerm params ψbi family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  unfold switcherooAggregateFirstTerm
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun y =>
                ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M y).outcome o * (completePartSubMeas params family x).total *
                        (M y).outcome o)))) := by
            simpa using
              (avgOver_uniform_slicePair params
                (f := fun x y =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor (ι₂ := ι)
                        ((M y).outcome o * (completePartSubMeas params family x).total *
                          (M y).outcome o))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
              (uniformDistribution (SliceQuestion params))
              M
              ((completePartSubMeas params family x).total)) := by
            apply avgOver_congr
            intro x
            simp [MIPStarRE.LDT.Preliminaries.leftSandwichExpectation,
              avgOver, leftTensor_mul_leftTensor, mul_assoc]

private lemma switcherooAggregateTarget_eq_middleSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateTarget params ψbi family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  unfold switcherooAggregateTarget
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                rightTensor (ι₁ := ι) ((M q.2).outcome o)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun y =>
                ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι) ((completePartSubMeas params family x).total) *
                      rightTensor (ι₁ := ι) ((M y).outcome o)))) := by
            simpa using
              (avgOver_uniform_slicePair params
                (f := fun x y =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor (ι₂ := ι) ((completePartSubMeas params family x).total) *
                        rightTensor (ι₁ := ι) ((M y).outcome o))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
              (uniformDistribution (SliceQuestion params))
              M
              ((completePartSubMeas params family x).total)) := by
            apply avgOver_congr
            intro x
            simp [MIPStarRE.LDT.Preliminaries.middleSandwichExpectation, avgOver]

private lemma switcherooAggregateFirstTerm_le_target
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (omega : Error)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega) :
    switcherooAggregateFirstTerm params ψbi family M ≤
      switcherooAggregateTarget params ψbi family M + 2 * Real.sqrt omega := by
  let 𝒟x : Distribution (SliceQuestion params) := uniformDistribution (SliceQuestion params)
  have h𝒟x :
      ∑ x ∈ 𝒟x.support, 𝒟x.weight x ≤ 1 := by
    simpa [𝒟x] using uniformDistribution_weight_sum_le_one (SliceQuestion params)
  have hswitch :
      ∀ x : Fq params,
        |MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
              ((completePartSubMeas params family x).total) -
            MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
              ((completePartSubMeas params family x).total)| ≤
          2 * Real.sqrt omega := by
    intro x
    have hB : Preliminaries.OpBounded01 ((completePartSubMeas params family x).total) :=
      subMeas_total_opBounded01 (completePartSubMeas params family x)
    have hM_bip := switcherooSelfConsistency_bip params ψbi M omega hselfM
    simpa [𝒟x] using
      (MIPStarRE.LDT.Preliminaries.switchSandwich ψbi 𝒟x hnorm h𝒟x M
        ((completePartSubMeas params family x).total) hB omega hM_bip).leftSandwichTransfer
  rw [switcherooAggregateFirstTerm_eq_leftSandwich,
    switcherooAggregateTarget_eq_middleSandwich]
  let diff : Fq params → Error := fun x =>
    MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
        ((completePartSubMeas params family x).total) -
      MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
        ((completePartSubMeas params family x).total)
  have hdiff :
      avgOver 𝒟x diff =
        avgOver 𝒟x
            (fun x => MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
              ((completePartSubMeas params family x).total)) -
          avgOver 𝒟x
            (fun x => MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
              ((completePartSubMeas params family x).total)) := by
    unfold avgOver diff
    rw [show
      (∑ x ∈ 𝒟x.support,
          𝒟x.weight x *
            (MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
                ((completePartSubMeas params family x).total) -
              MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
                ((completePartSubMeas params family x).total))) =
        ∑ x ∈ 𝒟x.support,
          (𝒟x.weight x *
              MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
                ((completePartSubMeas params family x).total) -
            𝒟x.weight x *
              MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
                ((completePartSubMeas params family x).total)) by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring]
    rw [Finset.sum_sub_distrib]
  have hbound : |avgOver 𝒟x diff| ≤ 2 * Real.sqrt omega := by
    apply avgOver_abs_le_of_bound 𝒟x h𝒟x diff (2 * Real.sqrt omega)
    · positivity
    · intro x
      simpa [diff] using hswitch x
  rw [hdiff] at hbound
  have hupper :
      avgOver 𝒟x
          (fun x => MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M
            ((completePartSubMeas params family x).total)) -
        avgOver 𝒟x
          (fun x => MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M
            ((completePartSubMeas params family x).total)) ≤ 2 * Real.sqrt omega := by
    exact (abs_le.mp hbound).2
  linarith

private lemma switcheroo_first_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (omega : Error)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega) :
    let firstTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.leftSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    |firstTerm - commonTerm| ≤ 2 * Real.sqrt omega := by
  dsimp
  let L : Fq params → Error := fun x =>
    Preliminaries.leftSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  let C : Fq params → Error := fun x =>
    Preliminaries.middleSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  have hselfM_bip := switcherooSelfConsistency_bip params ψbi M omega hselfM
  have hpoint : ∀ x, |L x - C x| ≤ 2 * Real.sqrt omega := by
    intro x
    have hB : Preliminaries.OpBounded01 ((completePartSubMeas params family x).total) := by
      refine ⟨?_, ?_⟩
      · exact SubMeas.total_nonneg (completePartSubMeas params family x)
      · exact sub_nonneg.mpr (completePartSubMeas params family x).total_le_one
    simpa [L, C] using
      (Preliminaries.switchSandwich ψbi
        (uniformDistribution (SliceQuestion params))
        hnorm
        (uniformDistribution_weight_sum_le_one (SliceQuestion params))
        M
        ((completePartSubMeas params family x).total)
        hB
        omega
        hselfM_bip).leftSandwichTransfer
  calc
    |avgOver (uniformDistribution (SliceQuestion params)) L -
        avgOver (uniformDistribution (SliceQuestion params)) C|
      = |avgOver (uniformDistribution (SliceQuestion params)) (fun x => L x - C x)| := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun x => |L x - C x|) := by
          exact avgOver_abs_le_avgOver_abs _ _
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun _ => 2 * Real.sqrt omega) := by
          exact avgOver_mono _ _ _ hpoint
    _ = 2 * Real.sqrt omega := by
          have hq0 : (params.q : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hq
          simp [avgOver, uniformDistribution]
          field_simp [hq0]

/-- The one-outcome projective family whose sole effect is the complete slice part `G^x`. -/
private noncomputable def completePartProjFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (SliceQuestion params) Unit ι :=
  fun x =>
    { toSubMeas := completePartSubMeas params family x
      proj := by
        intro u
        cases u
        have hsingle :
            (completePartSubMeas params family x).outcome () =
              (completePartSubMeas params family x).total := by
          rw [← (completePartSubMeas params family x).sum_eq_total]
          simp [completePartSubMeas]
        rw [hsingle]
        simpa [completePartSubMeas, postprocess_total] using
          MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x) }

/-- The second positive term in the switcheroo expansion. -/
private noncomputable def switcherooAggregateSecondTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The third (negative) term in the switcheroo expansion. -/
private noncomputable def switcherooAggregateThirdTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The fourth (negative) term in the switcheroo expansion. -/
private noncomputable def switcherooAggregateFourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))

private lemma switcherooAggregateThirdTerm_eq_fourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateThirdTerm params ψbi family M =
      switcherooAggregateFourthTerm params ψbi family M := by
  unfold switcherooAggregateThirdTerm switcherooAggregateFourthTerm
  apply avgOver_congr
  intro q
  refine Finset.sum_congr rfl ?_
  intro o _
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hGherm : Gᴴ = G :=
    (Matrix.nonneg_iff_posSemidef.mp
      (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq
  have hMoherm : Moᴴ = Mo :=
    (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq
  calc
    ev ψbi (leftTensor (ι₂ := ι) (Mo * G * Mo * G))
      = ev ψbi ((leftTensor (ι₂ := ι) (Mo * G * Mo * G))ᴴ) := by
          symm
          exact ev_conjTranspose ψbi _
    _ = ev ψbi (leftTensor (ι₂ := ι) ((Mo * G * Mo * G)ᴴ)) := by
          congr 1
          simpa [leftTensor, opTensor] using
            (conjTranspose_opTensor (Mo * G * Mo * G)
              (1 : MIPStarRE.Quantum.Op ι))
    _ = ev ψbi (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
          congr 1
          simpa [mul_assoc, Matrix.conjTranspose_mul, hGherm, hMoherm]

private lemma switcherooAggregate_qSDDOp_expand_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooAggregateLeft params family M q)
          (switcherooAggregateRight params family M q)) =
      switcherooAggregateFirstTerm params ψbi family M +
        switcherooAggregateSecondTerm params ψbi family M -
        switcherooAggregateThirdTerm params ψbi family M -
        switcherooAggregateFourthTerm params ψbi family M := by
  let A : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  let B : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))
  let C : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))
  let D : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooAggregateLeft params family M q)
          (switcherooAggregateRight params family M q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => A q + B q - C q - D q) := by
              apply avgOver_congr
              intro q
              rw [switcherooAggregate_qSDDOp_expand]
              simp [A, B, C, D, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) A +
          avgOver (uniformDistribution (SlicePairQuestion params)) B -
          avgOver (uniformDistribution (SlicePairQuestion params)) C -
          avgOver (uniformDistribution (SlicePairQuestion params)) D := by
            rw [show (fun q => A q + B q - C q - D q) =
                fun q => (A q + B q) + ((-1 : Error) * C q + (-1 : Error) * D q) by
                  funext q
                  ring]
            rw [avgOver_add, avgOver_add, avgOver_add, avgOver_const_mul, avgOver_const_mul]
            simp [sub_eq_add_neg]
            ring
    _ = switcherooAggregateFirstTerm params ψbi family M +
          switcherooAggregateSecondTerm params ψbi family M -
          switcherooAggregateThirdTerm params ψbi family M -
          switcherooAggregateFourthTerm params ψbi family M := by
            simp [switcherooAggregateFirstTerm, switcherooAggregateSecondTerm,
              switcherooAggregateThirdTerm, switcherooAggregateFourthTerm, A, B, C, D]



/-- The one-outcome complete-part family inherits self-consistency from the slice family. -/
private lemma completePartProjFamily_selfConsistency_generic
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight params (completePartProjFamily params family))
      zeta := by
  rcases hself.completePartSelfConsistency with ⟨hself_bound⟩
  constructor
  unfold sddError at *
  calc
    avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          qSDD ψbi
            ((switcherooSelfConsistencyLeft params (completePartProjFamily params family)) x)
            ((switcherooSelfConsistencyRight params (completePartProjFamily params family)) x))
      ≤
        avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
            apply avgOver_mono
            intro x
            simpa [switcherooSelfConsistencyLeft, switcherooSelfConsistencyRight,
              completePartProjFamily, IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
              qSDD_completePart_le_slice params ψbi family x
    _ ≤ zeta := hself_bound

private lemma switcheroo_second_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    let secondTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun y => Preliminaries.leftSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          family.meas (((M y).toSubMeas).total))
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun y => Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          family.meas (((M y).toSubMeas).total))
    |secondTerm - commonTerm| ≤ 2 * Real.sqrt zeta := by
  dsimp
  let L : Fq params → Error := fun y =>
    Preliminaries.leftSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      family.meas (((M y).toSubMeas).total)
  let C : Fq params → Error := fun y =>
    Preliminaries.middleSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      family.meas (((M y).toSubMeas).total)
  have hselfG_bip := switcherooCompletePartSelfConsistency_bip params ψbi family zeta hselfG
  have hpoint : ∀ y, |L y - C y| ≤ 2 * Real.sqrt zeta := by
    intro y
    have hB : Preliminaries.OpBounded01 (((M y).toSubMeas).total) := by
      refine ⟨?_, ?_⟩
      · exact SubMeas.total_nonneg ((M y).toSubMeas)
      · exact sub_nonneg.mpr ((M y).toSubMeas).total_le_one
    simpa [L, C] using
      (Preliminaries.switchSandwich ψbi
        (uniformDistribution (SliceQuestion params))
        hnorm
        (uniformDistribution_weight_sum_le_one (SliceQuestion params))
        family.meas
        (((M y).toSubMeas).total)
        hB
        zeta
        hselfG_bip).leftSandwichTransfer
  calc
    |avgOver (uniformDistribution (SliceQuestion params)) L -
        avgOver (uniformDistribution (SliceQuestion params)) C|
      = |avgOver (uniformDistribution (SliceQuestion params)) (fun y => L y - C y)| := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun y => |L y - C y|) := by
          exact avgOver_abs_le_avgOver_abs _ _
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun _ => 2 * Real.sqrt zeta) := by
          exact avgOver_mono _ _ _ hpoint
    _ = 2 * Real.sqrt zeta := by
          have hq0 : (params.q : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hq
          simp [avgOver, uniformDistribution]
          field_simp [hq0]

/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (hperm : PermInvState ψbi)
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

  The paper informally compares all four `qSDDOp` expansion terms to a single
  scalar center. In Lean it is cleaner to use two centers whose contributions
  cancel algebraically:

  * `G ⊗ M` for the first/third terms
  * `M ⊗ G` for the second/fourth terms

  This avoids inserting an extra symmetry assumption on `ψbi` at this stage.
  -/
  let 𝒟x : Distribution (SliceQuestion params) :=
    uniformDistribution (SliceQuestion params)
  let Gavg : SubMeas (Polynomial params) ι := IdxPolyFamily.averagedSubMeas family
  let Mavg : SubMeas Outcome ι :=
    averageIdxSubMeas 𝒟x (IdxProjSubMeas.toIdxSubMeas M)
      (uniformDistribution_weight_sum_le_one (SliceQuestion params))
  have h𝒟x : ∑ x ∈ 𝒟x.support, 𝒟x.weight x ≤ 1 := by
    simpa [𝒟x] using uniformDistribution_weight_sum_le_one (SliceQuestion params)
  have hselfM_bip := switcherooSelfConsistency_bip params ψbi M omega hselfM
  let firstTerm : Error :=
    MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x M Gavg.total
  let centerGM : Error :=
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x M Gavg.total
  have hfirst :
      |firstTerm - centerGM| ≤ 2 * Real.sqrt omega := by
    have hswitch :=
      MIPStarRE.LDT.Preliminaries.switchSandwich ψbi 𝒟x hnorm h𝒟x M Gavg.total
        ⟨Gavg.total_nonneg, sub_nonneg.mpr Gavg.total_le_one⟩ omega hselfM_bip
    simpa [firstTerm, centerGM] using hswitch.leftSandwichTransfer
  let secondTerm : Error :=
    MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi 𝒟x
      (fun x =>
        { toSubMeas := completePartSubMeas params family x
          proj := by
            intro u
            cases u
            have hsingle :
                (completePartSubMeas params family x).outcome () =
                  (completePartSubMeas params family x).total := by
              rw [← (completePartSubMeas params family x).sum_eq_total]
              simp [completePartSubMeas]
            rw [hsingle]
            simpa [completePartSubMeas, postprocess_total] using
              MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x) })
      Mavg.total
  let centerMG : Error :=
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi 𝒟x
      (fun x =>
        { toSubMeas := completePartSubMeas params family x
          proj := by
            intro u
            cases u
            have hsingle :
                (completePartSubMeas params family x).outcome () =
                  (completePartSubMeas params family x).total := by
              rw [← (completePartSubMeas params family x).sum_eq_total]
              simp [completePartSubMeas]
            rw [hsingle]
            simpa [completePartSubMeas, postprocess_total] using
              MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x) })
      Mavg.total
  have hMavg_bounded : MIPStarRE.LDT.Preliminaries.OpBounded01 Mavg.total := by
    exact ⟨Mavg.total_nonneg, sub_nonneg.mpr Mavg.total_le_one⟩
  sorry

/-- Reindexing a uniform slice-pair average along `Prod.swap` preserves `SDDOpRel`. -/
private lemma sddOpRel_swap_questions
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (A B : IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      A B δ →
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params))
        (fun q => A (q.2, q.1))
        (fun q => B (q.2, q.1))
        δ := by
  intro ⟨hAB⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi (A (q.2, q.1)) (B (q.2, q.1)))
      =
        avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi (A q) (B q)) := by
            symm
            simpa [SlicePairQuestion] using
              (CommutativityPoints.avgOver_uniform_equiv
                (α := SlicePairQuestion params)
                (β := SlicePairQuestion params)
                (Equiv.prodComm (Fq params) (Fq params))
                (fun q => qSDDOp ψbi (A q) (B q)))
    _ ≤ δ := hAB

/-- Reinterpret the point-with-complete-part commutation bound as a relation on the
`Polynomial × Unit` outcome type expected by `commutativitySwitcheroo`. -/
private lemma pointWithCompletePart_as_switcheroo_input
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      gamma) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family (completePartProjFamily params family))
      (switcherooPointProductRight params family (completePartProjFamily params family))
      gamma := by
  rcases hcomm with ⟨hcomm⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooPointProductLeft params family (completePartProjFamily params family) q)
          (switcherooPointProductRight params family (completePartProjFamily params family) q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi
            (completePartPointProductLeft params family q)
            (completePartPointProductRight params family q)) := by
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              let F : Polynomial params × Unit → Error := fun ab =>
                ev ψbi
                  ((((switcherooPointProductLeft params family
                            (completePartProjFamily params family) q).outcome ab -
                          (switcherooPointProductRight params family
                            (completePartProjFamily params family) q).outcome ab)ᴴ) *
                      ((switcherooPointProductLeft params family
                            (completePartProjFamily params family) q).outcome ab -
                        (switcherooPointProductRight params family
                          (completePartProjFamily params family) q).outcome ab))
              change (∑ ab : Polynomial params × Unit, F ab) = _
              have hsplit :
                  (∑ ab : Polynomial params × Unit, F ab) =
                    ∑ g : Polynomial params, ∑ u : Unit, F (g, u) := by
                simpa [F] using
                  (Fintype.sum_prod_type' (f := fun g u => F (g, u)))
              have hsingle :
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total := by
                rw [← (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).sum_eq_total]
                simp
              rw [hsplit]
              simp [F, switcherooPointProductLeft, switcherooPointProductRight,
                completePartProjFamily, completePartPointProductLeft,
                completePartPointProductRight, completePartSubMeas,
                multiplyByTotalOnRight, multiplyByTotalOnLeft,
                orderedProductOpFamily, reversedProductOpFamily,
                OpFamily.leftPlacedOpFamily, postprocess_total, hsingle]
    _ ≤ gamma := hcomm

/-- The complete-part family inherits self-consistency from the slice family by
pointwise comparison of the `qSDD` defect. -/
private lemma completePartProjFamily_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    SDDRel strategy.state
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight params (completePartProjFamily params family))
      zeta := by
  simpa using
    completePartProjFamily_selfConsistency_generic params strategy.state family zeta hself

private lemma switcherooAggregateLeft_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateLeft params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductLeft params family q).outcome () := by
  have hsingle1 :
      (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total := by
    rw [← (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).sum_eq_total]
    simp
  have hsingle2 :
      (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total := by
    rw [← (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).sum_eq_total]
    simp
  simp [switcherooAggregateLeft, completePartProjFamily,
    completePartTotalProductLeft, completePartSubMeas,
    multiplyByTotalOnRight, multiplyByTotalOnLeft,
    OpFamily.leftPlacedOpFamily, postprocess_total, hsingle1, hsingle2]

private lemma switcherooAggregateRight_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateRight params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductRight params family q).outcome () := by
  have hsingle1 :
      (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total := by
    rw [← (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).sum_eq_total]
    simp
  have hsingle2 :
      (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total := by
    rw [← (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).sum_eq_total]
    simp
  simp [switcherooAggregateRight, completePartProjFamily,
    completePartTotalProductRight, completePartSubMeas,
    multiplyByTotalOnRight, multiplyByTotalOnLeft,
    OpFamily.leftPlacedOpFamily, postprocess_total, hsingle1, hsingle2]

private lemma qSDDOp_congr_unit_outcome
    (ψbi : QuantumState (ι × ι))
    (A B A' B' : OpFamily Unit (ι × ι))
    (hA : A.outcome () = A'.outcome ())
    (hB : B.outcome () = B'.outcome ()) :
    qSDDOp ψbi A B = qSDDOp ψbi A' B' := by
  unfold qSDDOp qSDDCore
  simp [hA, hB]

private lemma completePartAggregateCommutation_as_total
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

set_option maxHeartbeats 1000000 in
-- Many sqrt/rpow manipulations for `12 * sqrt zeta + 4 * sqrt (ν_com) ≤ ν₂`.
private lemma firstSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (Commutativity.comMainError params gamma zeta)
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
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (2 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
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
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have heighth_le_sixteenth : eighthSum ≤ sixteenthSum := by
    dsimp [eighthSum, sixteenthSum]
    exact add_le_add (add_le_add heighth_gamma heighth_zeta) heighth_ratio
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
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      positivity
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
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
        6 * (params.m : Error) * sixteenthSum := by
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
      _ ≤ 6 * (params.m : Error) * sixteenthSum := by
            gcongr
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * (params.m : Error) * sixteenthSum := by
    have hterm : Real.rpow zeta (1 / (2 : Error)) ≤ sixteenthSum := by
      have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hgamma_nonneg _
      have hratio16_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hratio_nonneg _
      have hsum1 :
          Real.rpow zeta (1 / (16 : Error)) ≤
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) := by
        linarith
      have hsum2 :
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
            sixteenthSum := by
        have hsum2' :
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
              Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
          linarith
        simpa [sixteenthSum] using hsum2'
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    nlinarith [hm_ge_one, hterm]
  have hchi_term :
      4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
        24 * (params.m : Error) * sixteenthSum := by
    have hsqrt_com' :
        Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
          6 * (params.m : Error) * sixteenthSum := by
      simpa [Real.sqrt_eq_rpow] using hsqrt_com
    nlinarith [hsqrt_com']
  calc
    commutativitySwitcherooError zeta zeta (Commutativity.comMainError params gamma zeta)
      = 12 * Real.rpow zeta (1 / (2 : Error)) +
          4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) := by
            simp [commutativitySwitcherooError]
            ring
    _ ≤ 12 * (params.m : Error) * sixteenthSum +
          24 * (params.m : Error) * sixteenthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]
          ring

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

/-- TODO: formalize the paper's scalar inequality
`12 * sqrt zeta + 4 * sqrt θ₁ ≤ ν₂`, where `θ₁` is the first switcheroo error.
As above, this needs the paper-side small-error regime or a separate large-error
fallback argument. -/
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
    (hnorm : strategy.state.IsNormalized)
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
      commutativitySwitcheroo params strategy.state hnorm strategy.permInvState family family.meas zeta zeta
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
    apply commutativitySwitcheroo params strategy.state hnorm strategy.permInvState family
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

set_option maxHeartbeats 2000000 in
-- Large Finset.sum_option + simp unfolding across four quadrants.
/-- Split the `Option × Option` squared-distance defect into its four quadrants. -/
private lemma qSDDCore_option_pair_decompose
    {α β : Type*} [Fintype α] [Fintype β]
    (ψ : QuantumState ι)
    (Lss Rss : α × β → MIPStarRE.Quantum.Op ι)
    (Lsn Rsn : α → MIPStarRE.Quantum.Op ι)
    (Lns Rns : β → MIPStarRE.Quantum.Op ι)
    (Lnn Rnn : Unit → MIPStarRE.Quantum.Op ι) :
    qSDDCore ψ
      (fun ab : Option α × Option β =>
        match ab.1, ab.2 with
        | some a, some b => Lss (a, b)
        | some a, none => Lsn a
        | none, some b => Lns b
        | none, none => Lnn ())
      (fun ab : Option α × Option β =>
        match ab.1, ab.2 with
        | some a, some b => Rss (a, b)
        | some a, none => Rsn a
        | none, some b => Rns b
        | none, none => Rnn ()) =
      qSDDCore ψ Lss Rss +
        qSDDCore ψ Lsn Rsn +
        qSDDCore ψ Lns Rns +
        qSDDCore ψ Lnn Rnn := by
  unfold qSDDCore
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp_rw [Fintype.sum_option]
  rw [Finset.sum_add_distrib]
  let SS : α × β → Error := fun a =>
    ev ψ ((Lss a - Rss a)ᴴ * (Lss a - Rss a))
  have hss :
      (∑ x, ∑ x_1, ev ψ ((Lss (x, x_1) - Rss (x, x_1))ᴴ * (Lss (x, x_1) - Rss (x, x_1)))) =
        ∑ a : α × β, SS a := by
    symm
    simpa [SS] using
      (Fintype.sum_prod_type'
        (f := fun x x_1 =>
          ev ψ ((Lss (x, x_1) - Rss (x, x_1))ᴴ * (Lss (x, x_1) - Rss (x, x_1)))))
  rw [hss]
  simp [SS, add_assoc, add_left_comm, add_comm]

set_option maxHeartbeats 2000000 in
-- Combines four self-consistency + commutation witnesses with heavy unfolding.
/-- `cor:G-hat-facts`. -/
theorem gHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (_hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
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
  · -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    -- This step needs the full slice-family self-consistency witness:
    -- `\widehat G` expands into the original slice outcomes together with the
    -- incomplete part, not into the postprocessed complete-part family alone.
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
            simp [gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
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
    let swappedIncompletePointLeft :
        IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
      fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          multiplyByTotalOnLeft
            (incompletePartSubMeas params family q.1)
            ((family.meas q.2).toSubMeas)
    let swappedIncompletePointRight :
        IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
      fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          multiplyByTotalOnRight
            ((family.meas q.2).toSubMeas)
            (incompletePartSubMeas params family q.1)
    -- Review note: this duplicates a symmetry argument used elsewhere; keep it local for now.
    have hqSDDOp_symm_poly
        (A B : OpFamily (Polynomial params) (ι × ι)) :
        qSDDOp ψbi A B = qSDDOp ψbi B A := by
      let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        fun a => A.outcome a - B.outcome a
      let G : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        fun a => B.outcome a - A.outcome a
      have hFG : F = fun a => -G a := by
        funext a
        dsimp [F, G]
        abel
      unfold qSDDOp qSDDCore
      change ∑ a : Polynomial params, ev ψbi ((F a)ᴴ * F a) =
        ∑ a : Polynomial params, ev ψbi ((G a)ᴴ * G a)
      rw [hFG]
      refine Finset.sum_congr rfl ?_
      intro a _
      change ev ψbi ((-G a)ᴴ * (-G a)) = ev ψbi ((G a)ᴴ * G a)
      simp
    have hswapIncompleteBound :
        sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          swappedIncompletePointLeft
          swappedIncompletePointRight
          ≤ commutingWithGIncompleteError params gamma zeta := by
      rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hbound⟩
      calc
        sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight
          =
            avgOver (uniformDistribution (SlicePairQuestion params))
              (fun q =>
                qSDDOp ψbi
                  (incompletePartPointProductLeft params family (q.2, q.1))
                  (incompletePartPointProductRight params family (q.2, q.1))) := by
                unfold sddErrorOp swappedIncompletePointLeft swappedIncompletePointRight
                apply avgOver_congr
                intro q
                rw [hqSDDOp_symm_poly]
                rfl
        _ =
            avgOver (uniformDistribution (SlicePairQuestion params))
              (fun q =>
                qSDDOp ψbi
                  (incompletePartPointProductLeft params family q)
                  (incompletePartPointProductRight params family q)) := by
                simpa using
                  (avgOver_uniform_equiv
                    (Equiv.prodComm (Fq params) (Fq params))
                    (fun q =>
                      qSDDOp ψbi
                        (incompletePartPointProductLeft params family q)
                        (incompletePartPointProductRight params family q))).symm
        _ =
            sddErrorOp ψbi
              (uniformDistribution (SlicePairQuestion params))
              (incompletePartPointProductLeft params family)
              (incompletePartPointProductRight params family) := by
                rfl
        _ ≤ commutingWithGIncompleteError params gamma zeta := hbound
    have hzeta_nonneg : 0 ≤ zeta := by
      rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hbound⟩
      exact le_trans
        (sddError_nonneg ψbi
          (uniformDistribution (SliceQuestion params))
          (incompletePartLeftFamily params family)
          (incompletePartRightFamily params family))
        hbound
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
      positivity
    have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
      have hq_pos : (0 : Error) < params.q := by
        exact_mod_cast params.hq
      exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
    have hquarter_gamma :
        Real.rpow gamma (1 / (4 : Error)) ≤ Real.rpow gamma (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
    have hquarter_zeta :
        Real.rpow zeta (1 / (4 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
    have hquarter_ratio :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) ≤
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
    let completeQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
    let incompleteQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (incompletePartPointProductLeft params family q)
          (incompletePartPointProductRight params family q)
    let swappedQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (swappedIncompletePointLeft q)
          (swappedIncompletePointRight q)
    let totalQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (incompletePartTotalProductLeft params family q)
          (incompletePartTotalProductRight params family q)
    have hdecomp_q :
        ∀ q,
          qSDDOp ψbi
              (gHatPairProductLeft params family q)
              (gHatPairProductRight params family q) =
            completeQuadrant q +
              incompleteQuadrant q +
              swappedQuadrant q +
              totalQuadrant q := by
      -- TODO(#199): isolate the explicit `Option × Option` sum rewrite into a reusable lemma.
      -- The rest of the proof below already handles the scalar bounds once this decomposition
      -- is available.
      intro q
      rcases q with ⟨x, y⟩
      let completeLeft :
          (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
        (OpFamily.leftPlacedOpFamily (ιB := ι) <|
          orderedProductOpFamily
            ((family.meas x).toSubMeas)
            ((family.meas y).toSubMeas)).outcome
      let completeRight :
          (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
        (OpFamily.leftPlacedOpFamily (ιB := ι) <|
          reversedProductOpFamily
            ((family.meas x).toSubMeas)
            ((family.meas y).toSubMeas)).outcome
      let incompleteLeft :
          Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        (incompletePartPointProductLeft params family (x, y)).outcome
      let incompleteRight :
          Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        (incompletePartPointProductRight params family (x, y)).outcome
      let swappedLeft :
          Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        (swappedIncompletePointLeft (x, y)).outcome
      let swappedRight :
          Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
        (swappedIncompletePointRight (x, y)).outcome
      let totalLeft : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
        (incompletePartTotalProductLeft params family (x, y)).outcome
      let totalRight : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
        (incompletePartTotalProductRight params family (x, y)).outcome
      have hcompleteTotalX :
          (completePartSubMeas params family x).total = (family.meas x).total := by
        simp [completePartSubMeas, postprocess_total]
      have hcompleteTotalY :
          (completePartSubMeas params family y).total = (family.meas y).total := by
        simp [completePartSubMeas, postprocess_total]
      let gHatLeft :
          Option (Polynomial params) × Option (Polynomial params) →
            MIPStarRE.Quantum.Op (ι × ι) :=
        fun ab =>
          match ab.1, ab.2 with
          | some g, some h => completeLeft (g, h)
          | some g, none => incompleteLeft g
          | none, some h => swappedLeft h
          | none, none => totalLeft ()
      let gHatRight :
          Option (Polynomial params) × Option (Polynomial params) →
            MIPStarRE.Quantum.Op (ι × ι) :=
        fun ab =>
          match ab.1, ab.2 with
          | some g, some h => completeRight (g, h)
          | some g, none => incompleteRight g
          | none, some h => swappedRight h
          | none, none => totalRight ()
      have hgHatLeft :
          (gHatPairProductLeft params family (x, y)).outcome = gHatLeft := by
        funext ab
        rcases ab with ⟨a, b⟩
        cases a <;> cases b <;>
          simp [gHatLeft, completeLeft, incompleteLeft, swappedLeft, totalLeft,
            gHatPairProductLeft, gHatIdxMeas, completeSubMeas,
            incompletePartPointProductLeft, incompletePartTotalProductLeft,
            swappedIncompletePointLeft, incompletePartSubMeas, multiplyByTotalOnLeft,
            multiplyByTotalOnRight, orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
            hcompleteTotalX, hcompleteTotalY]
      have hgHatRight :
          (gHatPairProductRight params family (x, y)).outcome = gHatRight := by
        funext ab
        rcases ab with ⟨a, b⟩
        cases a <;> cases b <;>
          simp [gHatRight, completeRight, incompleteRight, swappedRight, totalRight,
            gHatPairProductRight, gHatIdxMeas, completeSubMeas,
            incompletePartPointProductRight, incompletePartTotalProductRight,
            swappedIncompletePointRight, incompletePartSubMeas, multiplyByTotalOnLeft,
            multiplyByTotalOnRight, reversedProductOpFamily, OpFamily.leftPlacedOpFamily,
            hcompleteTotalX, hcompleteTotalY]
      calc
        qSDDOp ψbi
            (gHatPairProductLeft params family (x, y))
            (gHatPairProductRight params family (x, y))
          = qSDDCore ψbi gHatLeft gHatRight := by
              rw [qSDDOp, hgHatLeft, hgHatRight]
        _ =
            qSDDCore ψbi completeLeft completeRight +
              qSDDCore ψbi incompleteLeft incompleteRight +
              qSDDCore ψbi swappedLeft swappedRight +
              qSDDCore ψbi totalLeft totalRight := by
                dsimp [gHatLeft, gHatRight]
                convert qSDDCore_option_pair_decompose ψbi
                  completeLeft completeRight
                  incompleteLeft incompleteRight
                  swappedLeft swappedRight
                  totalLeft totalRight using 1
                · unfold qSDDCore
                  apply Finset.sum_congr rfl
                  intro a _ha
                  rcases a with ⟨oa, ob⟩
                  cases oa <;> cases ob <;> simp
        _ =
            completeQuadrant (x, y) +
              incompleteQuadrant (x, y) +
              swappedQuadrant (x, y) +
              totalQuadrant (x, y) := by
                have hcompleteQuadrant :
                    qSDDCore ψbi completeLeft completeRight = completeQuadrant (x, y) := by
                  rfl
                have hincompleteQuadrant :
                    qSDDCore ψbi incompleteLeft incompleteRight =
                      incompleteQuadrant (x, y) := by
                  rfl
                have hswappedQuadrant :
                    qSDDCore ψbi swappedLeft swappedRight = swappedQuadrant (x, y) := by
                  rfl
                have htotalQuadrant :
                    qSDDCore ψbi totalLeft totalRight = totalQuadrant (x, y) := by
                  rfl
                rw [hcompleteQuadrant, hincompleteQuadrant, hswappedQuadrant, htotalQuadrant]
    rcases hcommComplete.pairwiseCompletePartCommutation with ⟨hcomplete_bound⟩
    rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hincomplete_point_bound⟩
    rcases hcommIncomplete.incompletePartCommutation with ⟨hincomplete_total_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (gHatPairProductLeft params family)
          (gHatPairProductRight params family)
        =
          avgOver (uniformDistribution (SlicePairQuestion params))
            (fun q =>
              completeQuadrant q +
                incompleteQuadrant q +
                swappedQuadrant q +
                totalQuadrant q) := by
            unfold sddErrorOp
            apply avgOver_congr
            exact hdecomp_q
      _ =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (fun q =>
              OpFamily.leftPlacedOpFamily (ιB := ι) <|
                orderedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas))
            (fun q =>
              OpFamily.leftPlacedOpFamily (ιB := ι) <|
                reversedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas)) +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (incompletePartPointProductLeft params family)
            (incompletePartPointProductRight params family) +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (incompletePartTotalProductLeft params family)
            (incompletePartTotalProductRight params family) := by
              unfold sddErrorOp
              rw [avgOver_add, avgOver_add, avgOver_add]
      _ ≤
          pairwiseCompletePartCommutationError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta := by
              gcongr
      _ ≤ gHatCommutationError params gamma zeta := by
            set quarterSum : Error :=
              Real.rpow gamma (1 / (4 : Error)) +
                Real.rpow zeta (1 / (4 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))
            set sixteenthSum : Error :=
              Real.rpow gamma (1 / (16 : Error)) +
                Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
            have hquarter_le :
                quarterSum ≤ sixteenthSum := by
              dsimp [quarterSum, sixteenthSum]
              exact add_le_add (add_le_add hquarter_gamma hquarter_zeta) hquarter_ratio
            have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
            calc
              pairwiseCompletePartCommutationError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta
                =
                  30 * (params.m : Error) * quarterSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum := by
                      simp [pairwiseCompletePartCommutationError, quarterSum,
                        commutingWithGIncompleteError, commutingWithGCompleteError,
                        sixteenthSum, Commutativity.comMainError]
              _ ≤
                  30 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum := by
                      gcongr
              _ = gHatCommutationError params gamma zeta := by
                    simp [gHatCommutationError, sixteenthSum]
                    ring

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
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i := by
  have hcomm :
      ∀ j : ℕ, 2 ≤ j →
        CommuteGHalfSandwichStatement params strategy.state family gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy.state family gamma zeta j hj hfacts
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
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

This packages the point-consistency part of the pasted-submeasurement chain and
the completed-measurement wrapper. -/
theorem hAConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta) ∧
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedMeasurement params family k).toSubMeas)
        (MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta) := by
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  constructor -- OverAllOutcomesStatement
  constructor -- SDDRel
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).
  Requires: Schwartz-Zippel infrastructure, distinct → uniform swap lemma. -/
  sorry

/-- `lem:truncated-type-sum-recurrence`.

This is the source-style recurrence for the truncated type sums that appear in
the `fromHToG` reduction. -/
theorem truncatedTypeSumRecurrence
    (G : MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums G d prefixLen τtail)ᴴ = truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ truncatedTypeSums G d prefixLen τtail ∧
      truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums G d (prefixLen + 1) τtail =
        truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G +
          truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
  /-
  Paper reference: `references/ldt-paper/ld-pasting.tex`,
  `lem:truncated-type-sum-recurrence`.
  The proof is the commuting-polynomial argument in `G` and `I - G`.
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params ψbi family gamma zeta k) :
    FromHToGStatement params strategy family gamma zeta k := by
  constructor -- FromHToGStatement
  · -- recurrenceStep: per-step Bernoulli-tail commutation
    intro ℓ hℓ τ
    constructor -- SDDOpRel
    /- Inductive step ℓ of the Bernoulli-tail recurrence (ld-pasting.tex
    lines 1294–1666). Three commutation sub-steps per induction step:
    (a) move rightmost Ĝ^{x_ℓ} to 2nd tensor factor (√(2ζ)),
    (b) commute leftmost Ĝ past remaining factors (√ν₄),
    (c) move leftmost to 2nd tensor factor (√(2ζ)).
    Per-step error: 2√(2ζ) + 2√ν₄ = fromHToGRecurrenceError. -/
    sorry
  · -- bernoulliPolynomialRewrite: aggregate k recurrence steps
    constructor -- SDDRel
    /- Aggregate k recurrence steps to show allOutcomesExpansion ≈ F(G).
    Total error ≤ k × per-step error ≤ fromHToGError. -/
    sorry

/-- `lem:chernoff-bernoulli-matrix`. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (hnorm : ψ.IsNormalized)
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
  -- tail_le_one: bernoulliTailOperator k degree X ≤ 1
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  /- Paper: `lem:chernoff-bernoulli-matrix` (ld-pasting.tex lines 1670–1797).
  Core spectral/Chernoff bound: ev ψ (F(X)) ≥ 1 - κ/(1-θ) - exp(-θ²k/2).
  (1) Spectral decomposition: X = ∑ λ_i |v_i⟩⟨v_i|, so
      ev ψ (F(X)) = E_{i∼μ} F(λ_i).
  (2) Markov: Pr[λ_i ≥ θ] ≥ 1 - κ/(1-θ).
  (3) Scalar Chernoff: ∀p ≥ θ, F(p) ≥ 1 - exp(-θ²k/2)
      (using hk: 2d/θ ≤ k ⟹ p - d/k ≥ θ/2).
  (4) Combine: (1-κ/(1-θ))(1-exp(-θ²k/2)) ≥ 1-κ/(1-θ)-exp(-θ²k/2).
  Requires: spectral decomposition for Op ι, scalar Chernoff bound. -/
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  -- Chain the three completeness-chain lemmas (§9.4 of the paper)
  have _hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood family hcons hself hbound k
  constructor -- LdPastingNCompletenessStatement
  · exact hk -- largeEnough: 400 * m * d ≤ k
  · -- completenessBound
    constructor -- CompletenessAtLeast
    /- Paper: `cor:ld-pasting-N-completeness` (ld-pasting.tex lines 1798–1849).
    Chains: overAllOutcomes (ν₇) + fromHToG (ν₈) → SDDRel H vs F(G);
    chernoffBernoulliMatrix (θ = 1/(200m)): ev ψ F(G) ≥ 1-κ/(1-θ)-exp(...);
    SDDRel → mass transfer: ev ψ H ≥ ev ψ F(G) - √(ν₇+ν₈);
    parameter match: κ/(1-θ) ≤ κ(1+1/(100m)),
    exp(-θ²k/2) = exp(-k/(80000m²)).
    Requires: SDDRel → completeness transfer for Unit-indexed families. -/
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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedSubMeas params family k, ?_⟩
  have hconsistency :=
    (hAConsistency params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk).1
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk
  exact
    { largeEnough := hk
      constructedSubMeas := rfl
      pointConsistency := hconsistency
      completeness := hcompleteness.completenessBound }

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
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedMeasurement params family k, ?_⟩
  have hconsistency :=
    (hAConsistency params strategy eps delta gamma kappa zeta
      hgood family hcomplete hcons hself hbound k hk).2
  exact
    { largeEnough := hk
      constructedMeasurement := rfl
      pointConsistency := hconsistency }

end MIPStarRE.LDT.Pasting
