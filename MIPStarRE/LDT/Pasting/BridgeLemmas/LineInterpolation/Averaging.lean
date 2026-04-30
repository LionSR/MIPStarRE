import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Line interpolation: averaging and tensor helpers

Tensor/average helper lemmas and total-variation comparison used across the
line interpolation error bounding chain.

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

lemma opTensor_smul_left
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor ((c : ℂ) • A) B = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

lemma opTensor_sum_left
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

lemma opTensor_averageOperatorOverDistribution_left
    {Question ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (𝒟 : Distribution Question)
    (A : Question → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (averageOperatorOverDistribution 𝒟 A) B =
      averageOperatorOverDistribution 𝒟 (fun q => opTensor (A q) B) := by
  classical
  unfold averageOperatorOverDistribution
  rw [opTensor_sum_left]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using opTensor_smul_left (c := 𝒟.weight q) (A := A q) (B := B)

lemma avgOver_sub
    {α : Type*}
    (𝒟 : Distribution α)
    (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) = avgOver 𝒟 f - avgOver 𝒟 g := by
  unfold avgOver
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv
    (params : Parameters) [FieldModel params.q]
    (k : ℕ) (hk : k ≤ params.q)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
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
      (Fintype.card_congr e).trans Fintype.card_embedding_eq
  have hqpow_ne : ((params.q : Error) ^ k) ≠ 0 := by
    have hq_ne : (params.q : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hq)
    exact pow_ne_zero k hq_ne
  have hsupport_nonempty : support.Nonempty := by
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
    exact one_div_le_one_div_of_le hsupport_pos (by exact_mod_cast hsupport_le_pow_nat)
  have hpartition_card :
      support.card + bad.card = params.q ^ k := by
    simpa [support, bad, PointTuple, Fintype.card_fun, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (PointTuple params k)))
        (p := fun xs : PointTuple params k => Function.Injective xs))
  have hpartition_cast :
      (support.card : Error) + bad.card = (params.q : Error) ^ k := by
    exact_mod_cast hpartition_card
  have hdisj : Disjoint support bad := by
    simpa [support, bad] using
      (Finset.disjoint_filter_filter_not
        (Finset.univ : Finset (PointTuple params k))
        (Finset.univ : Finset (PointTuple params k))
        (fun xs : PointTuple params k => Function.Injective xs))
  have huniform_support :
      (uniformDistribution (PointTuple params k)).support = support ∪ bad := by
    simp [uniformDistribution, support, bad, Finset.filter_union_filter_not_eq]
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
      _ = (support.card : Error) *
          ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
            field_simp [hsupport_card_ne, hqpow_ne]
  have htv_eq :
      totalVariationDistance (uniformDistribution (PointTuple params k))
          (distinctTupleDistribution params k)
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    have hsupp_union :
        (uniformDistribution (PointTuple params k)).support
          ∪ (distinctTupleDistribution params k).support
          = support ∪ bad := by
      simp [uniformDistribution, distinctTupleDistribution, support, bad,
        Finset.filter_union_filter_not_eq]
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
    rw [totalVariationDistance, hsupp_union, Finset.sum_union hdisj]
    simp [hgood, hbad]
    ring
  have hsupport_term :
      avgOver (distinctTupleDistribution params k) F ≤
        ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := by
    calc
      avgOver (distinctTupleDistribution params k) F
        = ∑ xs ∈ support, (distinctTupleDistribution params k).weight xs * F xs := by
            simp [avgOver, distinctTupleDistribution, support]
      _ ≤ ∑ xs ∈ support,
            ((uniformDistribution (PointTuple params k)).weight xs * F xs +
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs|) := by
            refine Finset.sum_le_sum ?_
            intro xs hxs
            have hFx_le := hF_le_one xs
            have hw :
                (uniformDistribution (PointTuple params k)).weight xs ≤
                  (distinctTupleDistribution params k).weight xs := by
              rw [show (uniformDistribution (PointTuple params k)).weight xs =
                  1 / ((params.q : Error) ^ k) by
                    simp [uniformDistribution, PointTuple, Fintype.card_fin]]
              rw [show (distinctTupleDistribution params k).weight xs =
                  if xs ∈ support then 1 / (support.card : Error) else 0 by
                    simp [distinctTupleDistribution, support]]
              rw [if_pos hxs]
              exact hweight_le
            have habs :
                |(uniformDistribution (PointTuple params k)).weight xs -
                    (distinctTupleDistribution params k).weight xs| =
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              rw [abs_of_nonpos (sub_nonpos.mpr hw)]
              ring
            have hdelta_nonneg :
                0 ≤ (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              linarith
            have hmul :
                ((distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs) * F xs ≤
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              have := mul_le_mul_of_nonneg_left hFx_le hdelta_nonneg
              simpa [one_mul] using this
            have hsplit :
                (distinctTupleDistribution params k).weight xs * F xs =
                  (uniformDistribution (PointTuple params k)).weight xs * F xs +
                    ((distinctTupleDistribution params k).weight xs -
                      (uniformDistribution (PointTuple params k)).weight xs) * F xs := by
              ring
            rw [hsplit]
            rw [habs]
            linarith
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ support,
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs| := by
            rw [Finset.sum_add_distrib]
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            totalVariationDistance (uniformDistribution (PointTuple params k)) (
                distinctTupleDistribution params k) := by
            rw [hgood, htv_eq]
  have hsupport_le_uniform :
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs ≤
        avgOver (uniformDistribution (PointTuple params k)) F := by
    have hbad_nonneg :
        0 ≤ ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
      exact Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
    calc
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs
        ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
              linarith
      _ = avgOver (uniformDistribution (PointTuple params k)) F := by
            rw [avgOver, huniform_support, Finset.sum_union hdisj]
  calc
    avgOver (distinctTupleDistribution params k) F
      ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := hsupport_term
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) F +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := by
            linarith [hsupport_le_uniform]

lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
    (params : Parameters) [FieldModel params.q]
    (k : ℕ)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  by_cases hk : k ≤ params.q
  · exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk F hF_nonneg hF_le_one
  · have hkq : params.q < k := lt_of_not_ge hk
    let support : Finset (PointTuple params k) :=
      Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
    have hsupport_card : support.card = params.q.descFactorial k := by
      rw [← Fintype.card_coe]
      let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
        Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
      simpa [support, Finset.mem_filter] using
        (Fintype.card_congr e).trans Fintype.card_embedding_eq
    have hsupport_empty : support = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hsupport_card]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hkq
    have hdistinct_zero : avgOver (distinctTupleDistribution params k) F = 0 := by
      unfold avgOver
      simp [distinctTupleDistribution, support, hsupport_empty]
    have hright_nonneg :
        0 ≤ avgOver (uniformDistribution (PointTuple params k)) F +
            totalVariationDistance
              (uniformDistribution (PointTuple params k))
              (distinctTupleDistribution params k) := by
      have hunif_nonneg : 0 ≤ avgOver (uniformDistribution (PointTuple params k)) F := by
        unfold avgOver
        exact Finset.sum_nonneg fun xs _ =>
          mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
      have htv_nonneg :
          0 ≤ totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
        unfold totalVariationDistance
        positivity
      linarith
    rw [hdistinct_zero]
    exact hright_nonneg

lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass avgOver averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a,
          ev ψ
            (averageOperatorOverDistribution 𝒟
              (fun q => opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact congrArg (ev ψ)
                (opTensor_averageOperatorOverDistribution_left 𝒟
                  (fun q => (A q).outcome a) (B.outcome a))
    _ = ∑ a, ∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          unfold averageOperatorOverDistribution
          rw [ev_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro q _
          simpa using ev_scale ψ (𝒟.weight q)
            (opTensor ((A q).outcome a) (B.outcome a))
    _ = ∑ q ∈ 𝒟.support, ∑ a, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          rw [Finset.sum_comm]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [← Finset.mul_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold avgOver averageIdxSubMeas
  change ev ψ (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).total)) B.total) = _
  rw [opTensor_averageOperatorOverDistribution_left]
  unfold averageOperatorOverDistribution
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using ev_scale ψ (𝒟.weight q) (opTensor (A q).total B.total)

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

end MIPStarRE.LDT.Pasting
