import MIPStarRE.LDT.Pasting.BridgeLemmas.Consistency.BadMass

/-!
# Section 12 pasting: bridge option-lift lemmas

Option-lift and completion helpers for comparing submeasurements with completed measurements.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma completeSubMeas_toSubMeas_eq_optionLiftSubMeas
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    (completeSubMeas A).toSubMeas = optionLiftSubMeas A := by
  refine SubMeas.ext ?_ ?_
  · intro oa
    cases oa <;> rfl
  · rfl

lemma gHatIdxMeas_toSubMeas_eq_optionLiftSubMeas
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    ((gHatIdxMeas params family x).toSubMeas) =
      optionLiftSubMeas ((family.meas x).toSubMeas) := by
  simpa [gHatIdxMeas] using
    completeSubMeas_toSubMeas_eq_optionLiftSubMeas ((family.meas x).toSubMeas)

lemma optionLiftSubMeas_outcome_none
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    (optionLiftSubMeas A).outcome none = 1 - A.total := by
  rfl

lemma optionLiftMeasurement_outcome_none_eq_zero
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) :
    (optionLiftMeasurement B).outcome none = 0 := by
  simp [optionLiftMeasurement, optionLiftSubMeas, B.total_eq_one]

noncomputable def optionSomeSubMeas
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas (Option α) ι) : SubMeas α ι where
  outcome a := A.outcome (some a)
  total := ∑ a : α, A.outcome (some a)
  outcome_pos a := A.outcome_pos (some a)
  sum_eq_total := rfl
  total_le_one := by
    have hsplit : A.outcome none + ∑ a : α, A.outcome (some a) = A.total := by
      simpa [Fintype.sum_option, add_comm] using A.sum_eq_total
    calc
      (∑ a : α, A.outcome (some a)) ≤ A.outcome none + ∑ a : α, A.outcome (some a) := by
        exact le_add_of_nonneg_left (A.outcome_pos none)
      _ = A.total := hsplit
      _ ≤ 1 := A.total_le_one

lemma optionSomeSubMeas_none_add_total_eq_total
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas (Option α) ι) :
    A.outcome none + (optionSomeSubMeas A).total = A.total := by
  simpa [optionSomeSubMeas, Fintype.sum_option, add_comm] using A.sum_eq_total

lemma optionSomeSubMeas_total_eq_total_of_none_eq_zero
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas (Option α) ι)
    (hnone : A.outcome none = 0) :
    (optionSomeSubMeas A).total = A.total := by
  have hsplit := optionSomeSubMeas_none_add_total_eq_total A
  rw [hnone, zero_add] at hsplit
  exact hsplit

lemma qBipartiteMatchMass_option_eq_none_add_some
    {α : Type*}
    {ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas (Option α) ιA) (B : SubMeas (Option α) ιB) :
    qBipartiteMatchMass ψ A B =
      ev ψ (opTensor (A.outcome none) (B.outcome none)) +
        qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
  unfold qBipartiteMatchMass optionSomeSubMeas
  rw [Fintype.sum_option]

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
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left, ih]

lemma opTensor_smul_right
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor A ((c : ℂ) • B) = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm, mul_assoc]

lemma opTensor_sum_right
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA)
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιB) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_right, ih]

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

lemma avgOver_distinct_indicator_le_avgOver_uniform_add_tv
    (params : Parameters) [FieldModel params.q]
    (k : ℕ) (hk : k ≤ params.q)
    (P : PointTuple params k → Prop) [DecidablePred P] :
    avgOver (distinctTupleDistribution params k)
        (fun xs => if P xs then (1 : Error) else 0)
      ≤ avgOver (uniformDistribution (PointTuple params k))
          (fun xs => if P xs then (1 : Error) else 0)
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  let Q : PointTuple params k → Prop := fun xs => ¬ P xs
  have hforward := avgOver_uniform_indicator_le_avgOver_distinct_add_tv params k hk Q
  have huniform_one :
      avgOver (uniformDistribution (PointTuple params k))
        (fun _ => (1 : Error)) = 1 := by
    simp [avgOver, uniformDistribution, PointTuple, Fintype.card_fin]
  have hdistinct_one :
      avgOver (distinctTupleDistribution params k)
        (fun _ => (1 : Error)) = 1 := by
    unfold avgOver
    simpa using distinctTupleDistribution_weight_sum_eq_one_of_le params k hk
  have huniform_compl :
      avgOver (uniformDistribution (PointTuple params k))
          (fun xs => if Q xs then (1 : Error) else 0)
        = 1 - avgOver (uniformDistribution (PointTuple params k))
            (fun xs => if P xs then (1 : Error) else 0) := by
    calc
      avgOver (uniformDistribution (PointTuple params k))
          (fun xs => if Q xs then (1 : Error) else 0)
        = avgOver (uniformDistribution (PointTuple params k))
            (fun xs => (1 : Error) - (if P xs then (1 : Error) else 0)) := by
              apply avgOver_congr
              intro xs
              by_cases hPx : P xs <;> simp [Q, hPx]
      _ = avgOver (uniformDistribution (PointTuple params k))
            (fun _ => (1 : Error)) -
          avgOver (uniformDistribution (PointTuple params k))
            (fun xs => if P xs then (1 : Error) else 0) := by
              rw [avgOver_sub]
      _ = 1 - avgOver (uniformDistribution (PointTuple params k))
            (fun xs => if P xs then (1 : Error) else 0) := by
              rw [huniform_one]
  have hdistinct_compl :
      avgOver (distinctTupleDistribution params k)
          (fun xs => if Q xs then (1 : Error) else 0)
        = 1 - avgOver (distinctTupleDistribution params k)
            (fun xs => if P xs then (1 : Error) else 0) := by
    calc
      avgOver (distinctTupleDistribution params k)
          (fun xs => if Q xs then (1 : Error) else 0)
        = avgOver (distinctTupleDistribution params k)
            (fun xs => (1 : Error) - (if P xs then (1 : Error) else 0)) := by
              apply avgOver_congr
              intro xs
              by_cases hPx : P xs <;> simp [Q, hPx]
      _ = avgOver (distinctTupleDistribution params k)
            (fun _ => (1 : Error)) -
          avgOver (distinctTupleDistribution params k)
            (fun xs => if P xs then (1 : Error) else 0) := by
              rw [avgOver_sub]
      _ = 1 - avgOver (distinctTupleDistribution params k)
            (fun xs => if P xs then (1 : Error) else 0) := by
              rw [hdistinct_one]
  have htv_nonneg :
      0 ≤ totalVariationDistance
        (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k) := by
    unfold totalVariationDistance
    positivity
  rw [huniform_compl, hdistinct_compl] at hforward
  linarith

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
  have hbad_mass :
      ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    calc
      ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs
        = ∑ xs ∈ bad, (1 / ((params.q : Error) ^ k)) := by
            apply Finset.sum_congr rfl
            intro xs hxs
            simp [uniformDistribution, PointTuple, Fintype.card_fin]
      _ = (bad.card : Error) / ((params.q : Error) ^ k) := by
            simp [div_eq_mul_inv]
      _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
            field_simp [hqpow_ne]
            nlinarith [hpartition_cast]
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
      _ = (support.card : Error) * ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
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
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
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
            have hFx_nonneg := hF_nonneg xs
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
            totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
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
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := hsupport_term
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) F +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
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
    [DecidableEq Question] [Fintype Outcome]
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
    [DecidableEq Question] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold avgOver averageIdxSubMeas
  rw [opTensor_averageOperatorOverDistribution_left]
  unfold averageOperatorOverDistribution
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using ev_scale ψ (𝒟.weight q) (opTensor (A q).total B.total)

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [DecidableEq Question] [Fintype Outcome]
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
          (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
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

lemma qBipartiteConsDefect_option_le_none_left_add_some
    {α : Type*}
    {ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas (Option α) ιA) (B : SubMeas (Option α) ιB)
    (hBnone : B.outcome none = 0) :
    qBipartiteConsDefect ψ A B ≤
      ev ψ (opTensor (A.outcome none) B.total) +
        qBipartiteConsDefect ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
  have hBtotal : (optionSomeSubMeas B).total = B.total :=
    optionSomeSubMeas_total_eq_total_of_none_eq_zero B hBnone
  have hmatch :
      qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
    rw [qBipartiteMatchMass_option_eq_none_add_some ψ A B, hBnone]
    simp [opTensor, ev]
  have ha_nonneg : 0 ≤ ev ψ (opTensor (A.outcome none) B.total) := by
    exact ev_nonneg_of_psd ψ _ <|
      opTensor_nonneg (A.outcome_pos none) B.total_nonneg
  have hsplitA := optionSomeSubMeas_none_add_total_eq_total A
  have hinner :
      ev ψ (opTensor A.total B.total) -
          qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) =
        ev ψ (opTensor (A.outcome none) B.total) +
          (ev ψ (opTensor (optionSomeSubMeas A).total (optionSomeSubMeas B).total) -
            qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B)) := by
    calc
      ev ψ (opTensor A.total B.total) -
          qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B)
        = ev ψ (opTensor (A.outcome none + (optionSomeSubMeas A).total) B.total) -
            qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
              rw [optionSomeSubMeas_none_add_total_eq_total A]
        _ = ev ψ
              (opTensor (A.outcome none) B.total +
                opTensor (optionSomeSubMeas A).total B.total) -
              qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
                rw [opTensor_add_left]
        _ = (ev ψ (opTensor (A.outcome none) B.total) +
              ev ψ (opTensor (optionSomeSubMeas A).total B.total)) -
              qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B) := by
                rw [ev_add]
        _ = ev ψ (opTensor (A.outcome none) B.total) +
              (ev ψ (opTensor (optionSomeSubMeas A).total B.total) -
                qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B)) := by
                ring
        _ = ev ψ (opTensor (A.outcome none) B.total) +
              (ev ψ (opTensor (optionSomeSubMeas A).total (optionSomeSubMeas B).total) -
                qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B)) := by
                rw [hBtotal]
  change max 0 (ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B) ≤
      ev ψ (opTensor (A.outcome none) B.total) +
        max 0
          (ev ψ (opTensor (optionSomeSubMeas A).total (optionSomeSubMeas B).total) -
            qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B))
  rw [hmatch, hinner]
  exact max_zero_add_le
    (ev ψ (opTensor (A.outcome none) B.total))
    (ev ψ (opTensor (optionSomeSubMeas A).total (optionSomeSubMeas B).total) -
      qBipartiteMatchMass ψ (optionSomeSubMeas A) (optionSomeSubMeas B))
    ha_nonneg

lemma optionSomeSubMeas_optionLiftSubMeas_eq
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    optionSomeSubMeas (optionLiftSubMeas A) = A := by
  refine SubMeas.ext ?_ ?_
  · intro a
    rfl
  · simpa [optionSomeSubMeas, optionLiftSubMeas] using A.sum_eq_total

lemma optionSomeSubMeas_optionLiftMeasurement_eq
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) :
    optionSomeSubMeas (optionLiftMeasurement B) = B.toSubMeas := by
  simpa [optionLiftMeasurement] using optionSomeSubMeas_optionLiftSubMeas_eq B.toSubMeas

lemma qBipartiteConsDefect_optionLiftMeasurement_le
    {α : Type*}
    {ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas α ιA) (B : Measurement α ιB) :
    qBipartiteConsDefect ψ (optionLiftSubMeas A) (optionLiftMeasurement B) ≤
      ev ψ (opTensor ((optionLiftSubMeas A).outcome none) 1) +
        qBipartiteConsDefect ψ A B.toSubMeas := by
  have hbase := qBipartiteConsDefect_option_le_none_left_add_some ψ
    (optionLiftSubMeas A) (optionLiftMeasurement B)
    (optionLiftMeasurement_outcome_none_eq_zero B)
  simpa [optionLiftMeasurement, optionLiftSubMeas_outcome_none,
    optionSomeSubMeas_optionLiftSubMeas_eq, optionSomeSubMeas_optionLiftMeasurement_eq,
    B.total_eq_one] using hbase

lemma processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome false = 0 := by
  rw [show ((ldSandwichLineOnePointRightFamily params strategy family k i) q) =
      postprocess (verticalLineMeasurementFamily params strategy q.1)
        (fun f => some (f (q.2 ⟨i, hi⟩))) by
      simp [ldSandwichLineOnePointRightFamily, hi]]
  rw [postprocess_postprocess]
  simp [postprocess, Function.comp, Option.isSome]

lemma processed_ldSandwichLineOnePointRightFamily_isSome_true_eq_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome true =
      (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).total := by
  let B := postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome
  have hfalse : B.outcome false = 0 := by
    simpa [B] using processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
      params strategy family k i hi q
  have hsum : B.outcome false + B.outcome true = B.total := by
    simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
  calc
    B.outcome true = B.outcome false + B.outcome true := by simp [hfalse]
    _ = B.total := by simpa [add_comm] using hsum

lemma ldSandwichLineOnePoint_option_isSome_map
    {α β : Type*} (f : α → β) (o : Option α) :
    Option.isSome (Option.map f o) = Option.isSome o := by
  cases o <;> rfl

lemma ldSandwichLineOnePointRightFamily_isSome_true
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome =
      postprocess (verticalLineMeasurementFamily params strategy q.1) (fun _ : AxisLinePolynomial params.next => true) := by
  refine SubMeas.ext ?_ ?_
  · intro b
    cases b
    · calc
        (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome false
          = 0 := by
              exact processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
                params strategy family k i hi q
        _ = (postprocess (verticalLineMeasurementFamily params strategy q.1)
              (fun _ : AxisLinePolynomial params.next => true)).outcome false := by
              simp [postprocess]
    · calc
        (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome true
          = (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
              Option.isSome).total := by
                exact processed_ldSandwichLineOnePointRightFamily_isSome_true_eq_total
                  params strategy family k i hi q
        _ = (verticalLineMeasurementFamily params strategy q.1).total := by
              simp [ldSandwichLineOnePointRightFamily, hi, postprocess_total]
        _ = (postprocess (verticalLineMeasurementFamily params strategy q.1)
              (fun _ : AxisLinePolynomial params.next => true)).outcome true := by
              simp [postprocess, (verticalLineMeasurementFamily params strategy q.1).sum_eq_total]
  · simp [ldSandwichLineOnePointRightFamily, hi, postprocess_total]

lemma ldSandwichLineOnePointLeftFamily_isSome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome =
      postprocess (gHatSandwichFamily params family k q.2) (fun gs => Option.isSome (gs ⟨i, hi⟩)) := by
  rw [show ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) =
      postprocess (gHatSandwichFamily params family k q.2)
        (fun gs => Option.map (fun g => g q.1) (gs ⟨i, hi⟩)) by
      simp [ldSandwichLineOnePointLeftFamily, hi]]
  rw [postprocess_postprocess]
  congr 1
  funext gs
  simp [Function.comp, ldSandwichLineOnePoint_option_isSome_map]

end MIPStarRE.LDT.Pasting
