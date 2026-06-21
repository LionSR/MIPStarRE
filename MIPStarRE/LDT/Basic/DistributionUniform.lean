import MIPStarRE.LDT.Basic.Distribution

/-!
# Uniform subset estimates

This file contains estimates for the total variation distance between the
uniform distribution on a finite type and the uniform distribution on a
nonempty finite subset, together with averaging bounds for `[0,1]`-valued
functions.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

/-- On the selected subset, the pointwise absolute difference between the
ambient uniform distribution and the subset-uniform distribution has total mass
`1 - |s| / |α|`.

This is an elementary finite-sum identity used in the uniform-subset total
variation calculation. -/
private theorem sum_abs_weight_diff_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    ∑ a ∈ s,
      |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|
      = 1 - (s.card : Error) / (Fintype.card α : Error) := by
  classical
  have hs_card_ne_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hs_card_ne : (s.card : Error) ≠ 0 := by
    exact_mod_cast hs_card_ne_nat
  have hα_card_ne : (Fintype.card α : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs_pos : 0 < (s.card : Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hs_card_ne_nat
  have hs_le_univ_nat : s.card ≤ Fintype.card α := by
    simpa using Finset.card_le_univ s
  have hweight_le :
      1 / (Fintype.card α : Error) ≤ 1 / (s.card : Error) := by
    exact one_div_le_one_div_of_le hs_pos (by exact_mod_cast hs_le_univ_nat)
  have hconst :
      ∀ a ∈ s,
        |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|
          = (1 / (s.card : Error)) - (1 / (Fintype.card α : Error)) := by
    intro a ha
    rw [show (uniformDistribution α).weight a =
        1 / (Fintype.card α : Error) by
          simp [uniformDistribution]]
    rw [show (Distribution.uniformOnFinset s).weight a =
        if a ∈ s then 1 / (s.card : Error) else 0 by
          simp]
    rw [if_pos ha]
    rw [abs_of_nonpos (sub_nonpos.mpr hweight_le)]
    ring
  calc
    ∑ a ∈ s,
        |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|
      = ∑ a ∈ s,
          ((1 / (s.card : Error)) - (1 / (Fintype.card α : Error))) := by
          exact Finset.sum_congr rfl hconst
    _ = (s.card : Error) *
        ((1 / (s.card : Error)) - (1 / (Fintype.card α : Error))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = 1 - (s.card : Error) / (Fintype.card α : Error) := by
          field_simp [hs_card_ne, hα_card_ne]

/-- Total variation between the uniform distribution on a finite ambient type and
the uniform distribution on a nonempty finite subset.

This is the elementary finite identity
`TV(uniform α, uniform s) = 1 - |s| / |α|`, stated for the project
`Distribution` type. -/
theorem totalVariationDistance_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) =
      1 - (s.card : Error) / (Fintype.card α : Error) := by
  classical
  let outside : Finset α := Finset.univ.filter fun a => a ∉ s
  have hα_card_ne : (Fintype.card α : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hpartition_card : s.card + outside.card = Fintype.card α := by
    simpa [outside] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun a : α => a ∈ s))
  have hpartition_cast :
      (s.card : Error) + outside.card = (Fintype.card α : Error) := by
    exact_mod_cast hpartition_card
  have hdisj : Disjoint s outside := by
    rw [Finset.disjoint_left]
    intro a ha houtside
    exact (Finset.mem_filter.mp houtside).2 ha
  have hgood :=
    sum_abs_weight_diff_uniformDistribution_uniformOnFinset_eq (s := s) hs
  have hbad :
      ∑ a ∈ outside,
        |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|
        = 1 - (s.card : Error) / (Fintype.card α : Error) := by
    calc
      ∑ a ∈ outside,
          |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|
        = ∑ _a ∈ outside, (1 / (Fintype.card α : Error)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hnot : a ∉ s := (Finset.mem_filter.mp ha).2
            rw [show (uniformDistribution α).weight a =
                1 / (Fintype.card α : Error) by
                  simp [uniformDistribution]]
            rw [show (Distribution.uniformOnFinset s).weight a =
                if a ∈ s then 1 / (s.card : Error) else 0 by
                  simp]
            rw [if_neg hnot]
            simp
      _ = (outside.card : Error) / (Fintype.card α : Error) := by
            simp [div_eq_mul_inv]
      _ = 1 - (s.card : Error) / (Fintype.card α : Error) := by
            field_simp [hα_card_ne]
            nlinarith [hpartition_cast]
  have hsupp_union :
      (uniformDistribution α).support ∪ (Distribution.uniformOnFinset s).support =
        s ∪ outside := by
    ext a
    by_cases ha : a ∈ s
    · simp [uniformDistribution, outside, ha]
    · simp [uniformDistribution, outside, ha]
  rw [totalVariationDistance, hsupp_union, Finset.sum_union hdisj]
  rw [hgood, hbad]
  ring_nf

/-- A `[0,1]`-valued function averaged over a nonempty finite subset is bounded
by its ambient uniform average plus the total variation distance between the
two uniform distributions. -/
theorem avgOver_uniformOnFinset_le_uniformDistribution_add_totalVariationDistance
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty)
    (f : α → Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    avgOver (Distribution.uniformOnFinset s) f
      ≤ avgOver (uniformDistribution α) f
        + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
  classical
  let outside : Finset α := Finset.univ.filter fun a => a ∉ s
  have hs_card_ne_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hs_pos : 0 < (s.card : Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hs_card_ne_nat
  have hs_le_univ_nat : s.card ≤ Fintype.card α := by
    simpa using Finset.card_le_univ s
  have hweight_le :
      1 / (Fintype.card α : Error) ≤ 1 / (s.card : Error) := by
    exact one_div_le_one_div_of_le hs_pos (by exact_mod_cast hs_le_univ_nat)
  have htv_eq :=
    totalVariationDistance_uniformDistribution_uniformOnFinset_eq (s := s) hs
  have hgood :=
    sum_abs_weight_diff_uniformDistribution_uniformOnFinset_eq (s := s) hs
  have hsupport_term :
      avgOver (Distribution.uniformOnFinset s) f ≤
        ∑ a ∈ s, (uniformDistribution α).weight a * f a
          + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
    calc
      avgOver (Distribution.uniformOnFinset s) f
        = ∑ a ∈ s, (Distribution.uniformOnFinset s).weight a * f a := by
            simp [avgOver]
      _ ≤ ∑ a ∈ s,
            ((uniformDistribution α).weight a * f a +
              |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a|) := by
            refine Finset.sum_le_sum ?_
            intro a ha
            have hf_a_le := hf_le_one a
            have hw :
                (uniformDistribution α).weight a ≤
                  (Distribution.uniformOnFinset s).weight a := by
              rw [show (uniformDistribution α).weight a =
                  1 / (Fintype.card α : Error) by
                    simp [uniformDistribution]]
              rw [show (Distribution.uniformOnFinset s).weight a =
                  if a ∈ s then 1 / (s.card : Error) else 0 by
                    simp]
              rw [if_pos ha]
              exact hweight_le
            have habs :
                |(uniformDistribution α).weight a -
                    (Distribution.uniformOnFinset s).weight a| =
                  (Distribution.uniformOnFinset s).weight a -
                    (uniformDistribution α).weight a := by
              rw [abs_of_nonpos (sub_nonpos.mpr hw)]
              ring
            have hdelta_nonneg :
                0 ≤
                  (Distribution.uniformOnFinset s).weight a -
                    (uniformDistribution α).weight a := by
              linarith
            have hmul :
                ((Distribution.uniformOnFinset s).weight a - (uniformDistribution α).weight a)
                    * f a
                  ≤
                    (Distribution.uniformOnFinset s).weight a -
                      (uniformDistribution α).weight a := by
              have := mul_le_mul_of_nonneg_left hf_a_le hdelta_nonneg
              simpa [one_mul] using this
            have hsplit :
                (Distribution.uniformOnFinset s).weight a * f a =
                  (uniformDistribution α).weight a * f a +
                    ((Distribution.uniformOnFinset s).weight a -
                      (uniformDistribution α).weight a) * f a := by
              ring
            rw [hsplit, habs]
            linarith
      _ = ∑ a ∈ s, (uniformDistribution α).weight a * f a +
            ∑ a ∈ s,
              |(uniformDistribution α).weight a - (Distribution.uniformOnFinset s).weight a| := by
            rw [Finset.sum_add_distrib]
      _ =
          ∑ a ∈ s, (uniformDistribution α).weight a * f a
            + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
          rw [hgood, htv_eq]
  have hdisj : Disjoint s outside := by
    rw [Finset.disjoint_left]
    intro a ha houtside
    exact (Finset.mem_filter.mp houtside).2 ha
  have huniform_support : (uniformDistribution α).support = s ∪ outside := by
    ext a
    by_cases ha : a ∈ s
    · simp [uniformDistribution, outside, ha]
    · simp [uniformDistribution, outside, ha]
  have hsupport_le_uniform :
      ∑ a ∈ s, (uniformDistribution α).weight a * f a
        ≤ avgOver (uniformDistribution α) f := by
    have hbad_nonneg :
        0 ≤ ∑ a ∈ outside, (uniformDistribution α).weight a * f a := by
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg ((uniformDistribution α).nonnegative a) (hf_nonneg a)
    calc
      ∑ a ∈ s, (uniformDistribution α).weight a * f a
        ≤ ∑ a ∈ s, (uniformDistribution α).weight a * f a +
            ∑ a ∈ outside, (uniformDistribution α).weight a * f a := by
              linarith
      _ = avgOver (uniformDistribution α) f := by
            rw [avgOver, huniform_support, Finset.sum_union hdisj]
  calc
    avgOver (Distribution.uniformOnFinset s) f
      ≤ ∑ a ∈ s, (uniformDistribution α).weight a * f a
          + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) :=
        hsupport_term
    _ ≤ avgOver (uniformDistribution α) f
          + totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) := by
        linarith [hsupport_le_uniform]

end MIPStarRE.LDT
