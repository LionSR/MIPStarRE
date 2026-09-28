import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.TruncationCombinatorics

/-!
# Global rank allocation for state-dependent orthogonalization

The proof of `lem:state-dependent-orthogonalization` in
`blueprint/src/chapter/low_degree_simplified.tex` selects the largest `d`
weighted eigenvectors across all measurement outcomes.  This file proves the
finite-dimensional linear-programming inequality behind that selection.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:state-dependent-orthogonalization`, equation `eq:selected-overlap`.
- `references/ldt-paper/orthonormalization.tex`, Section 5, for the original
  orthogonalization theorem whose conclusion the simplified proof strengthens.
-/

open scoped BigOperators

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- A set of the `d` largest weights dominates every fractional selection of
total mass `d`.  This is the global rank-allocation inequality in the simplified
proof, before the weights are specialized to spectral overlap weights
`λ_{a,j} φ(|v_{a,j}⟩⟨v_{a,j}|)`. -/
theorem largest_weights_dominate_fractional {α : Type*}
    [Fintype α]
    (w x : α → ℝ) (d : ℕ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_le_one : ∀ i, x i ≤ 1)
    (hx_sum : ∑ i, x i = d) :
    ∃ L : Finset α, L.card = d ∧
      ∑ i ∈ L, w i ≥ ∑ i, x i * w i := by
  classical
  have hd : d ≤ Fintype.card α := by
    have hbound : (∑ i, x i) ≤ ∑ _i : α, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hx_le_one i)
    have hsum_one : (∑ _i : α, (1 : ℝ)) = Fintype.card α := by simp
    rw [hx_sum, hsum_one] at hbound
    exact_mod_cast hbound
  obtain ⟨L, hLcard, horder⟩ :=
    Truncation.exists_large_subset_ordered w hd
  refine ⟨L, hLcard, ?_⟩
  by_cases hLempty : L.Nonempty
  · obtain ⟨threshold, hthreshold_mem, hthreshold_min⟩ :=
      Finset.exists_min_image L w hLempty
    have hselected :
        ∑ i ∈ L, ((1 : ℝ) - x i) * w i ≥
          w threshold * ∑ i ∈ L, ((1 : ℝ) - x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (hthreshold_min i hi) (sub_nonneg.mpr (hx_le_one i))
    have hunselected :
        ∑ i ∈ (Lᶜ : Finset α), x i * w i ≤
          w threshold * ∑ i ∈ (Lᶜ : Finset α), x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (horder i hi threshold hthreshold_mem) (hx_nonneg i)
    have hbalance :
        ∑ i ∈ L, ((1 : ℝ) - x i) =
          ∑ i ∈ (Lᶜ : Finset α), x i := by
      have hpartition := Finset.sum_add_sum_compl (s := L) (f := x)
      have hcard_real : (L.card : ℝ) = (d : ℝ) := by exact_mod_cast hLcard
      calc
        ∑ i ∈ L, ((1 : ℝ) - x i) = (L.card : ℝ) - ∑ i ∈ L, x i := by
          simp [Finset.sum_sub_distrib]
        _ = (d : ℝ) - ∑ i ∈ L, x i := by rw [hcard_real]
        _ = ∑ i ∈ (Lᶜ : Finset α), x i := by linarith [hpartition, hx_sum]
    have hsplit := Finset.sum_add_sum_compl (s := L) (f := fun i => x i * w i)
    have hselected_eq :
        ∑ i ∈ L, ((1 : ℝ) - x i) * w i =
          (∑ i ∈ L, w i) - ∑ i ∈ L, x i * w i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hbalance, hselected_eq] at hselected
    linarith
  · have hL : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLempty
    have hd_zero : d = 0 := by simpa [hL] using hLcard.symm
    have hx_zero : ∀ i, x i = 0 := by
      intro i
      have hxi_le : x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx_nonneg j) (Finset.mem_univ i)
      have hsum_zero : (∑ j, x j) = 0 := by simpa [hd_zero] using hx_sum
      linarith only [hxi_le, hx_nonneg i, hsum_zero]
    simp [hL, hx_zero]

/-- The numerical form of `eq:selected-overlap`: when `λ` are measurement
eigenvalues and `r` are state weights, selecting the largest `d` values of
`λᵢ rᵢ` captures at least the quadratic spectral mass `Σᵢ λᵢ² rᵢ`.
The operator-level interpretation is supplied by the spectral projector
construction still required for the full orthogonalization theorem. -/
theorem selected_spectral_overlap {α : Type*} [Fintype α]
    (lam r : α → ℝ) (d : ℕ)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hlam_le_one : ∀ i, lam i ≤ 1)
    (hlam_sum : ∑ i, lam i = d) :
    ∃ L : Finset α, L.card = d ∧
      ∑ i ∈ L, lam i * r i ≥ ∑ i, (lam i) ^ 2 * r i := by
  obtain ⟨L, hLcard, hbound⟩ :=
    largest_weights_dominate_fractional (fun i => lam i * r i) lam d
      hlam_nonneg hlam_le_one hlam_sum
  refine ⟨L, hLcard, ?_⟩
  simpa [pow_two, mul_assoc] using hbound

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
