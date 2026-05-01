import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt

/-!
# Section 5 — Combinatorial core of the `r > d` truncation branch

Helper lemmas for the `r > d` branch of `lem:projective-low-rank-sum`
(`references/ldt-paper/orthonormalization.tex:559-658`).

Given a finite family of overlap values `f : α → ℝ` (with `α` the pair index set
`{(a, i)}` carrying `r = |α|` entries) and a chosen `Large ⊂ α` of size
`d < r` such that every `Small = Lᶜ` entry has overlap `≤` every `Large` entry,
the paper derives

* `|Large| * ∑_{Small} f ≤ |Small| * ∑_{Large} f` (pairwise double-counting),
* `r * ∑_{Small} f ≤ |Small| * ∑_{α} f` (partition bound).

We then combine this with the global `R ≤ (1 + 2√ζ) I` estimate to obtain
`∑_{Small} f ≤ 4√ζ` when `ζ ≤ 1/4`, which is the combinatorial heart of the
paper's `4√ζ` truncation error.

These lemmas do **not** depend on the matrix/spectral scaffolding in
`QXPLayer/Core.lean` or `QXPLayer/RankReduction.lean`; they are pure
combinatorics over a chosen partition. The per-projector orthonormal range
decomposition is available as `MIPStarRE.Quantum.IsProj.rangeONB`; the concrete
`Large/Small` choice and truncated projectors are assembled in
`QXPLayer/RankReduction.lean`.

## References

* `references/ldt-paper/orthonormalization.tex` lines 559–658
  (proof of `lem:projective-low-rank-sum`, `r > d` branch).
-/

open scoped BigOperators

namespace MIPStarRE.LDT.MakingMeasurementsProjective.Truncation

/-- Choose `d` elements with the largest values of `f`, breaking ties
arbitrarily. The resulting `Large` set has the paper's ordering property:
every element outside `Large` has value at most every element of `Large`. -/
lemma exists_large_subset_ordered {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
    ∃ L : Finset α, L.card = d ∧
      ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l := by
  classical
  let candidates : Finset (Finset α) := (Finset.univ : Finset α).powersetCard d
  have hcandidates : candidates.Nonempty := by
    simpa [candidates] using
      (Finset.powersetCard_nonempty_of_le (s := (Finset.univ : Finset α)) hd)
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image candidates (fun T : Finset α => ∑ x ∈ T, f x) hcandidates
  have hL_card : L.card = d := (Finset.mem_powersetCard.mp hLmem).2
  refine ⟨L, hL_card, ?_⟩
  intro s hs l hl
  by_contra hnot
  have hlt : f l < f s := lt_of_not_ge hnot
  have hs_not_mem : s ∉ L := by
    simpa using hs
  let L' : Finset α := insert s (L.erase l)
  have hL'_card : L'.card = d := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hcard_erase : (L.erase l).card = d - 1 := by
      rw [Finset.card_erase_of_mem hl, hL_card]
    have hd_pos : 0 < d := by
      rw [← hL_card]
      exact Finset.card_pos.mpr ⟨l, hl⟩
    calc
      L'.card = (L.erase l).card + 1 := by rw [Finset.card_insert_of_notMem hs_erase]
      _ = d := by omega
  have hL'_mem : L' ∈ candidates := by
    rw [Finset.mem_powersetCard]
    exact ⟨by intro x hx; simp, hL'_card⟩
  have hsum_L' : ∑ x ∈ L', f x = (∑ x ∈ L, f x) - f l + f s := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hsum_erase : ∑ x ∈ L.erase l, f x = (∑ x ∈ L, f x) - f l := by
      have h := Finset.add_sum_erase L f hl
      linarith
    calc
      ∑ x ∈ L', f x = f s + ∑ x ∈ L.erase l, f x := by
        simp [L', hs_erase]
      _ = (∑ x ∈ L, f x) - f l + f s := by
        rw [hsum_erase]
        ring
  have hstrict : (∑ x ∈ L, f x) < ∑ x ∈ L', f x := by
    rw [hsum_L']
    linarith
  exact not_lt_of_ge (hLmax L' hL'_mem) hstrict

/-- **Pairwise ordered double-counting.**

If every element of `S` has value at most every element of `L`, the sum over `S`
scaled by `|L|` is dominated by the sum over `L` scaled by `|S|`. Matches the
paper's inequality `∑_{Small} o ≤ (|Small|/r) · ∑ o` when `L ∪ S` exhausts the
index set. -/
lemma card_mul_sum_small_le {α : Type*} {L S : Finset α}
    {f : α → ℝ} (hf : ∀ s ∈ S, ∀ l ∈ L, f s ≤ f l) :
    (L.card : ℝ) * (∑ s ∈ S, f s) ≤ (S.card : ℝ) * (∑ l ∈ L, f l) := by
  classical
  have hL :
      (L.card : ℝ) * (∑ s ∈ S, f s) = ∑ s ∈ S, ∑ _l ∈ L, f s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  have hR :
      (S.card : ℝ) * (∑ l ∈ L, f l) = ∑ l ∈ L, ∑ _s ∈ S, f l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro l hl
  refine Finset.sum_le_sum ?_
  intro s hs
  exact hf s hs l hl

/-- **Partition-total form of the pairwise bound.**

If `S = Lᶜ`, the paper's `r · ∑_{Small} o ≤ |Small| · ∑ o` follows from
`card_mul_sum_small_le` after splitting `∑ x, f x = ∑_L f + ∑_{Lᶜ} f`. -/
lemma card_univ_mul_sum_compl_le {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α) {f : α → ℝ}
    (hf : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l) :
    (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
      (Lᶜ.card : ℝ) * (∑ x, f x) := by
  classical
  have hcard_nat : L.card + Lᶜ.card = Fintype.card α := Finset.card_add_card_compl L
  have hcard : (Fintype.card α : ℝ) = (L.card : ℝ) + (Lᶜ.card : ℝ) := by
    exact_mod_cast hcard_nat.symm
  have hunion : ∑ x, f x = (∑ l ∈ L, f l) + ∑ s ∈ (Lᶜ : Finset α), f s := by
    have := Finset.sum_add_sum_compl (s := L) (f := f)
    linarith
  have hbase := card_mul_sum_small_le (L := L) (S := (Lᶜ : Finset α)) (f := f) hf
  calc
    (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s)
        = ((L.card : ℝ) + (Lᶜ.card : ℝ)) * (∑ s ∈ (Lᶜ : Finset α), f s) := by
              rw [hcard]
    _ = (L.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) +
          (Lᶜ.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) := by ring
    _ ≤ (Lᶜ.card : ℝ) * (∑ l ∈ L, f l) +
          (Lᶜ.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) := by
              linarith [hbase]
    _ = (Lᶜ.card : ℝ) * ((∑ l ∈ L, f l) + ∑ s ∈ (Lᶜ : Finset α), f s) := by ring
    _ = (Lᶜ.card : ℝ) * (∑ x, f x) := by rw [← hunion]

/-- **Small-overlap sum bound.**

Assuming the paper's inputs:

* `L.card = d` with `d < |α|`,
* `|α| ≤ (1 + 2√ζ) · d`,
* every `Small = Lᶜ` entry has value at most every `Large = L` entry,
* `∑ x, f x ≤ 1 + 2√ζ`,
* `0 ≤ ζ ≤ 1/4`,

this yields `∑_{Small} f ≤ 4√ζ`, matching `eq:small-overlaps` in the paper. The
Lean statement is slightly stronger than the paper's: it does not need `f ≥ 0`,
since the ordering hypothesis and partition-total estimate already suffice.
See `docs/paper-gaps/truncation-combinatorics-f-nonneg.tex`. -/
lemma sum_small_le_four_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α)
    {f : α → ℝ}
    {d : ℕ} {ζ : ℝ}
    (hL_card : L.card = d)
    (hcard_gt : d < Fintype.card α)
    (hr_bound : (Fintype.card α : ℝ) ≤ (1 + 2 * Real.sqrt ζ) * d)
    (hf_ordering : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l)
    (htotal : (∑ x, f x) ≤ 1 + 2 * Real.sqrt ζ)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / 4) :
    (∑ s ∈ (Lᶜ : Finset α), f s) ≤ 4 * Real.sqrt ζ := by
  classical
  have hr_pos : 0 < Fintype.card α := lt_of_le_of_lt (Nat.zero_le _) hcard_gt
  have hsqrt_nonneg : 0 ≤ Real.sqrt ζ := Real.sqrt_nonneg _
  have hsqrt_le_half : Real.sqrt ζ ≤ 1 / 2 := by
    have h1 : Real.sqrt ζ ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hζ_le
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hLc_card_nat : L.card + Lᶜ.card = Fintype.card α := Finset.card_add_card_compl L
  have hLc_card : (Lᶜ.card : ℝ) = (Fintype.card α : ℝ) - d := by
    have h1 : (L.card : ℝ) + (Lᶜ.card : ℝ) = (Fintype.card α : ℝ) := by
      exact_mod_cast hLc_card_nat
    have hL : (L.card : ℝ) = (d : ℝ) := by exact_mod_cast hL_card
    linarith
  have hLc_nonneg : (0 : ℝ) ≤ (Lᶜ.card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hpart := card_univ_mul_sum_compl_le (α := α) L hf_ordering
  have hr_real_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hr_pos
  have htotal_nonneg : 0 ≤ 1 + 2 * Real.sqrt ζ := by positivity
  have hSsum_le_frac : ∑ s ∈ (Lᶜ : Finset α), f s ≤
      (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) := by
    have hrhs :
        (Lᶜ.card : ℝ) * (∑ x, f x) ≤
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) :=
      mul_le_mul_of_nonneg_left htotal hLc_nonneg
    have hcomb :
        (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) := le_trans hpart hrhs
    have hgoal_rewrite :
        (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) =
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) / (Fintype.card α : ℝ) := by ring
    rw [hgoal_rewrite, le_div_iff₀ hr_real_pos]
    nlinarith [hcomb]
  have hd_le_r : (d : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast (le_of_lt hcard_gt)
  have hLc_le : (Lᶜ.card : ℝ) ≤ 2 * Real.sqrt ζ * (Fintype.card α : ℝ) := by
    have h1 : (Fintype.card α : ℝ) - d ≤ 2 * Real.sqrt ζ * d := by
      nlinarith [hr_bound, hsqrt_nonneg]
    have h2 : 2 * Real.sqrt ζ * (d : ℝ) ≤ 2 * Real.sqrt ζ * (Fintype.card α : ℝ) := by
      nlinarith [hd_le_r, hsqrt_nonneg]
    linarith [hLc_card]
  have hratio : (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) ≤ 2 * Real.sqrt ζ := by
    rw [div_le_iff₀ hr_real_pos]
    linarith
  have hbound_final :
      (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) ≤
        2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) :=
    mul_le_mul_of_nonneg_right hratio htotal_nonneg
  have hSsum_le_mix : ∑ s ∈ (Lᶜ : Finset α), f s ≤
      2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) := le_trans hSsum_le_frac hbound_final
  have hsq_sqrt : Real.sqrt ζ * Real.sqrt ζ = ζ := Real.mul_self_sqrt hζ_nonneg
  have h_4zeta_le_sqrt : 4 * ζ ≤ 2 * Real.sqrt ζ := by
    have h1 : 2 * (Real.sqrt ζ * Real.sqrt ζ) ≤ Real.sqrt ζ := by
      nlinarith [hsqrt_le_half, hsqrt_nonneg]
    calc 4 * ζ = 4 * (Real.sqrt ζ * Real.sqrt ζ) := by rw [hsq_sqrt]
      _ = 2 * (2 * (Real.sqrt ζ * Real.sqrt ζ)) := by ring
      _ ≤ 2 * Real.sqrt ζ := by linarith
  have h_rhs_expand :
      2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) = 2 * Real.sqrt ζ + 4 * ζ := by
    have hstep : 2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) =
        2 * Real.sqrt ζ + 4 * (Real.sqrt ζ * Real.sqrt ζ) := by ring
    rw [hstep, hsq_sqrt]
  have hfinal : 2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) ≤ 4 * Real.sqrt ζ := by
    rw [h_rhs_expand]; linarith
  exact le_trans hSsum_le_mix hfinal

end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
