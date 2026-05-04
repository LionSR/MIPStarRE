import Mathlib.Data.Nat.Choose.Sum
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Bernoulli.Weights
import MIPStarRE.LDT.Pasting.Bernoulli.Scalar
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

/-!
# Section 12 pasting: Bernoulli tail polynomial combinatorics

Finset re-indexing and cardinality-grouping lemmas for the Bernoulli-tail
operator endpoint of the `fromHToG` recurrence.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Boolean type patterns are equivalent to their support finsets. -/
noncomputable def gHatTypeFinsetEquiv (k : ℕ) :
    GHatType k ≃ Finset (Fin k) where
  toFun τ := Finset.univ.filter fun i => τ i
  invFun s := fun i => i ∈ s
  left_inv τ := by
    ext i
    simp
  right_inv s := by
    ext i
    simp

lemma fromHToG_gHatTypeWeight_of_finset {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeWeight (fun i : Fin k => i ∈ s) = s.card := by
  simp [gHatTypeWeight]

lemma fromHToG_gHatTypeOperator_of_finset
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeOperator G (fun i : Fin k => i ∈ s) =
      G ^ s.card * (1 - G) ^ (k - s.card) := by
  simp [gHatTypeOperator, fromHToG_gHatTypeWeight_of_finset]

/-- Rewrite the terminal truncated type sum as a sum over support finsets. -/
lemma fromHToG_truncatedTypeSums_full_as_finset_sum
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) =
      ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
  unfold truncatedTypeSums
  calc
    (∑ τprefix : GHatType k,
      if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight (default : GHatType 0) then
        gHatTypeOperator G τprefix
      else 0)
      = ∑ s : Finset (Fin k),
          if d + 1 ≤ gHatTypeWeight ((gHatTypeFinsetEquiv k).symm s) +
              gHatTypeWeight (default : GHatType 0) then
            gHatTypeOperator G ((gHatTypeFinsetEquiv k).symm s)
          else 0 := by
          exact Fintype.sum_equiv (gHatTypeFinsetEquiv k)
            (fun τ => if d + 1 ≤ gHatTypeWeight τ +
                gHatTypeWeight (default : GHatType 0) then
              gHatTypeOperator G τ
            else 0)
            (fun s => if d + 1 ≤ gHatTypeWeight ((gHatTypeFinsetEquiv k).symm s) +
                gHatTypeWeight (default : GHatType 0) then
              gHatTypeOperator G ((gHatTypeFinsetEquiv k).symm s)
            else 0)
            (by intro τ; simp)
    _ = ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro s _
        simp [gHatTypeFinsetEquiv, fromHToG_gHatTypeOperator_of_finset, gHatTypeWeight]

/-- Group the terminal support-finset sum by cardinality, producing the binomial
coefficients in the Bernoulli-tail polynomial.  The key combinatorial step is
Mathlib's `Finset.sum_powerset_apply_card`, applied to `Finset.univ : Finset (Fin k)`. -/
lemma fromHToG_sum_finsets_by_card_indicator
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0) =
      ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
  classical
  let F : ℕ → MIPStarRE.Quantum.Op ι := fun r =>
    if d + 1 ≤ r then G ^ r * (1 - G) ^ (k - r) else 0
  have hpow := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin k))) F
  have hleft :
      (∑ s : Finset (Fin k), F s.card) =
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := by
    rw [Finset.powerset_univ]
  calc
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0)
      = ∑ s : Finset (Fin k), F s.card := by rfl
    _ = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := hleft
    _ = ∑ r ∈ Finset.range ((Finset.univ : Finset (Fin k)).card + 1),
          (Finset.univ : Finset (Fin k)).card.choose r • F r := hpow
    _ = ∑ r ∈ Finset.range (k + 1), Nat.choose k r • F r := by simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k, Nat.choose k r • F r := by
      symm
      refine Finset.sum_subset ?hsubset ?hzero
      · intro r hr
        simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
        exact Nat.lt_succ_of_le hr.2
      · intro r hrange hrnot
        simp only [Finset.mem_range, Finset.mem_Icc] at hrange hrnot
        have hnot : ¬ d + 1 ≤ r := by
          intro hdr
          exact hrnot ⟨hdr, Nat.le_of_lt_succ hrange⟩
        dsimp [F]
        rw [if_neg hnot]
        simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hdr : d + 1 ≤ r := hr.1
      dsimp [F]
      rw [if_pos hdr]
      simp [Algebra.smul_def]

/-- Terminal endpoint of the recurrence weight: after all `k` bits have been
converted, the truncated type sum is exactly the Bernoulli-tail polynomial
`F(G)`. -/
lemma fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) =
      bernoulliTailOperator k d G := by
  calc
    truncatedTypeSums G d k (default : GHatType 0)
      = ∑ s : Finset (Fin k),
          if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 :=
          fromHToG_truncatedTypeSums_full_as_finset_sum G d k
    _ = bernoulliTailOperator k d G := by
          rw [fromHToG_sum_finsets_by_card_indicator]
          rfl

/-- At prefix length zero, the recurrence weight is exactly the eligibility
indicator for the remaining type: the empty prefix contributes the identity when
`|τtail| ≥ d + 1`, and contributes zero otherwise. -/
lemma fromHToG_truncatedTypeSums_zero_eq_indicator
    (G : MIPStarRE.Quantum.Op ι) (d : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

end MIPStarRE.LDT.Pasting
