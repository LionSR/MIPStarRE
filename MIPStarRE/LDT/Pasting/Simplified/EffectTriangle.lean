import MIPStarRE.LDT.Pasting.Simplified.RandomWordAdjointCommutation

/-!
# Quadratic triangle inequality with a right-hand effect

The simplified consistency argument compares the probability of a
selected-slice mismatch before and after moving the slice operator through
a completed-measurement word. The comparison keeps the square of the
commutator energy.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The operator form of the quadratic triangle inequality. -/
theorem mul_conjTranspose_add_le_two
    {ι : Type*} [Fintype ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    (X + Y) * (X + Y)ᴴ ≤
      (X * Xᴴ + Y * Yᴴ) + (X * Xᴴ + Y * Yᴴ) := by
  have hpos : 0 ≤ (X - Y) * (X - Y)ᴴ :=
    (Matrix.posSemidef_self_mul_conjTranspose (X - Y)).nonneg
  have hle : (X + Y) * (X + Y)ᴴ ≤
      (X + Y) * (X + Y)ᴴ + (X - Y) * (X - Y)ᴴ :=
    le_add_of_nonneg_right hpos
  convert hle using 1
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
  noncomm_ring

/-- A positive right-hand effect preserves the quadratic comparison. -/
theorem ev_opTensor_mul_conjTranspose_add_le_weighted
    {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (X Y : MIPStarRE.Quantum.Op ι₁)
    (C : MIPStarRE.Quantum.Op ι₂)
    (hCpos : 0 ≤ C) :
    ev ψ (opTensor ((X + Y) * (X + Y)ᴴ) C) ≤
      2 * ev ψ (opTensor (X * Xᴴ) C) +
        2 * ev ψ (opTensor (Y * Yᴴ) C) := by
  have htri := ev_mono ψ _ _
    (opTensor_mono_left (mul_conjTranspose_add_le_two X Y) hCpos)
  have hrewrite :
      ev ψ (opTensor
        ((X * Xᴴ + Y * Yᴴ) + (X * Xᴴ + Y * Yᴴ)) C) =
      2 * ev ψ (opTensor (X * Xᴴ) C) +
        2 * ev ψ (opTensor (Y * Yᴴ) C) := by
    rw [opTensor_add_left_local, opTensor_add_left_local,
      ev_add, ev_add]
    ring
  rwa [hrewrite] at htri

/-- A mismatch effect admits the same quadratic comparison. The error
term is bounded by its unweighted commutator energy. -/
theorem ev_opTensor_mul_conjTranspose_add_le
    {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (X Y : MIPStarRE.Quantum.Op ι₁)
    (C : MIPStarRE.Quantum.Op ι₂)
    (hCpos : 0 ≤ C) (hCle : C ≤ 1) :
    ev ψ (opTensor ((X + Y) * (X + Y)ᴴ) C) ≤
      2 * ev ψ (opTensor (X * Xᴴ) C) +
        2 * ev ψ (leftTensor (ι₂ := ι₂) (Y * Yᴴ)) := by
  have hYpos : 0 ≤ Y * Yᴴ :=
    (Matrix.posSemidef_self_mul_conjTranspose Y).nonneg
  have hY := ev_mono ψ _ _ (opTensor_le_leftTensor hYpos hCle)
  have htri := ev_opTensor_mul_conjTranspose_add_le_weighted
    ψ X Y C hCpos
  linarith

/-- Weighted direct-sum quadratic comparison. -/
theorem averaged_effect_triangle_le_weighted
    {Question Outcome ι₁ ι₂ : Type*}
    [Fintype Outcome]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂)) (D : Distribution Question)
    (X Y : Question → Outcome → MIPStarRE.Quantum.Op ι₁)
    (C : Question → Outcome → MIPStarRE.Quantum.Op ι₂)
    (hCpos : ∀ q a, 0 ≤ C q a) :
    avgOver D (fun q => ∑ a : Outcome,
      ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      2 * avgOver D (fun q => ∑ a : Outcome,
        ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
      2 * avgOver D (fun q => ∑ a : Outcome,
        ev ψ (opTensor (Y q a * (Y q a)ᴴ) (C q a))) := by
  have hpoint (q : Question) :
      (∑ a : Outcome,
        ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      2 * (∑ a : Outcome,
        ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
      2 * (∑ a : Outcome,
        ev ψ (opTensor (Y q a * (Y q a)ᴴ) (C q a))) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      ev_opTensor_mul_conjTranspose_add_le_weighted
        ψ (X q a) (Y q a) (C q a) (hCpos q a))
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  calc
    avgOver D (fun q => ∑ a : Outcome,
        ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      avgOver D (fun q =>
        2 * (∑ a : Outcome,
          ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
        2 * (∑ a : Outcome,
          ev ψ (opTensor (Y q a * (Y q a)ᴴ) (C q a)))) :=
        avgOver_mono D _ _ hpoint
    _ = 2 * avgOver D (fun q => ∑ a : Outcome,
          ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
        2 * avgOver D (fun q => ∑ a : Outcome,
          ev ψ (opTensor (Y q a * (Y q a)ᴴ) (C q a))) := by
      rw [avgOver_add, avgOver_const_mul, avgOver_const_mul]

/-- The quadratic effect comparison survives sums over outcomes and
averages over questions. This is the analytic step behind the per-position
bound in the simplified interpolation argument. -/
theorem averaged_effect_triangle_le
    {Question Outcome ι₁ ι₂ : Type*}
    [Fintype Outcome]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂)) (D : Distribution Question)
    (X Y : Question → Outcome → MIPStarRE.Quantum.Op ι₁)
    (C : Question → Outcome → MIPStarRE.Quantum.Op ι₂)
    (hCpos : ∀ q a, 0 ≤ C q a) (hCle : ∀ q a, C q a ≤ 1) :
    avgOver D (fun q => ∑ a : Outcome,
      ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      2 * avgOver D (fun q => ∑ a : Outcome,
        ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
      2 * avgOver D (fun q => ∑ a : Outcome,
        ev ψ (leftTensor (ι₂ := ι₂) (Y q a * (Y q a)ᴴ))) := by
  have hpoint (q : Question) :
      (∑ a : Outcome,
        ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      2 * (∑ a : Outcome,
        ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
      2 * (∑ a : Outcome,
        ev ψ (leftTensor (ι₂ := ι₂) (Y q a * (Y q a)ᴴ))) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      ev_opTensor_mul_conjTranspose_add_le ψ (X q a) (Y q a) (C q a)
        (hCpos q a) (hCle q a))
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  calc
    avgOver D (fun q => ∑ a : Outcome,
        ev ψ (opTensor ((X q a + Y q a) * (X q a + Y q a)ᴴ) (C q a))) ≤
      avgOver D (fun q =>
        2 * (∑ a : Outcome,
          ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
        2 * (∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ι₂) (Y q a * (Y q a)ᴴ)))) :=
        avgOver_mono D _ _ hpoint
    _ = 2 * avgOver D (fun q => ∑ a : Outcome,
          ev ψ (opTensor (X q a * (X q a)ᴴ) (C q a))) +
        2 * avgOver D (fun q => ∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ι₂) (Y q a * (Y q a)ᴴ))) := by
      rw [avgOver_add, avgOver_const_mul, avgOver_const_mul]

end MIPStarRE.LDT.Pasting
