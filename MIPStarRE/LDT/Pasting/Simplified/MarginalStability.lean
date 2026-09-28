import MIPStarRE.LDT.Pasting.Simplified.EffectCenter
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-!
# Marginal stability for random measurement words

The centered-effect estimate and weighted Cauchy--Schwarz control the change
in an effect's expectation when an operator family is perturbed. This is the
analytic part of the simplified pasting argument's marginal-stability lemma.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:sequential-bot-marginal`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted Cauchy--Schwarz for one centered-effect cross term. -/
theorem averaged_centered_effect_cross_abs_le
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (D : Distribution Question)
    (M : MIPStarRE.Quantum.Op ι)
    (hM : 0 ≤ M) (hMle : M ≤ 1)
    (A B : Question → Outcome → MIPStarRE.Quantum.Op ι) :
    |avgOver D (fun q => ∑ a : Outcome,
        ev ψ ((A q a)ᴴ * (M - (1 / 2 : ℝ) • 1) * B q a))| ≤
      (1 / 2 : ℝ) *
        Real.sqrt (avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((A q a)ᴴ * A q a))) *
        Real.sqrt (avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((B q a)ᴴ * B q a))) := by
  let t : Question → Outcome → Error := fun q a =>
    ev ψ ((A q a)ᴴ * (M - (1 / 2 : ℝ) • 1) * B q a)
  let x : Question → Outcome → Error := fun q a => ev ψ ((A q a)ᴴ * A q a)
  let y : Question → Outcome → Error := fun q a => ev ψ ((B q a)ᴴ * B q a)
  have hx : ∀ q a, 0 ≤ x q a := fun q a => ev_adjoint_self_nonneg ψ (A q a)
  have hy : ∀ q a, 0 ≤ y q a := fun q a => ev_adjoint_self_nonneg ψ (B q a)
  have hroot (r : Error) (hr : 0 ≤ r) :
      Real.sqrt ((1 / 4 : Error) * r) = (1 / 2 : Error) * Real.sqrt r := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 1 / 4)]
    norm_num
  have hterm (q : Question) (a : Outcome) :
      |t q a| ≤ Real.sqrt ((1 / 4 : Error) * x q a) * Real.sqrt (y q a) := by
    rw [hroot (x q a) (hx q a)]
    simpa [t, x, y, mul_assoc] using
      ev_centered_effect_cross_abs_le ψ M (A q a) (B q a) hM hMle
  have hcs := Preliminaries.weightedFinsetCauchySchwarz D t
    (fun q a => (1 / 4 : Error) * x q a) y hterm
    (fun q a => mul_nonneg (by norm_num) (hx q a)) hy
  have hscale :
      avgOver D (fun q => ∑ a : Outcome, (1 / 4 : Error) * x q a) =
        (1 / 4 : Error) * avgOver D (fun q => ∑ a : Outcome, x q a) := by
    simp [avgOver, Finset.mul_sum, mul_assoc, mul_comm]
  rw [hscale] at hcs
  have hmass : 0 ≤ avgOver D (fun q => ∑ a : Outcome, x q a) := by
    apply avgOver_nonneg
    intro q
    exact Finset.sum_nonneg fun a _ => hx q a
  rw [hroot _ hmass] at hcs
  simpa [t, x, y, mul_assoc] using hcs

/-- Averaged expectation of an effect inside an operator family. -/
noncomputable def averagedSandwichMass
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (D : Distribution Question)
    (M : MIPStarRE.Quantum.Op ι)
    (A : Question → Outcome → MIPStarRE.Quantum.Op ι) : Error :=
  avgOver D (fun q => ∑ a : Outcome, ev ψ ((A q a)ᴴ * M * A q a))

/-- Averaged squared operator norm in a state. -/
noncomputable def averagedOperatorNormSq
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (D : Distribution Question)
    (A : Question → Outcome → MIPStarRE.Quantum.Op ι) : Error :=
  avgOver D (fun q => ∑ a : Outcome, ev ψ ((A q a)ᴴ * A q a))

/-- Centering an effect separates its sandwich expectation from half the
family's normalization mass. -/
theorem averagedSandwichMass_center
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (D : Distribution Question)
    (M : MIPStarRE.Quantum.Op ι)
    (A : Question → Outcome → MIPStarRE.Quantum.Op ι) :
    averagedSandwichMass ψ D M A =
      averagedSandwichMass ψ D (M - (1 / 2 : ℝ) • 1) A +
        (1 / 2 : ℝ) * averagedOperatorNormSq ψ D A := by
  let C : MIPStarRE.Quantum.Op ι := M - (1 / 2 : ℝ) • 1
  have hM : M = C + (1 / 2 : ℝ) • 1 := by dsimp [C]; abel
  have hpoint (q : Question) (a : Outcome) :
      ev ψ ((A q a)ᴴ * M * A q a) =
        ev ψ ((A q a)ᴴ * C * A q a) +
          (1 / 2 : ℝ) * ev ψ ((A q a)ᴴ * A q a) := by
    rw [hM]
    simp only [mul_add, add_mul, ev_add]
    have hsmul :
        (A q a)ᴴ * ((1 / 2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι)) * A q a =
          (1 / 2 : ℝ) • ((A q a)ᴴ * A q a) := by
      simp
    rw [hsmul, ev_real_smul]
  unfold averagedSandwichMass averagedOperatorNormSq
  calc
    avgOver D (fun q => ∑ a : Outcome, ev ψ ((A q a)ᴴ * M * A q a)) =
        avgOver D (fun q => ∑ a : Outcome,
          (ev ψ ((A q a)ᴴ * C * A q a) +
            (1 / 2 : ℝ) * ev ψ ((A q a)ᴴ * A q a))) := by
          apply avgOver_congr
          intro q
          exact Finset.sum_congr rfl fun a _ => hpoint q a
    _ = avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((A q a)ᴴ * C * A q a)) +
        (1 / 2 : ℝ) * avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((A q a)ᴴ * A q a)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, avgOver_add,
            avgOver_const_mul]


/-- Two normalized operator families have effect expectations at distance at
most the square root of their state-dependent squared distance. -/
theorem averagedSandwichMass_gap_le_sqrt
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (D : Distribution Question)
    (M : MIPStarRE.Quantum.Op ι) (hM : 0 ≤ M) (hMle : M ≤ 1)
    (A B : Question → Outcome → MIPStarRE.Quantum.Op ι)
    (hA : averagedOperatorNormSq ψ D A = 1)
    (hB : averagedOperatorNormSq ψ D B = 1) :
    |averagedSandwichMass ψ D M A - averagedSandwichMass ψ D M B| ≤
      Real.sqrt (averagedOperatorNormSq ψ D (fun q a => A q a - B q a)) := by
  let Δ : Question → Outcome → MIPStarRE.Quantum.Op ι :=
    fun q a => A q a - B q a
  let C : MIPStarRE.Quantum.Op ι := M - (1 / 2 : ℝ) • 1
  let t₁ : Question → Outcome → Error := fun q a =>
    ev ψ ((Δ q a)ᴴ * C * A q a)
  let t₂ : Question → Outcome → Error := fun q a =>
    ev ψ ((B q a)ᴴ * C * Δ q a)
  have hcenter :
      averagedSandwichMass ψ D M A - averagedSandwichMass ψ D M B =
        averagedSandwichMass ψ D C A - averagedSandwichMass ψ D C B := by
    rw [averagedSandwichMass_center ψ D M A,
      averagedSandwichMass_center ψ D M B, hA, hB]
    ring
  have hpoint (q : Question) (a : Outcome) :
      ev ψ ((A q a)ᴴ * C * A q a) -
        ev ψ ((B q a)ᴴ * C * B q a) = t₁ q a + t₂ q a := by
    have hop :
        (A q a)ᴴ * C * A q a - (B q a)ᴴ * C * B q a =
          (Δ q a)ᴴ * C * A q a + (B q a)ᴴ * C * Δ q a := by
      dsimp [Δ]
      rw [Matrix.conjTranspose_sub]
      noncomm_ring
    rw [← ev_sub, hop, ev_add]
  have hsplit :
      averagedSandwichMass ψ D C A - averagedSandwichMass ψ D C B =
        avgOver D (fun q => ∑ a : Outcome, t₁ q a) +
          avgOver D (fun q => ∑ a : Outcome, t₂ q a) := by
    unfold averagedSandwichMass
    rw [← avgOver_sub]
    simp only [← Finset.sum_sub_distrib]
    apply Eq.trans (avgOver_congr D _ _ (fun q =>
      Finset.sum_congr rfl (fun a _ => hpoint q a)))
    simp only [Finset.sum_add_distrib, avgOver_add]
  have hcross₁ :
      |avgOver D (fun q => ∑ a : Outcome, t₁ q a)| ≤
        (1 / 2 : ℝ) * Real.sqrt (averagedOperatorNormSq ψ D Δ) := by
    have h := averaged_centered_effect_cross_abs_le ψ D M hM hMle Δ A
    have hA' :
        avgOver D (fun q => ∑ a : Outcome, ev ψ ((A q a)ᴴ * A q a)) = 1 := hA
    rw [hA'] at h
    simpa only [t₁, C, averagedOperatorNormSq, Real.sqrt_one, mul_one] using h
  have hcross₂ :
      |avgOver D (fun q => ∑ a : Outcome, t₂ q a)| ≤
        (1 / 2 : ℝ) * Real.sqrt (averagedOperatorNormSq ψ D Δ) := by
    have h := averaged_centered_effect_cross_abs_le ψ D M hM hMle B Δ
    have hB' :
        avgOver D (fun q => ∑ a : Outcome, ev ψ ((B q a)ᴴ * B q a)) = 1 := hB
    rw [hB'] at h
    simpa only [t₂, C, averagedOperatorNormSq, Real.sqrt_one, mul_one,
      one_mul] using h
  rw [hcenter, hsplit]
  calc
    |avgOver D (fun q => ∑ a : Outcome, t₁ q a) +
        avgOver D (fun q => ∑ a : Outcome, t₂ q a)| ≤
      |avgOver D (fun q => ∑ a : Outcome, t₁ q a)| +
        |avgOver D (fun q => ∑ a : Outcome, t₂ q a)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * Real.sqrt (averagedOperatorNormSq ψ D Δ) +
        (1 / 2 : ℝ) * Real.sqrt (averagedOperatorNormSq ψ D Δ) :=
          add_le_add hcross₁ hcross₂
    _ = Real.sqrt (averagedOperatorNormSq ψ D Δ) := by ring

end MIPStarRE.LDT.Pasting
