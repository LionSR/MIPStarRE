import MIPStarRE.LDT.SelfImprovement.Simplified.SimultaneousDilation

/-!
# Compression after simultaneous dilation

Taking the distinguished auxiliary matrix block maps positive effects
to positive effects and preserves their sum. A measurement on the
enlarged register therefore compresses to a measurement on the
original register.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:simultaneous-dilation-compression`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v w

/-- Compression to the distinguished auxiliary basis vector. -/
def compressAtNone {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (X : MIPStarRE.Quantum.Op (ι × Option Outcome)) :
    MIPStarRE.Quantum.Op ι :=
  X.submatrix (fun i => (i, none)) (fun i => (i, none))

/-- Distinguished-block compression preserves positivity. -/
theorem compressAtNone_nonneg {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (X : MIPStarRE.Quantum.Op (ι × Option Outcome))
    (hX : 0 ≤ X) : 0 ≤ compressAtNone X := by
  exact Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hX).submatrix (fun i : ι => (i, none)))

/-- Compression maps the identity on the enlarged register to the
identity on the original register. -/
@[simp] theorem compressAtNone_one {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome] :
    compressAtNone (1 : MIPStarRE.Quantum.Op (ι × Option Outcome)) = 1 := by
  ext i j
  simp [compressAtNone, Matrix.one_apply]

/-- Compression is additive. -/
theorem compressAtNone_add {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (X Y : MIPStarRE.Quantum.Op (ι × Option Outcome)) :
    compressAtNone (X + Y) = compressAtNone X + compressAtNone Y := by
  ext i j
  rfl

/-- Compression commutes with finite operator sums. -/
theorem compressAtNone_sum {α : Type w} {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (s : Finset α) (X : α → MIPStarRE.Quantum.Op (ι × Option Outcome)) :
    compressAtNone (∑ a ∈ s, X a) = ∑ a ∈ s, compressAtNone (X a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [compressAtNone]
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, compressAtNone_add, ih]

/-- Compression is monotone for the positive-operator order. -/
theorem compressAtNone_mono {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (X Y : MIPStarRE.Quantum.Op (ι × Option Outcome))
    (hXY : X ≤ Y) : compressAtNone X ≤ compressAtNone Y := by
  have h : 0 ≤ compressAtNone (Y - X) :=
    compressAtNone_nonneg (Y - X) (sub_nonneg.mpr hXY)
  have heq : compressAtNone (Y - X) = compressAtNone Y - compressAtNone X := by
    ext i j
    rfl
  exact sub_nonneg.mp (heq ▸ h)

/-- A measurement on the enlarged register compresses to a
measurement on the original register. -/
noncomputable def compressMeasurementAtNone
    {α : Type w} {ι : Type u} {Outcome : Type v}
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (T : Measurement α (ι × Option Outcome)) : Measurement α ι where
  toSubMeas := {
    outcome := fun a => compressAtNone (T.outcome a)
    total := 1
    outcome_pos := fun a => compressAtNone_nonneg _ (T.outcome_pos a)
    sum_eq_total := by
      calc
        (∑ a, compressAtNone (T.outcome a)) =
            compressAtNone (∑ a, T.outcome a) := by
          simpa using (compressAtNone_sum (Finset.univ) T.outcome).symm
        _ = 1 := by rw [T.sum_eq_total, T.total_eq_one, compressAtNone_one]
    total_le_one := le_rfl }
  total_eq_one := rfl

/-- Compression preserves a correlation with an original operator
extended by the identity on the auxiliary register. -/
theorem original_left_compressed_correlation
    {ι : Type u} {Outcome : Type v}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (R : MIPStarRE.Quantum.Op ι)
    (T : MIPStarRE.Quantum.Op (ι × Option Outcome)) :
    ev ψ (opTensor R (compressAtNone T)) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome))) T) := by
  let HA : MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.{u} :=
    simultaneousDilationBaseSpace ι
  have hR : ∀ i j : ι,
      (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome)))
        (i, none) (j, none) = R i j := by
    intro i j
    simp [opTensor]
  have hT : ∀ i j : ι, T (i, none) (j, none) = compressAtNone T i j := by
    intro i j
    rfl
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ R (compressAtNone T)
    (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome))) T hR hT
  convert h using 1 <;>
    simp [simultaneousDilationState, HA] <;> rfl

end MIPStarRE.LDT.SelfImprovement
