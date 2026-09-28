import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SpectralMass

/-!
# Projectors selected from outcome spectral bases

For each outcome, the global spectral selection chooses some eigenvectors of
that outcome effect.  Conjugating the corresponding diagonal coordinate
projector by the eigenvector unitary gives the local projector `Qₐ` in the
simplified orthogonalization proof.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, equation
  `eq:global-rank-allocation`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The coordinate projector onto those eigenvectors of outcome `a` selected
by the global set `L`. -/
noncomputable def selectedDiagonal {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (a : Outcome) : MIPStarRE.Quantum.Op ι :=
  Matrix.diagonal (fun j => if (a, j) ∈ L then 1 else 0)

/-- Indices selected in the spectral basis of outcome `a`. -/
def selectedFiber {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (a : Outcome) : Finset ι :=
  Finset.univ.filter (fun j => (a, j) ∈ L)

/-- The spectral projector `Qₐ` onto selected eigenvectors of `Mₐ`. -/
noncomputable def selectedProjector {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι)
    hM.eigenvectorUnitary (selectedDiagonal L a)

/-- A selected coordinate projector is idempotent. -/
theorem selectedDiagonal_idempotent {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (a : Outcome) :
    selectedDiagonal L a * selectedDiagonal L a = selectedDiagonal L a := by
  classical
  unfold selectedDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases h : (a, j) ∈ L <;> simp [h]

/-- A selected coordinate projector is self-adjoint. -/
theorem selectedDiagonal_selfAdjoint {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (a : Outcome) :
    (selectedDiagonal L a)ᴴ = selectedDiagonal L a := by
  classical
  unfold selectedDiagonal
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : (a, j) ∈ L <;> simp [h]

/-- Each `Qₐ` is an orthogonal projection. -/
theorem selectedProjector_isProj {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    MIPStarRE.Quantum.IsProj (selectedProjector M L a) := by
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  let Φ := Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι) hM.eigenvectorUnitary
  change IsStarProjection (Φ (selectedDiagonal L a))
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change Φ (selectedDiagonal L a) * Φ (selectedDiagonal L a) =
      Φ (selectedDiagonal L a)
    rw [← map_mul, selectedDiagonal_idempotent]
  · change star (Φ (selectedDiagonal L a)) = Φ (selectedDiagonal L a)
    rw [← map_star, show star (selectedDiagonal L a) = selectedDiagonal L a from
      selectedDiagonal_selfAdjoint L a]

/-- The selected projector `Qₐ` commutes with its source effect `Mₐ`, since
both are diagonal in the same eigenbasis. -/
theorem selectedProjector_commutes {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    selectedProjector M L a * M.outcome a =
      M.outcome a * selectedProjector M L a := by
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  let Φ := Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι) hM.eigenvectorUnitary
  let D := selectedDiagonal L a
  let E : MIPStarRE.Quantum.Op ι :=
    Matrix.diagonal (fun j => (measurementEigenvalue M a j : ℂ))
  have hM_spec : M.outcome a = Φ E := hM.spectral_theorem
  have hDE : D * E = E * D := by
    simp [D, E, selectedDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]
  change Φ D * M.outcome a = M.outcome a * Φ D
  rw [hM_spec, ← map_mul, ← map_mul, hDE]

/-- The selected effect `QₐMₐ` is positive and bounded by its source effect. -/
theorem selectedProjector_mul_effect_nonneg_le {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    0 ≤ selectedProjector M L a * M.outcome a ∧
      selectedProjector M L a * M.outcome a ≤ M.outcome a := by
  let Q := selectedProjector M L a
  have hQ : MIPStarRE.Quantum.IsProj Q := selectedProjector_isProj M L a
  have hM : 0 ≤ M.outcome a := M.outcome_pos a
  have hcomm : Commute Q (M.outcome a) := selectedProjector_commutes M L a
  constructor
  · exact Commute.mul_nonneg hQ.nonneg hM hcomm
  · have hcomm' : Commute (1 - Q) (M.outcome a) :=
      (Commute.one_left (M.outcome a)).sub_left hcomm
    have hpos : 0 ≤ (1 - Q) * M.outcome a :=
      Commute.mul_nonneg hQ.one_sub_nonneg hM hcomm'
    exact sub_nonneg.mp (by simpa [sub_mul] using hpos)

/-- The sum of selected effects is a positive contraction. -/
theorem selectedEffectSum_nonneg_le_one {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) :
    0 ≤ ∑ a, selectedProjector M L a * M.outcome a ∧
      (∑ a, selectedProjector M L a * M.outcome a) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => (selectedProjector_mul_effect_nonneg_le M L a).1)
  · calc
      (∑ a, selectedProjector M L a * M.outcome a) ≤
          ∑ a, M.outcome a :=
        Finset.sum_le_sum (fun a _ => (selectedProjector_mul_effect_nonneg_le M L a).2)
      _ = 1 := by rw [M.sum_eq_total, M.total_eq_one]

/-- The rank of `Qₐ` is the number of eigenvectors selected for outcome `a`. -/
theorem selectedProjector_rank {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    (selectedProjector M L a).rank = (selectedFiber L a).card := by
  classical
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  change (Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι)
    hM.eigenvectorUnitary (selectedDiagonal L a)).rank = (selectedFiber L a).card
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
  simp [selectedDiagonal, selectedFiber, Matrix.rank_diagonal, Fintype.card_subtype,
    -isUnit_iff_ne_zero, -Unitary.coe_star]

/-- The selected projectors have total rank equal to the size of the global
selection.  When `L` is supplied by rank allocation, this is `dim H`. -/
theorem sum_selectedProjector_rank_eq_card {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) :
    (∑ a : Outcome, (selectedProjector M L a).rank) = L.card := by
  classical
  have hfiber (a : Outcome) :
      (selectedFiber L a).card =
        ∑ j : ι, if (a, j) ∈ L then 1 else 0 := by
    simp [selectedFiber]
  calc
    (∑ a : Outcome, (selectedProjector M L a).rank) =
        ∑ a : Outcome, (selectedFiber L a).card := by
          apply Finset.sum_congr rfl
          intro a _
          exact selectedProjector_rank M L a
    _ = ∑ a : Outcome, ∑ j : ι, if (a, j) ∈ L then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          exact hfiber a
    _ = ∑ p : Outcome × ι, if p ∈ L then 1 else 0 := by
          rw [Fintype.sum_prod_type]
    _ = L.card := by simp

/-- Conjugating a diagonal matrix in the eigenbasis of `Mₐ` gives the
corresponding weighted sum of rank-one eigenprojectors.  The coefficients
may depend on the eigenvector index, as they do for the global selection. -/
theorem measurement_conj_diagonal_eq_sum_eigenprojectors {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (c : ι → ℂ) :
    Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι)
        (show (M.outcome a).IsHermitian from M.outcome_hermitian a).eigenvectorUnitary
        (Matrix.diagonal c) =
      ∑ j : ι, c j • measurementEigenProjector M a j := by
  classical
  ext r s
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.sum_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp [measurementEigenProjector, Matrix.smul_apply, Matrix.vecMulVec_apply]
  ring

/-- The selected part of an effect is the sum of its chosen spectral weights. -/
theorem selectedProjector_mul_effect_eq_sum {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) (a : Outcome) :
    selectedProjector M L a * M.outcome a =
      ∑ j : ι, (if (a, j) ∈ L then (measurementEigenvalue M a j : ℂ) else 0) •
        measurementEigenProjector M a j := by
  classical
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  let Φ := Unitary.conjStarAlgAut ℂ (MIPStarRE.Quantum.Op ι) hM.eigenvectorUnitary
  let D := selectedDiagonal L a
  let E : MIPStarRE.Quantum.Op ι :=
    Matrix.diagonal (fun j => (measurementEigenvalue M a j : ℂ))
  have hDE : D * E =
      Matrix.diagonal
        (fun j => if (a, j) ∈ L then (measurementEigenvalue M a j : ℂ) else 0) := by
    simp [D, E, selectedDiagonal, Matrix.diagonal_mul_diagonal, ite_mul]
  change Φ D * M.outcome a = _
  have hM_spec : M.outcome a = Φ E := hM.spectral_theorem
  rw [hM_spec, ← map_mul, hDE]
  exact measurement_conj_diagonal_eq_sum_eigenprojectors M a _

/-- State expectation of the selected effect equals its selected spectral
mass. -/
theorem ev_selectedProjector_mul_effect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι)
    (L : Finset (Outcome × ι)) (a : Outcome) :
    ev ψ (selectedProjector M L a * M.outcome a) =
      ∑ j : ι, if (a, j) ∈ L then
        measurementEigenvalue M a j * ev ψ (measurementEigenProjector M a j) else 0 := by
  rw [selectedProjector_mul_effect_eq_sum, ev_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (a, j) ∈ L
  · simp only [if_pos h]
    exact ev_scale ψ (measurementEigenvalue M a j) (measurementEigenProjector M a j)
  · simp only [if_neg h]
    simpa using ev_zero (ι := ι) ψ

/-- The selected overlap from the blueprint is precisely the sum of local
selected-effect expectations. -/
theorem sum_ev_selectedProjector_mul_effect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι)
    (L : Finset (Outcome × ι)) :
    (∑ a : Outcome, ev ψ (selectedProjector M L a * M.outcome a)) =
      ∑ p ∈ L, measurementEigenvalue M p.1 p.2 *
        ev ψ (measurementEigenProjector M p.1 p.2) := by
  classical
  simp_rw [ev_selectedProjector_mul_effect]
  calc
    (∑ x : Outcome, ∑ j : ι,
        if (x, j) ∈ L then
          measurementEigenvalue M x j * ev ψ (measurementEigenProjector M x j) else 0) =
        ∑ p : Outcome × ι, if p ∈ L then
          measurementEigenvalue M p.1 p.2 * ev ψ (measurementEigenProjector M p.1 p.2)
          else 0 := by rw [Fintype.sum_prod_type]
    _ = ∑ p ∈ L, measurementEigenvalue M p.1 p.2 *
          ev ψ (measurementEigenProjector M p.1 p.2) := by simp

/-- Global rank allocation produces commuting local projectors with total
rank `dim H` and selected overlap at least `1 − Δ`. -/
theorem exists_selected_projectors {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (M : Measurement Outcome ι) :
    ∃ L : Finset (Outcome × ι),
      (∀ a, MIPStarRE.Quantum.IsProj (selectedProjector M L a)) ∧
      (∀ a, selectedProjector M L a * M.outcome a =
        M.outcome a * selectedProjector M L a) ∧
      (∑ a, (selectedProjector M L a).rank) = Fintype.card ι ∧
      1 - idempotenceDefect ψ M ≤
        ∑ a, ev ψ (selectedProjector M L a * M.outcome a) := by
  classical
  obtain ⟨L, hcard, hoverlap⟩ := exists_selected_overlap_ge_one_sub_defect ψ hψ M
  refine ⟨L, (selectedProjector_isProj M L),
    (selectedProjector_commutes M L), ?_, ?_⟩
  · rw [sum_selectedProjector_rank_eq_card, hcard]
  · rwa [sum_ev_selectedProjector_mul_effect]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
