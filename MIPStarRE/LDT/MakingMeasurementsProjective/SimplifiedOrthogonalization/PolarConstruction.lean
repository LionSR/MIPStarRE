import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SelectedProjectors
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.PolarAlgebra

/-!
# Square coordinate space for the selected eigenvectors

The global rank allocation selects exactly `dim H` eigenvectors.  Their index
type therefore has the same finite cardinality as the ambient basis, allowing
the direct-sum coordinate space in the simplified proof to be represented by a
square matrix.  The outcome-coordinate projections form a projective
measurement on that space.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, construction of `K`, `Eₐ`, and `X`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The finite type of selected outcome-eigenvector pairs. -/
abbrev SelectedCarrier {Outcome ι : Type*} [Fintype Outcome] [Fintype ι]
    (L : Finset (Outcome × ι)) := {p : Outcome × ι // p ∈ L}

/-- A selection of `dim H` pairs supplies a basis equivalence from `H` to the
selected coordinate space. -/
noncomputable def selectedCarrierEquiv {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι]
    (L : Finset (Outcome × ι)) (hcard : L.card = Fintype.card ι) :
    ι ≃ SelectedCarrier L := by
  classical
  apply Fintype.equivOfCardEq
  simpa [SelectedCarrier] using hcard.symm

/-- The coordinate projection onto rows belonging to outcome `a`. -/
noncomputable def selectedCoordinateProjector {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (e : ι ≃ SelectedCarrier L) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  Matrix.diagonal (fun r => if (e r).val.1 = a then 1 else 0)

/-- The outcome-coordinate projections form a complete projective
measurement on the selected coordinate space. -/
noncomputable def selectedCoordinateMeasurement {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (e : ι ≃ SelectedCarrier L) :
    ProjMeas Outcome ι where
  outcome := selectedCoordinateProjector L e
  total := 1
  outcome_pos := by
    intro a
    exact Matrix.nonneg_iff_posSemidef.mpr <|
      Matrix.PosSemidef.diagonal fun r => by
        by_cases h : (e r).val.1 = a <;> simp [h]
  sum_eq_total := by
    classical
    ext r s
    rw [Matrix.sum_apply]
    by_cases hrs : r = s
    · subst s
      simp [selectedCoordinateProjector]
    · simp [selectedCoordinateProjector, hrs]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := by
    intro a
    unfold selectedCoordinateProjector
    rw [Matrix.diagonal_mul_diagonal]
    ext r s
    by_cases hrs : r = s
    · subst s
      by_cases h : (e r).val.1 = a <;> simp [h]
    · simp [hrs]

/-- The square matrix whose row for a selected pair `(a,j)` is
`√λₐⱼ ⟨vₐⱼ|`.  This is the direct-sum operator `X` in the simplified proof,
after identifying its `dim H` rows with the original basis. -/
noncomputable def selectedPolarMatrix {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (e : ι ≃ SelectedCarrier L) : MIPStarRE.Quantum.Op ι :=
  fun r c =>
    let p := (e r).val
    let hM : (M.outcome p.1).IsHermitian := M.outcome_hermitian p.1
    (Real.sqrt (measurementEigenvalue M p.1 p.2) : ℂ) *
      star ((hM.eigenvectorBasis p.2).ofLp c)

/-- Reindex a sum over the selected coordinate rows as the spectral fiber for
one outcome.  This is the finite combinatorial step in `X†EₐX = QₐMₐ`. -/
theorem sum_selected_coordinate_rows {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (L : Finset (Outcome × ι)) (e : ι ≃ SelectedCarrier L)
    (a : Outcome) (f : Outcome × ι → ℂ) :
    (∑ r : ι, if (e r).val.1 = a then f (e r).val else 0) =
      ∑ j : ι, if (a, j) ∈ L then f (a, j) else 0 := by
  classical
  calc
    (∑ r : ι, if (e r).val.1 = a then f (e r).val else 0) =
        ∑ p : SelectedCarrier L, if p.val.1 = a then f p.val else 0 := by
          exact e.sum_comp
            (fun p : SelectedCarrier L => if p.val.1 = a then f p.val else (0 : ℂ))
    _ = ∑ p ∈ L, if p.1 = a then f p else 0 := by
          simpa [SelectedCarrier] using
            (Finset.sum_coe_sort L
              (fun p : Outcome × ι => if p.1 = a then f p else (0 : ℂ)))
    _ = ∑ p : Outcome × ι, if p ∈ L then if p.1 = a then f p else 0 else 0 := by
          simp
    _ = ∑ b : Outcome, ∑ j : ι,
          if (b, j) ∈ L then if b = a then f (b, j) else 0 else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ j : ι, if (a, j) ∈ L then f (a, j) else 0 := by
          calc
            (∑ b : Outcome, ∑ j : ι,
                if (b, j) ∈ L then if b = a then f (b, j) else 0 else 0) =
                ∑ b : Outcome,
                  if b = a then (∑ j : ι, if (a, j) ∈ L then f (a, j) else 0)
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro b _
                    by_cases h : b = a
                    · subst b
                      simp
                    · simp [h]
            _ = ∑ j : ι, if (a, j) ∈ L then f (a, j) else 0 := by simp

/-- The inner product of one row of `X` is its eigenvalue times the
corresponding rank-one spectral projector. -/
theorem selectedPolarMatrix_row_inner {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (e : ι ≃ SelectedCarrier L) (k r c : ι) :
    star (selectedPolarMatrix M L e k r) * selectedPolarMatrix M L e k c =
      (measurementEigenvalue M (e k).val.1 (e k).val.2 : ℂ) *
        measurementEigenProjector M (e k).val.1 (e k).val.2 r c := by
  let p := (e k).val
  let hM : (M.outcome p.1).IsHermitian := M.outcome_hermitian p.1
  let t : ℝ := Real.sqrt (measurementEigenvalue M p.1 p.2)
  have ht : t * t = measurementEigenvalue M p.1 p.2 :=
    Real.mul_self_sqrt (measurementEigenvalue_nonneg M p.1 p.2)
  change star ((t : ℂ) * star ((hM.eigenvectorBasis p.2).ofLp r)) *
      ((t : ℂ) * star ((hM.eigenvectorBasis p.2).ofLp c)) =
    (measurementEigenvalue M p.1 p.2 : ℂ) *
      (((hM.eigenvectorBasis p.2).ofLp r) *
        star ((hM.eigenvectorBasis p.2).ofLp c))
  simp only [star_mul, star_star]
  rw [show star (t : ℂ) = (t : ℂ) by simp]
  calc
    ((hM.eigenvectorBasis p.2).ofLp r) * (t : ℂ) *
        ((t : ℂ) * star ((hM.eigenvectorBasis p.2).ofLp c)) =
        ((t : ℂ) * (t : ℂ)) *
          (((hM.eigenvectorBasis p.2).ofLp r) *
            star ((hM.eigenvectorBasis p.2).ofLp c)) := by ring
    _ = (measurementEigenvalue M p.1 p.2 : ℂ) *
          (((hM.eigenvectorBasis p.2).ofLp r) *
            star ((hM.eigenvectorBasis p.2).ofLp c)) := by
            rw [← Complex.ofReal_mul, ht]

/-- The selected-row operator has the required coordinate compression:
`X† Eₐ X = Qₐ Mₐ`. -/
theorem selectedPolarMatrix_coordinate_compression {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (e : ι ≃ SelectedCarrier L) (a : Outcome) :
    (selectedPolarMatrix M L e)ᴴ * selectedCoordinateProjector L e a *
        selectedPolarMatrix M L e =
      selectedProjector M L a * M.outcome a := by
  classical
  rw [selectedProjector_mul_effect_eq_sum]
  ext r c
  let X := selectedPolarMatrix M L e
  let E := selectedCoordinateProjector L e a
  have hXE (k : ι) : (Xᴴ * E) r k =
      if (e k).val.1 = a then star (X k r) else 0 := by
    simp [E, X, selectedCoordinateProjector, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  change ((Xᴴ * E) * X) r c = _
  rw [Matrix.mul_apply]
  simp_rw [hXE]
  simp_rw [ite_mul, zero_mul]
  dsimp only [X]
  simp_rw [selectedPolarMatrix_row_inner M L e]
  let f : Outcome × ι → ℂ := fun p =>
    (measurementEigenvalue M p.1 p.2 : ℂ) *
      (measurementEigenProjector M p.1 p.2) r c
  change (∑ k : ι, if (e k).val.1 = a then f (e k).val else 0) = _
  rw [sum_selected_coordinate_rows L e a f]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (a, j) ∈ L
  · simp [h, f, measurementEigenProjector, Matrix.smul_apply]
  · simp [h]

/-- The Gram matrix of `X` is the total selected effect `S = ΣₐQₐMₐ`. -/
theorem selectedPolarMatrix_gram {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (e : ι ≃ SelectedCarrier L) :
    (selectedPolarMatrix M L e)ᴴ * selectedPolarMatrix M L e =
      ∑ a, selectedProjector M L a * M.outcome a := by
  let X := selectedPolarMatrix M L e
  let E := selectedCoordinateMeasurement L e
  have hE : (∑ a, E.outcome a) = (1 : MIPStarRE.Quantum.Op ι) := E.sum_eq
  calc
    Xᴴ * X = Xᴴ * (1 : MIPStarRE.Quantum.Op ι) * X := by simp
    _ = Xᴴ * (∑ a, E.outcome a) * X := by rw [hE]
    _ = ∑ a, Xᴴ * E.outcome a * X := by
          rw [Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ a, selectedProjector M L a * M.outcome a := by
          apply Finset.sum_congr rfl
          intro a _
          exact selectedPolarMatrix_coordinate_compression M L e a

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
