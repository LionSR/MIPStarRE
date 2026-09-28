import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.RankAllocation
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.Defect
import MIPStarRE.LDT.Basic.OperatorExpectations
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Total spectral mass of a measurement

The global rank allocation in the simplified proof uses the ordinary trace
of a complete measurement to show that all outcome eigenvalues together have
sum equal to the Hilbert-space dimension.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, equation preceding
  `eq:global-rank-allocation`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The `j`-th eigenvalue of outcome effect `Mₐ`, using the Hermitian
eigenbasis chosen by Mathlib. -/
noncomputable def measurementEigenvalue {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (j : ι) : ℝ :=
  (show (M.outcome a).IsHermitian from M.outcome_hermitian a).eigenvalues j

/-- Every measurement eigenvalue is nonnegative. -/
theorem measurementEigenvalue_nonneg {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (j : ι) :
    0 ≤ measurementEigenvalue M a j := by
  have hpsd : (M.outcome a).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (M.outcome_pos a)
  simpa [measurementEigenvalue] using hpsd.eigenvalues_nonneg j

/-- Every measurement eigenvalue is at most one. -/
theorem measurementEigenvalue_le_one {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (j : ι) :
    measurementEigenvalue M a j ≤ 1 := by
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  have hsa : IsSelfAdjoint (M.outcome a) := hM.isSelfAdjoint
  have hle : cfc (id : Error → Error) (M.outcome a) ≤ 1 := by
    simpa [cfc_id ℝ (M.outcome a) (ha := hsa)] using M.outcome_le_one a
  have hspectrum :=
    (cfc_le_one_iff (f := id) (a := M.outcome a) (ha := hsa)).mp hle
  exact hspectrum (hM.eigenvalues j) (hM.eigenvalues_mem_spectrum_real j)

/-- The rank-one projector onto an eigenvector of an outcome effect. -/
noncomputable def measurementEigenProjector {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (j : ι) :
    MIPStarRE.Quantum.Op ι :=
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  Matrix.vecMulVec ((hM.eigenvectorBasis j).ofLp)
    (star ((hM.eigenvectorBasis j).ofLp))

/-- Every rank-one spectral projector is positive semidefinite. -/
theorem measurementEigenProjector_nonneg {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (j : ι) :
    0 ≤ measurementEigenProjector M a j := by
  unfold measurementEigenProjector
  exact Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.posSemidef_vecMulVec_self_star _)

/-- A state assigns nonnegative mass to each rank-one spectral projector. -/
theorem ev_measurementEigenProjector_nonneg {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι) (a : Outcome) (j : ι) :
    0 ≤ ev ψ (measurementEigenProjector M a j) :=
  ev_nonneg_of_psd ψ (measurementEigenProjector M a j)
    (measurementEigenProjector_nonneg M a j)

/-- The eigenvalues of all effects of a complete measurement sum to the
dimension of the local Hilbert space. -/
theorem sum_measurement_eigenvalues_eq_card {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) :
    (∑ p : Outcome × ι, measurementEigenvalue M p.1 p.2) = Fintype.card ι := by
  have htrace :
      (∑ a : Outcome, (M.outcome a).trace) = (Fintype.card ι : ℂ) := by
    rw [← Matrix.trace_sum, M.sum_eq_total, M.total_eq_one, Matrix.trace_one]
  have hcomplex :
      (∑ p : Outcome × ι,
        (measurementEigenvalue M p.1 p.2 : ℂ)) =
        (Fintype.card ι : ℂ) := by
    calc
      (∑ p : Outcome × ι,
          (measurementEigenvalue M p.1 p.2 : ℂ)) =
          ∑ a : Outcome, ∑ j : ι,
            (measurementEigenvalue M a j : ℂ) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ a : Outcome, (M.outcome a).trace := by
            apply Finset.sum_congr rfl
            intro a _
            exact (show (M.outcome a).IsHermitian from M.outcome_hermitian a)
              |>.trace_eq_sum_eigenvalues.symm
      _ = Fintype.card ι := htrace
  exact_mod_cast hcomplex

/-- Spectral expansion of a function of one measurement effect in the
eigenbasis used by the global rank selection. -/
theorem measurement_cfc_eq_sum_eigenprojectors {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (a : Outcome) (f : ℝ → ℝ) :
    cfc f (M.outcome a) =
      ∑ j : ι, ((f (measurementEigenvalue M a j) : ℂ) •
        measurementEigenProjector M a j) := by
  classical
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  calc
    cfc f (M.outcome a) = hM.cfc f := hM.cfc_eq f
    _ = ∑ j : ι, ((f (measurementEigenvalue M a j) : ℂ) •
        measurementEigenProjector M a j) := by
      ext r c
      simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
        Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp [measurementEigenvalue, measurementEigenProjector,
        Matrix.smul_apply, Matrix.vecMulVec_apply]
      ring

/-- The quadratic spectral mass in the selected-overlap inequality is the
state expectation of `Σₐ Mₐ²`. -/
theorem sum_quadratic_spectral_mass {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι) :
    (∑ p : Outcome × ι, (measurementEigenvalue M p.1 p.2) ^ 2 *
      ev ψ (measurementEigenProjector M p.1 p.2)) =
      ∑ a, ev ψ (M.outcome a * M.outcome a) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  let hM : (M.outcome a).IsHermitian := M.outcome_hermitian a
  have hpow : cfc (fun x : Error => x ^ (2 : Nat)) (M.outcome a) =
      M.outcome a * M.outcome a := by
    rw [cfc_pow_id (R := ℝ) (M.outcome a) 2 (ha := hM.isSelfAdjoint)]
    simp [pow_two]
  calc
    (∑ j : ι, (measurementEigenvalue M a j) ^ 2 *
        ev ψ (measurementEigenProjector M a j)) =
        ∑ j : ι, ev ψ (((measurementEigenvalue M a j ^ 2 : ℝ) : ℂ) •
          measurementEigenProjector M a j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact (ev_scale ψ ((measurementEigenvalue M a j) ^ 2)
              (measurementEigenProjector M a j)).symm
    _ = ev ψ (∑ j : ι, (((measurementEigenvalue M a j ^ 2 : ℝ) : ℂ) •
          measurementEigenProjector M a j)) := by rw [ev_sum]
    _ = ev ψ (cfc (fun x : Error => x ^ (2 : Nat)) (M.outcome a)) := by
          rw [measurement_cfc_eq_sum_eigenprojectors]
    _ = ev ψ (M.outcome a * M.outcome a) := by rw [hpow]

/-- Select exactly `dim H` outcome eigenvectors whose state-weighted overlap
dominates the quadratic spectral mass of the whole measurement.  This is the
finite-dimensional selection step used to construct the projectors `Qₐ` in
the simplified proof. -/
theorem exists_selected_spectral_overlap {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι) :
    ∃ L : Finset (Outcome × ι), L.card = Fintype.card ι ∧
      (∑ p ∈ L, measurementEigenvalue M p.1 p.2 *
        ev ψ (measurementEigenProjector M p.1 p.2)) ≥
      ∑ p : Outcome × ι, (measurementEigenvalue M p.1 p.2) ^ 2 *
        ev ψ (measurementEigenProjector M p.1 p.2) := by
  classical
  exact selected_spectral_overlap
    (fun p : Outcome × ι => measurementEigenvalue M p.1 p.2)
    (fun p : Outcome × ι => ev ψ (measurementEigenProjector M p.1 p.2))
    (Fintype.card ι)
    (fun p => measurementEigenvalue_nonneg M p.1 p.2)
    (fun p => measurementEigenvalue_le_one M p.1 p.2)
    (sum_measurement_eigenvalues_eq_card M)

/-- The selected rank-one spectral mass is at least `1 − Δ`, where `Δ` is
the state-dependent idempotence defect.  This is `eq:selected-overlap` in the
simplified blueprint. -/
theorem exists_selected_overlap_ge_one_sub_defect {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (M : Measurement Outcome ι) :
    ∃ L : Finset (Outcome × ι), L.card = Fintype.card ι ∧
      1 - idempotenceDefect ψ M ≤
        ∑ p ∈ L, measurementEigenvalue M p.1 p.2 *
          ev ψ (measurementEigenProjector M p.1 p.2) := by
  obtain ⟨L, hLcard, hbound⟩ := exists_selected_spectral_overlap ψ M
  refine ⟨L, hLcard, ?_⟩
  rw [sum_quadratic_spectral_mass] at hbound
  rw [idempotenceDefect_eq_one_sub_sum_squares ψ hψ M]
  linarith only [hbound]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
