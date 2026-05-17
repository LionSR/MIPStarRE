import MIPStarRE.Quantum.FiniteMatrix
import Mathlib.Analysis.Matrix.Spectrum

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Projector Range Orthonormal Bases

This file packages the finite-dimensional spectral decomposition of an
orthogonal projector as an orthonormal basis of its range. It supplies the
rank-one decomposition needed by the rank-reduction truncation branch in the
low-degree-test formalization.

## References

- `references/ldt-paper/orthonormalization.tex`, lines 570--573.
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator

namespace MIPStarRE.Quantum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral expansion of a Hermitian matrix as a sum of rank-one eigenvector
projectors weighted by eigenvalues. -/
lemma hermitian_eq_sum_eigenvalues_vecMulVec (A : Op ι) (hA : A.IsHermitian) :
    A = ∑ i : ι, ((hA.eigenvalues i : ℂ) •
      Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
        (star ((hA.eigenvectorBasis i).ofLp))) := by
  classical
  calc
    A = Unitary.conjStarAlgAut ℂ (Op ι) hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
    _ = ∑ i : ι, ((hA.eigenvalues i : ℂ) •
        Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
          (star ((hA.eigenvectorBasis i).ofLp))) := by
          ext r c
          simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.sum_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          simp [Matrix.smul_apply, Matrix.vecMulVec_apply]
          ring

/-- For a Hermitian idempotent matrix, every eigenvalue is either `0` or `1`. -/
lemma IsProj.eigenvalues_zero_or_one (P : Op ι) (hP : IsProj P) (i : ι) :
    hP.isHermitian.eigenvalues i = 0 ∨ hP.isHermitian.eigenvalues i = 1 := by
  let v : ι → ℂ := (hP.isHermitian.eigenvectorBasis i).ofLp
  have hv_ne : v ≠ 0 := by
    change (hP.isHermitian.eigenvectorBasis i).ofLp ≠ 0
    simpa using hP.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
  have hmul1 : P *ᵥ v = hP.isHermitian.eigenvalues i • v := by
    simpa [v] using hP.isHermitian.mulVec_eigenvectorBasis i
  have hmul2 : P *ᵥ (P *ᵥ v) = P *ᵥ v := by
    simp [v, hP.idempotent]
  have hscalar : hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i =
      hP.isHermitian.eigenvalues i := by
    have htmp : (hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i) • v =
        hP.isHermitian.eigenvalues i • v := by
      calc
        (hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i) • v
            = hP.isHermitian.eigenvalues i •
                (hP.isHermitian.eigenvalues i • v) := by
              exact (smul_smul (hP.isHermitian.eigenvalues i)
                (hP.isHermitian.eigenvalues i) v).symm
        _ = hP.isHermitian.eigenvalues i • (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ (hP.isHermitian.eigenvalues i • v) := by
              exact (Matrix.mulVec_smul P (hP.isHermitian.eigenvalues i) v).symm
        _ = P *ᵥ (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ v := hmul2
        _ = hP.isHermitian.eigenvalues i • v := hmul1
    exact (smul_left_injective ℝ hv_ne) htmp
  have hfactor :
      hP.isHermitian.eigenvalues i * (hP.isHermitian.eigenvalues i - 1) = 0 := by
    nlinarith [hscalar]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · right
    linarith

/-- A projector is the sum of the rank-one projectors onto the eigenvectors with
nonzero eigenvalue. For a projector these are exactly the `1`-eigenvectors. -/
lemma IsProj.eq_sum_nonzero_eigenvector_projectors (P : Op ι) (hP : IsProj P) :
    P = ∑ i : {i // hP.isHermitian.eigenvalues i ≠ 0},
      Matrix.vecMulVec ((hP.isHermitian.eigenvectorBasis i.1).ofLp)
        (star ((hP.isHermitian.eigenvectorBasis i.1).ofLp)) := by
  classical
  let p : ι → Prop := fun i => hP.isHermitian.eigenvalues i ≠ 0
  let E : ι → Op ι := fun i =>
    Matrix.vecMulVec ((hP.isHermitian.eigenvectorBasis i).ofLp)
      (star ((hP.isHermitian.eigenvectorBasis i).ofLp))
  calc
    P = ∑ i : ι, ((hP.isHermitian.eigenvalues i : ℂ) • E i) := by
          simpa [E] using hermitian_eq_sum_eigenvalues_vecMulVec P hP.isHermitian
    _ = ∑ i : ι, if p i then E i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rcases hP.eigenvalues_zero_or_one P i with hzero | hone
          · simp [p, E, hzero]
          · simp [p, E, hone]
    _ = ∑ i : {i // p i}, E i.1 := by
          rw [← Finset.sum_filter]
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp [p]

/-- The trace of a finite-dimensional orthogonal projector equals its rank. -/
lemma IsProj.trace_eq_rank (Q : Op ι) (hQ : IsProj Q) :
    Q.trace = (Q.rank : ℂ) := by
  classical
  let p : ι → Prop := fun i => hQ.isHermitian.eigenvalues i ≠ 0
  let indicator : ι → ℕ := fun i => if p i then 1 else 0
  have hp_nat : Fintype.card {i // p i} = ∑ i, indicator i := by
    rw [Fintype.card_subtype p]
    simpa [p, indicator] using Finset.card_filter p (Finset.univ : Finset ι)
  have hp_complex : (Fintype.card {i // p i} : ℂ) = ∑ i, (indicator i : ℂ) := by
    exact_mod_cast hp_nat
  have h_indicator : ∀ i, (indicator i : ℂ) = (hQ.isHermitian.eigenvalues i : ℂ) := by
    intro i
    rcases hQ.eigenvalues_zero_or_one Q i with hzero | hone
    · simp [p, indicator, hzero]
    · simp [p, indicator, hone]
  calc
    Q.trace = ∑ i, (hQ.isHermitian.eigenvalues i : ℂ) :=
      hQ.isHermitian.trace_eq_sum_eigenvalues
    _ = ∑ i, (indicator i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          symm
          exact h_indicator i
    _ = Fintype.card {i // p i} := by symm; exact hp_complex
    _ = (Q.rank : ℂ) := by rw [hQ.isHermitian.rank_eq_card_non_zero_eigs]

/-- A rank-indexed orthonormal basis of the range of a projector, packaged with
the corresponding rank-one decomposition. -/
structure ProjectorRangeONB (P : Op ι) (hP : IsProj P) where
  /-- The chosen range basis vectors. -/
  vec : Fin P.rank → ι → ℂ
  /-- The chosen vectors are orthonormal. -/
  orthonormal : ∀ i j, star (vec i) ⬝ᵥ vec j = if i = j then 1 else 0
  /-- The projector decomposes as the sum of the rank-one projectors onto the
  chosen range basis. -/
  decomposition : P = ∑ i, Matrix.vecMulVec (vec i) (star (vec i))

namespace ProjectorRangeONB

variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)

/-- The rank-one projector attached to one vector of a projector range ONB. -/
noncomputable def rankOne (i : Fin P.rank) : Op ι :=
  Matrix.vecMulVec (b.vec i) (star (b.vec i))

/-- The partial projector obtained by summing a subset of range ONB rank-one projectors. -/
noncomputable def subprojector (S : Finset (Fin P.rank)) : Op ι :=
  ∑ i ∈ S, b.rankOne i

@[simp] lemma rankOne_apply (i : Fin P.rank) :
    b.rankOne i = Matrix.vecMulVec (b.vec i) (star (b.vec i)) := rfl

/-- Rank-one projectors from an orthonormal family multiply as Kronecker deltas. -/
lemma rankOne_mul (i j : Fin P.rank) :
    b.rankOne i * b.rankOne j = if i = j then b.rankOne i else 0 := by
  rw [rankOne, rankOne, Matrix.vecMulVec_mul_vecMulVec]
  have horth := b.orthonormal i j
  by_cases hij : i = j
  · subst hij
    rw [horth]
    simp
  · have hzero : star (b.vec i) ⬝ᵥ b.vec j = 0 := by simpa [hij] using horth
    rw [hzero]
    simp [hij]

/-- A rank-one projector from the chosen range basis acts by the corresponding
Kronecker delta on basis vectors. -/
lemma rankOne_mulVec_vec (i j : Fin P.rank) :
    b.rankOne i *ᵥ b.vec j = if i = j then b.vec i else 0 := by
  rw [rankOne, Matrix.vecMulVec_mulVec]
  have horth := b.orthonormal i j
  by_cases hij : i = j
  · subst hij
    rw [horth]
    simp
  · have hzero : star (b.vec i) ⬝ᵥ b.vec j = 0 := by simpa [hij] using horth
    rw [hzero]
    simp [hij]

/-- Each vector in the chosen orthonormal basis of the range is fixed by the
projector. -/
lemma mulVec_vec (i : Fin P.rank) :
    P *ᵥ b.vec i = b.vec i := by
  calc
    P *ᵥ b.vec i =
        (∑ j, Matrix.vecMulVec (b.vec j) (star (b.vec j))) *ᵥ b.vec i := by
          rw [← b.decomposition]
    _ = b.vec i := by
          rw [Matrix.sum_mulVec]
          rw [Finset.sum_eq_single i]
          · rw [Matrix.vecMulVec_mulVec]
            have horth := b.orthonormal i i
            rw [horth]
            simp
          · intro j _ hji
            rw [Matrix.vecMulVec_mulVec]
            have horth := b.orthonormal j i
            have hzero : star (b.vec j) ⬝ᵥ b.vec i = 0 := by simpa [hji] using horth
            rw [hzero]
            simp
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))

/-- A selected sum of orthonormal rank-one projectors is Hermitian. -/
lemma subprojector_isHermitian (S : Finset (Fin P.rank)) :
    (b.subprojector S).IsHermitian := by
  classical
  unfold subprojector rankOne
  rw [Matrix.IsHermitian]
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_vecMulVec]

/-- A selected sum of orthonormal rank-one projectors is idempotent. -/
lemma subprojector_idempotent (S : Finset (Fin P.rank)) :
    b.subprojector S * b.subprojector S = b.subprojector S := by
  classical
  unfold subprojector
  calc
    (∑ i ∈ S, b.rankOne i) * (∑ j ∈ S, b.rankOne j)
        = ∑ i ∈ S, ∑ j ∈ S, b.rankOne i * b.rankOne j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i ∈ S, b.rankOne i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_eq_single i]
          · rw [b.rankOne_mul i i]
            simp
          · intro j hj hji
            have hij : i ≠ j := fun hij => hji hij.symm
            rw [b.rankOne_mul i j]
            simp [hij]
          · intro hi_not
            exact False.elim (hi_not hi)

/-- A selected sum of orthonormal rank-one projectors is a projector. -/
lemma subprojector_isProj (S : Finset (Fin P.rank)) :
    IsProj (b.subprojector S) where
  isHermitian := b.subprojector_isHermitian S
  idempotent := b.subprojector_idempotent S

/-- The partial projector's trace is the number of selected vectors. -/
lemma subprojector_trace (S : Finset (Fin P.rank)) :
    (b.subprojector S).trace = (S.card : ℂ) := by
  classical
  unfold subprojector rankOne
  calc
    (∑ i ∈ S, Matrix.vecMulVec (b.vec i) (star (b.vec i))).trace
        = ∑ i ∈ S, (Matrix.vecMulVec (b.vec i) (star (b.vec i))).trace := by
            rw [Matrix.trace_sum]
    _ = ∑ _i ∈ S, (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Matrix.trace_vecMulVec]
          simpa [dotProduct_comm] using b.orthonormal i i
    _ = (S.card : ℂ) := by simp

/-- The rank of a selected sum is exactly the number of selected ONB vectors. -/
lemma subprojector_rank (S : Finset (Fin P.rank)) :
    (b.subprojector S).rank = S.card := by
  have htrace_rank := IsProj.trace_eq_rank (b.subprojector S) (b.subprojector_isProj S)
  have htrace_card := b.subprojector_trace S
  have hcast : ((b.subprojector S).rank : ℂ) = (S.card : ℂ) := by
    rw [← htrace_rank, htrace_card]
  exact_mod_cast hcast

/-- A partial projector plus its complementary partial projector is the original projector. -/
lemma subprojector_add_compl (S : Finset (Fin P.rank)) :
    b.subprojector S + b.subprojector (Sᶜ : Finset (Fin P.rank)) = P := by
  calc
    b.subprojector S + b.subprojector (Sᶜ : Finset (Fin P.rank))
        = (∑ i ∈ S, b.rankOne i) +
            ∑ i ∈ (Sᶜ : Finset (Fin P.rank)), b.rankOne i := rfl
    _ = ∑ i : Fin P.rank, b.rankOne i := by rw [Finset.sum_add_sum_compl]
    _ = P := by simpa [rankOne] using b.decomposition.symm

/-- The difference between a projector and a partial projector is the
complementary partial projector. -/
lemma subprojector_diff_eq_compl (S : Finset (Fin P.rank)) :
    P - b.subprojector S = b.subprojector (Sᶜ : Finset (Fin P.rank)) := by
  have h := congrArg (fun X : Op ι => X - b.subprojector S) (b.subprojector_add_compl S).symm
  have hcancel :
      (b.subprojector S + b.subprojector (Sᶜ : Finset (Fin P.rank))) - b.subprojector S =
        b.subprojector (Sᶜ : Finset (Fin P.rank)) := by
    abel
  exact h.trans hcancel

/-- A partial projector is dominated by the original projector. -/
lemma subprojector_le (S : Finset (Fin P.rank)) :
    b.subprojector S ≤ P := by
  rw [← sub_nonneg]
  rw [b.subprojector_diff_eq_compl S]
  exact (b.subprojector_isProj (Sᶜ : Finset (Fin P.rank))).isStarProjection.nonneg

end ProjectorRangeONB

/-- The nonzero-eigenvalue index set of a projector has cardinality equal to its
matrix rank. -/
private noncomputable def IsProj.nonzeroEigenEquivFinRank (P : Op ι) (hP : IsProj P) :
    {i : ι // hP.isHermitian.eigenvalues i ≠ 0} ≃ Fin P.rank :=
  Fintype.equivFinOfCardEq hP.isHermitian.rank_eq_card_non_zero_eigs.symm

/-- Choose an orthonormal basis of the range of a projector using Mathlib's
Hermitian spectral theorem. -/
noncomputable def IsProj.rangeONB (P : Op ι) (hP : IsProj P) :
    ProjectorRangeONB P hP := by
  classical
  let e := hP.nonzeroEigenEquivFinRank P
  let vec : Fin P.rank → ι → ℂ := fun i =>
    (hP.isHermitian.eigenvectorBasis (e.symm i).1).ofLp
  refine
    { vec := vec
      orthonormal := ?_
      decomposition := ?_ }
  · intro i j
    have hindex : ((e.symm i).1 = (e.symm j).1) ↔ i = j := by
      constructor
      · intro h
        exact (EquivLike.injective e.symm) (Subtype.ext h)
      · intro h
        simp [h]
    have horth := orthonormal_iff_ite.mp hP.isHermitian.eigenvectorBasis.orthonormal
      (e.symm i).1 (e.symm j).1
    simpa [vec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, hindex] using
      horth
  · have hdecomp := hP.eq_sum_nonzero_eigenvector_projectors P
    simpa [vec, e] using
      (hdecomp.trans
        ((e.symm.sum_comp
          fun i : {i : ι // hP.isHermitian.eigenvalues i ≠ 0} =>
            Matrix.vecMulVec ((hP.isHermitian.eigenvectorBasis i.1).ofLp)
              (star ((hP.isHermitian.eigenvectorBasis i.1).ofLp))).symm))

/-- An orthogonal projection is positive semidefinite. -/
lemma IsProj.nonneg (P : Op ι) (hP : IsProj P) :
    0 ≤ P := by
  exact hP.isStarProjection.nonneg

end

end MIPStarRE.Quantum
