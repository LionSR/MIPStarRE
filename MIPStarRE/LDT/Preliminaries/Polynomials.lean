import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
Polynomial preliminaries from Section 4 of
`references/ldt-paper/preliminaries.tex`.

This file packages the paper's low-individual-degree polynomial class together
with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing
multivariate polynomial theorems.
-/

open Finset Fintype

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MvPolynomial

/-- `\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree
polynomials. This is Mathlib's `MvPolynomial.restrictDegree` submodule. -/
abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d

/-- If `p ∈ polyFunc m K d`, then `p.degreeOf i ≤ d` for every variable `i`. -/
theorem degreeOf_le_of_mem_polyFunc {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hp : p ∈ polyFunc m K d) (i : Fin m) :
    p.degreeOf i ≤ d :=
  MvPolynomial.degreeOf_le_iff.mpr fun s hs =>
    (MvPolynomial.mem_restrictDegree (σ := Fin m) (R := K) p d).mp hp s hs i

/-- The uniform agreement probability of two polynomials on `K^m`, written as a
finite cardinality ratio over `K^m`. -/
noncomputable def polynomialAgreementProbability (m : ℕ) (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ (Finset.univ : Finset (Fin m → K)) |
      MvPolynomial.eval x g = MvPolynomial.eval x h} /
    (Fintype.card K ^ m : ℚ≥0)

/-- If every individual degree of `p` is at most `d`, then the total degree of
`p` is at most `m * d`. -/
theorem totalDegree_le_mul_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hdeg : ∀ i, p.degreeOf i ≤ d) :
    p.totalDegree ≤ m * d := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  calc
    s.sum (fun _ e => e) = ∑ i : Fin m, s i := by
      rw [Finsupp.sum_fintype]
      intro i
      rfl
    _ ≤ ∑ _i : Fin m, d := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s hs
    _ = m * d := by
      simp [Fintype.card_fin]

private theorem agreementEvent_eq_zeroEvent_sub {m : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : MvPolynomial (Fin m) K) :
    {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x g = MvPolynomial.eval x h} =
      {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} := by
  ext x
  simp [MvPolynomial.eval_sub, sub_eq_zero]

/-- `lem:schwartz-zippel-total-degree`.

If two polynomials on `K^m` have total degree at most `d`, then the uniform
agreement probability is at most `d / |K|`. -/
theorem schwartzZippel_totalDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : MvPolynomial (Fin m) K} (hneq : g ≠ h)
    (hg : g.totalDegree ≤ d) (hh : h.totalDegree ≤ d) :
    polynomialAgreementProbability m K g h ≤ d / Fintype.card K := by
  have hsub_ne : g - h ≠ 0 := sub_ne_zero.mpr hneq
  have hsub_deg : (g - h).totalDegree ≤ d := by
    exact (MvPolynomial.totalDegree_sub g h).trans (max_le hg hh)
  unfold polynomialAgreementProbability
  rw [agreementEvent_eq_zeroEvent_sub g h]
  calc
    #{x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} /
        (Fintype.card K ^ m : ℚ≥0)
      ≤ (g - h).totalDegree / Fintype.card K := by
          simpa using
            (MvPolynomial.schwartz_zippel_totalDegree
              (n := m) (p := g - h) hsub_ne (Finset.univ : Finset K))
    _ ≤ d / Fintype.card K := by
          gcongr

/-- Schwartz-Zippel for the paper's low-individual-degree class
`\polyfunc{m}{q}{d}`. -/
theorem schwartzZippel_individualDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
    polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K := by
  have hval_ne : g.1 ≠ h.1 := by
    intro hgh
    apply hneq
    exact Subtype.ext hgh
  have hg_degOf : ∀ i, g.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc g.property
  have hh_degOf : ∀ i, h.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc h.property
  exact schwartzZippel_totalDegree (g := g.1) (h := h.1) hval_ne
    (totalDegree_le_mul_of_degreeOf_le hg_degOf)
    (totalDegree_le_mul_of_degreeOf_le hh_degOf)

end MIPStarRE.LDT.Preliminaries
