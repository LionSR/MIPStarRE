import MIPStarRE.LDT.Pasting.Defs.Tuples

/-!
# Section 12 — Definitions: interpolation

Interpolation helpers extracted from `Pasting.Defs`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Remove the first coordinate from a tuple of slice questions. -/
def pointTupleTail {params : Parameters} {k : ℕ}
    (xs : PointTuple params (k + 1)) : PointTuple params k :=
  fun i => xs i.succ

/-- Remove the first coordinate from a tuple of completed slice outcomes. -/
def gHatTupleOutcomeTail {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params (k + 1)) : GHatTupleOutcome params k :=
  fun i => gs i.succ

/-- Fallback global polynomial used when all completed slice outcomes are `⊥`.
Uses the zero polynomial (trivially low individual degree). -/
noncomputable def fallbackInterpolatedPolynomial (params : Parameters) [FieldModel params.q] :
    Polynomial params.next where
  poly := 0
  lowIndividualDegree := by
    intro i
    simp [MvPolynomial.degreeOf_zero]

/-- Extract the polynomial from a genuine slice outcome. -/
noncomputable def extractSlicePoly {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) (i : Fin k)
    (hi : i ∈ gHatTupleSupport gs) : Polynomial params := by
  classical
  exact (gs i).get (by
    cases hgi : gs i with
    | none =>
        have hisSome : (gs i).isSome = true := by
          simpa [gHatTupleSupport] using hi
        simp [Option.isSome, hgi] at hisSome
    | some p =>
        simp)

/-- Extract the polynomial from a genuine (Some) slice outcome, or fallback to zero. -/
noncomputable def extractSliceOr0 {params : Parameters} [FieldModel params.q]
    (g : GHatOutcome params) : PolynomialModel params :=
  match g with
  | some p => p.poly
  | none => 0

/-- The zero fallback and genuine slice outcomes are low individual degree. -/
private theorem extractSliceOr0_lowIndividualDegree {params : Parameters} [FieldModel params.q]
    (g : GHatOutcome params) (i : Fin params.m) :
    MvPolynomial.degreeOf i (extractSliceOr0 g) ≤ params.d := by
  cases g with
  | none =>
      simp [extractSliceOr0, MvPolynomial.degreeOf_zero]
  | some p =>
      exact p.lowIndividualDegree i

/-- The old-coordinate embedding into the appended coordinate space is injective. -/
private theorem embedCoord_injective (params : Parameters) :
    Function.Injective (embedCoord params) := by
  intro a b h
  simp only [embedCoord, Fin.mk.injEq] at h
  exact Fin.ext h

/-- The appended last coordinate is outside the image of the old-coordinate embedding. -/
private theorem degreeOf_rename_embedCoord_last (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) :
    MvPolynomial.degreeOf (lastCoord params)
      (MvPolynomial.rename (embedCoord params) p : PolynomialModel params.next) = 0 := by
  rw [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective
    (embedCoord_injective params)]
  simp only [Multiset.count_eq_zero, Multiset.mem_map]
  rintro ⟨b, _, hb⟩
  simp only [embedCoord, lastCoord, Fin.ext_iff] at hb
  omega

/-- Substituting a univariate polynomial into one multivariate variable preserves its
degree bound in that variable and gives degree zero in all other variables. -/
private theorem degreeOf_eval₂_C_X_le_natDegree {K σ : Type*} [Field K] [DecidableEq σ]
    (p : _root_.Polynomial K) (i j : σ) :
    MvPolynomial.degreeOf i
      (p.eval₂ MvPolynomial.C (MvPolynomial.X j) : MvPolynomial σ K) ≤
        if i = j then p.natDegree else 0 := by
  rw [_root_.Polynomial.eval₂_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le i (Finset.range (p.natDegree + 1)) _).trans ?_
  refine Finset.sup_le fun n hn => ?_
  calc
    MvPolynomial.degreeOf i
        (MvPolynomial.C (p.coeff n) * MvPolynomial.X j ^ n : MvPolynomial σ K)
        ≤ MvPolynomial.degreeOf i (MvPolynomial.X j ^ n : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_C_mul_le _ _ _
    _ ≤ n * MvPolynomial.degreeOf i (MvPolynomial.X j : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_pow_le _ _ _
    _ ≤ if i = j then p.natDegree else 0 := by
          by_cases hij : i = j
          · have hn_le : n ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            simp [hij, MvPolynomial.degreeOf_X, hn_le]
          · simp [hij, MvPolynomial.degreeOf_X]

/-- Each Lagrange basis polynomial has degree at most one less than the size of the
interpolation support, without requiring distinct interpolation nodes. -/
private theorem natDegree_lagrangeBasis_le_card_sub_one {K ρ : Type*} [Field K] [DecidableEq ρ]
    {s : Finset ρ} {v : ρ → K} {i : ρ} (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree ≤ s.card - 1 := by
  rw [Lagrange.basis]
  calc
    (∏ j ∈ s.erase i, Lagrange.basisDivisor (v i) (v j)).natDegree
        ≤ ∑ j ∈ s.erase i, (Lagrange.basisDivisor (v i) (v j)).natDegree := by
          exact _root_.Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ s.erase i, 1 := by
          exact Finset.sum_le_sum fun j _ => by
            rw [Lagrange.basisDivisor]
            exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
              (_root_.Polynomial.natDegree_X_sub_C_le _)
    _ = s.card - 1 := by
          simp [Finset.card_erase_of_mem hi]

/-- An interpolation-eligible tuple has at least `d+1` genuine outcomes. -/
private theorem interpolationEligible_card_le {params : Parameters} {k : ℕ}
    [FieldModel params.q] {gs : GHatTupleOutcome params k}
    (hEligible : InterpolationEligible params gs) :
    params.d + 1 ≤ (gHatTupleSupport gs).card := by
  simpa [InterpolationEligible, gHatTupleHammingWeight] using hEligible

/-- A chosen `d+1`-element subset of the genuine completed-slice support. -/
noncomputable def interpolationSupportSubset {params : Parameters} {k : ℕ}
    [FieldModel params.q] (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) : Finset (Fin k) :=
  Classical.choose <|
    Finset.exists_subset_card_eq (interpolationEligible_card_le hEligible)

/-- The chosen interpolation support lies inside the genuine support.
Used downstream to ensure the Lagrange interpolation correctness property
(`Lagrange.eval_basis_self`) holds when combined with `distinctTupleDistribution`. -/
theorem interpolationSupportSubset_subset {params : Parameters} {k : ℕ}
    [FieldModel params.q] (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    interpolationSupportSubset gs hEligible ⊆ gHatTupleSupport gs :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (interpolationEligible_card_le hEligible))).1

/-- The chosen interpolation support has exactly `d+1` points. -/
theorem interpolationSupportSubset_card {params : Parameters} {k : ℕ}
    [FieldModel params.q] (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    (interpolationSupportSubset gs hEligible).card = params.d + 1 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (interpolationEligible_card_le hEligible))).2

/-- Interpolate from a specified `d+1`-element index set to recover
a polynomial in `m+1` variables via Lagrange interpolation.
The degree bound (`lowIndividualDegree ≤ d`) holds for any `σ`;
the interpolation correctness property (that `restrictAtHeight`
of the result agrees with each slice) additionally requires
`σ ⊆ gHatTupleSupport gs` and distinct evaluation points, which
are ensured by the caller via `interpolationSupportSubset_subset`
and `distinctTupleDistribution`.

The coefficient is Mathlib's `Lagrange.basis σ v i`, the polynomial
`∏ j ∈ σ.erase i, (X - v j) / (v i - v j)`, evaluated at the appended
coordinate. -/
noncomputable def interpolateCompletedSlicesFromSupport (params : Parameters)
    [FieldModel params.q] {k : ℕ} (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) (σ : Finset (Fin k))
    (hσcard : σ.card = params.d + 1) : Polynomial params.next where
  poly := ∑ i ∈ σ,
    let slicePoly :=
      MvPolynomial.rename (embedCoord params)
        (extractSliceOr0 (gs i))
    let Li : _root_.Polynomial (Scalar params) :=
      Lagrange.basis σ (fun i => decodeScalar (xs i)) i
    let LiMv :=
      Li.eval₂ MvPolynomial.C
        (MvPolynomial.X (lastCoord params))
    LiMv * slicePoly
  lowIndividualDegree := by
    intro coord
    refine (MvPolynomial.degreeOf_sum_le coord σ _).trans ?_
    refine Finset.sup_le fun idx hidx => ?_
    let slicePoly : PolynomialModel params.next :=
      MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs idx))
    let Li : _root_.Polynomial (Scalar params) :=
      Lagrange.basis σ (fun i => decodeScalar (xs i)) idx
    let LiMv : PolynomialModel params.next :=
      Li.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
    have hLi_natDegree : Li.natDegree ≤ params.d := by
      have hbasis :
          Li.natDegree ≤ σ.card - 1 := by
        exact natDegree_lagrangeBasis_le_card_sub_one hidx
      simpa [Li, hσcard] using hbasis
    by_cases hcoord : coord.val < params.m
    · let oldCoord : Fin params.m := ⟨coord.val, hcoord⟩
      have hcoord_eq : embedCoord params oldCoord = coord := by
        ext
        simp [embedCoord, oldCoord]
      have hcoord_ne_last : coord ≠ lastCoord params := by
        intro h
        have hval : coord.val = params.m := by
          simpa [lastCoord] using congrArg Fin.val h
        omega
      have hLiMv_zero : MvPolynomial.degreeOf coord LiMv ≤ 0 := by
        simpa [LiMv, hcoord_ne_last] using
          (degreeOf_eval₂_C_X_le_natDegree
            (p := Li) (i := coord) (j := lastCoord params))
      have hslice : MvPolynomial.degreeOf coord slicePoly ≤ params.d := by
        change MvPolynomial.degreeOf coord
            (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs idx)) :
              PolynomialModel params.next) ≤ params.d
        rw [← hcoord_eq, MvPolynomial.degreeOf_rename_of_injective
          (embedCoord_injective params)]
        exact extractSliceOr0_lowIndividualDegree (gs idx) oldCoord
      calc
        MvPolynomial.degreeOf coord (LiMv * slicePoly)
            ≤ MvPolynomial.degreeOf coord LiMv + MvPolynomial.degreeOf coord slicePoly := by
              exact MvPolynomial.degreeOf_mul_le _ _ _
        _ ≤ 0 + params.d := Nat.add_le_add hLiMv_zero hslice
        _ = params.d := by simp
    · have hcoord_eq_last : coord = lastCoord params := by
        have hlt_succ : coord.val < params.m + 1 := by
          simpa [Parameters.next] using coord.isLt
        have hle : params.m ≤ coord.val := Nat.le_of_not_gt hcoord
        have hval : coord.val = params.m := le_antisymm (Nat.le_of_lt_succ hlt_succ) hle
        ext
        simp [lastCoord, hval]
      subst coord
      have hLiMv : MvPolynomial.degreeOf (lastCoord params) LiMv ≤ params.d := by
        have hLiMv_nat :
            MvPolynomial.degreeOf (lastCoord params) LiMv ≤ Li.natDegree := by
          simpa [LiMv] using
            (degreeOf_eval₂_C_X_le_natDegree
              (p := Li) (i := lastCoord params) (j := lastCoord params))
        exact hLiMv_nat.trans hLi_natDegree
      have hslice_zero : MvPolynomial.degreeOf (lastCoord params) slicePoly ≤ 0 := by
        change MvPolynomial.degreeOf (lastCoord params)
            (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs idx)) :
              PolynomialModel params.next) ≤ 0
        rw [degreeOf_rename_embedCoord_last]
      calc
        MvPolynomial.degreeOf (lastCoord params) (LiMv * slicePoly)
            ≤ MvPolynomial.degreeOf (lastCoord params) LiMv +
                MvPolynomial.degreeOf (lastCoord params) slicePoly := by
              exact MvPolynomial.degreeOf_mul_le _ _ _
        _ ≤ params.d + 0 := Nat.add_le_add hLiMv hslice_zero
        _ = params.d := by simp

end MIPStarRE.LDT.Pasting
