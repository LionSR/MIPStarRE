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
def extractSlicePoly {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) (i : Fin k)
    (hi : i ∈ gHatTupleSupport gs) : Polynomial params := by
  have hisSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hi
  exact (gs i).get hisSome

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

/-- `InterpolationEligible params` is decidable without invoking classical logic:
it is the finite inequality `d + 1 ≤ |support(gs)|`, where the support is computed
by filtering the finite index set. -/
instance interpolationEligible_decidablePred (params : Parameters) [FieldModel params.q]
    {k : ℕ} : DecidablePred (InterpolationEligible params (k := k)) := by
  intro gs
  unfold InterpolationEligible gHatTupleHammingWeight gHatTupleSupport
  infer_instance

/-- Select the first `n` elements of a finite linearly ordered set by sorting it and
truncating the resulting list. -/
private def takeCardSubset {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) (n : ℕ) : Finset α :=
  (s.sort (· ≤ ·)).take n |>.toFinset

/-- The sorted-take subset produced by `takeCardSubset` stays inside the original
finset. -/
private theorem takeCardSubset_subset {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) (n : ℕ) :
    takeCardSubset s n ⊆ s := by
  intro a ha
  have haTake : a ∈ (s.sort (· ≤ ·)).take n := by
    simpa [takeCardSubset] using ha
  exact (Finset.mem_sort (s := s) (r := (· ≤ ·))).mp (List.mem_of_mem_take haTake)

/-- If `n` does not exceed the size of `s`, then `takeCardSubset s n` has exactly
`n` elements. -/
private theorem takeCardSubset_card {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) {n : ℕ} (hn : n ≤ s.card) :
    (takeCardSubset s n).card = n := by
  have hNodup : ((s.sort (· ≤ ·)).take n).Nodup := by
    exact List.Nodup.sublist (List.take_sublist n (s.sort (· ≤ ·)))
      (Finset.sort_nodup s (· ≤ ·))
  rw [takeCardSubset, List.toFinset_card_of_nodup hNodup, List.length_take,
    Finset.length_sort]
  exact Nat.min_eq_left hn

/-- A canonical `d+1`-element interpolation support together with the proof fields
that show it lies inside the genuine completed-slice support. The support is built
by sorting the genuine support and taking its first `d+1` indices. -/
structure InterpolationSupportWitness (params : Parameters) [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k) where
  support : Finset (Fin k)
  subset_support : support ⊆ gHatTupleSupport gs
  card_eq : support.card = params.d + 1

/-- Construct an explicit `d+1`-point interpolation support inside the genuine support of
an interpolation-eligible tuple by taking the first `d+1` indices in sorted order. -/
def interpolationSupportWitness {params : Parameters} {k : ℕ}
    [FieldModel params.q] (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    InterpolationSupportWitness params gs :=
  { support := takeCardSubset (gHatTupleSupport gs) (params.d + 1)
    subset_support := by
      simpa using (takeCardSubset_subset (gHatTupleSupport gs) (params.d + 1))
    card_eq := by
      apply takeCardSubset_card
      simpa using (interpolationEligible_card_le hEligible) }

/-- Interpolate from a specified `d+1`-element index set to recover
a polynomial in `m+1` variables via Lagrange interpolation.
The caller must provide `hσsupport : σ ⊆ gHatTupleSupport gs`, i.e. every
interpolation node is a genuine completed-slice outcome. This keeps the support
precondition explicit instead of silently falling back to the zero polynomial.

The degree bound (`lowIndividualDegree ≤ d`) holds for any `σ` with
`σ.card = d+1`; the interpolation correctness property (that `restrictAtHeight`
of the result agrees with each slice) additionally requires distinct evaluation
points, which are ensured by the caller together with `hσsupport`.

The coefficient is Mathlib's `Lagrange.basis σ v i`, the polynomial
`∏ j ∈ σ.erase i, (X - v j) / (v i - v j)`, evaluated at the appended
coordinate. -/
noncomputable def interpolateCompletedSlicesFromSupport (params : Parameters)
    [FieldModel params.q] {k : ℕ} (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) (σ : Finset (Fin k))
    (hσsupport : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1) : Polynomial params.next where
  poly := ∑ idx ∈ σ.attach,
    let slicePoly :=
      MvPolynomial.rename (embedCoord params)
        (extractSlicePoly gs idx.1 (hσsupport idx.2)).poly
    let Li : _root_.Polynomial (Scalar params) :=
      Lagrange.basis σ (fun i => decodeScalar (xs i)) idx.1
    let LiMv :=
      Li.eval₂ MvPolynomial.C
        (MvPolynomial.X (lastCoord params))
    LiMv * slicePoly
  lowIndividualDegree := by
    intro coord
    refine (MvPolynomial.degreeOf_sum_le coord σ.attach _).trans ?_
    refine Finset.sup_le fun idx _hidx => ?_
    let slice : Polynomial params := extractSlicePoly gs idx.1 (hσsupport idx.2)
    let slicePoly : PolynomialModel params.next :=
      MvPolynomial.rename (embedCoord params) slice.poly
    let Li : _root_.Polynomial (Scalar params) :=
      Lagrange.basis σ (fun i => decodeScalar (xs i)) idx.1
    let LiMv : PolynomialModel params.next :=
      Li.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
    have hLi_natDegree : Li.natDegree ≤ params.d := by
      have hbasis : Li.natDegree ≤ σ.card - 1 := by
        exact natDegree_lagrangeBasis_le_card_sub_one idx.2
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
            (MvPolynomial.rename (embedCoord params) slice.poly :
              PolynomialModel params.next) ≤ params.d
        rw [← hcoord_eq, MvPolynomial.degreeOf_rename_of_injective
          (embedCoord_injective params)]
        exact slice.lowIndividualDegree oldCoord
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
            (MvPolynomial.rename (embedCoord params) slice.poly :
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
