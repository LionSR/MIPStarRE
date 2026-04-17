import MIPStarRE.LDT.Commutativity.Theorems
import Mathlib.LinearAlgebra.Lagrange

/-!
# Section 12 — Definitions

This file contains the core definitions, type abbreviations, utility operators, tuple
helpers, interpolation, and basic `\widehat G` / part-family constructors used
throughout the Section 12 pasting scaffold.  The displayed error formulas and
statement structures live in `Pasting/Statements.lean`.

## References

- `references/ldt-paper/ld-pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of `k`-tuples with distinct coordinates. -/
def distinctTuples (params : Parameters) (k : ℕ) : Set (PointTuple params k) :=
  { xs | Function.Injective xs }

/-- Uniform distribution on pairwise-distinct `k`-tuples from `Fq`.
Support is the set of injective functions `Fin k → Fq params`;
weight is uniform `1 / |support|` on support, `0` outside. -/
noncomputable def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) := by
  classical
  let support := Finset.univ.filter (fun xs : PointTuple params k => Function.Injective xs)
  exact {
    support := support
    weight := fun xs =>
      if xs ∈ support then 1 / (support.card : Error) else 0
    nonnegative := by intro xs; split_ifs <;> positivity
    outsideSupport := by intro xs hxs; simp_all
  }

/-- The distinct-tuple distribution has total mass at most `1`. -/
theorem distinctTupleDistribution_weight_sum_le_one (params : Parameters) (k : ℕ) :
    ∑ xs ∈ (distinctTupleDistribution params k).support,
      (distinctTupleDistribution params k).weight xs ≤ 1 := by
  classical
  let support := Finset.univ.filter (fun xs : PointTuple params k => Function.Injective xs)
  have hsupport :
      (distinctTupleDistribution params k).support = support := by
    simp [distinctTupleDistribution, support]
  have hweight :
      ∀ xs, (distinctTupleDistribution params k).weight xs =
        if xs ∈ support then 1 / (support.card : Error) else 0 := by
    intro xs
    simp [distinctTupleDistribution, support]
  rw [hsupport]
  simp_rw [hweight]
  by_cases hs : support.Nonempty
  · have hcard_nat : support.card ≠ 0 := Finset.card_ne_zero.mpr hs
    have hcard : (support.card : Error) ≠ 0 := by
      exact_mod_cast hcard_nat
    have hsum :
        (∑ xs ∈ support, if xs ∈ support then 1 / (support.card : Error) else 0) =
          ∑ xs ∈ support, 1 / (support.card : Error) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      simp [hxs]
    rw [hsum]
    simp [Finset.sum_const, hcard]
  · have hempty : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

/-- The outcome type of the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) [FieldModel params.q] := Option (Polynomial params)

/-- The question type for a single slice height. -/
abbrev SliceQuestion (params : Parameters) := Fq params

/-- The question type for an ordered pair of slice heights. -/
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params

/-- The outcome type of a `k`-tuple of completed-slice answers. -/
abbrev GHatTupleOutcome (params : Parameters) [FieldModel params.q] (k : ℕ) :=
  Fin k → GHatOutcome params

/-- A Boolean type pattern for a completed-slice tuple. -/
abbrev GHatType (k : ℕ) := Fin k → Bool

/-- A sandwiched-line question consists of a point and a `k`-tuple of slice heights. -/
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) :=
  Point params × PointTuple params k

/-- The question type for vertical lines, identified with their base point. -/
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- The Hamming weight `|τ|` of a type `τ ∈ {0,1}^k`. -/
def gHatTypeWeight {k : ℕ} (τ : GHatType k) : ℕ :=
  (Finset.univ.filter fun i => τ i).card

/-- Prepend one type bit to a tail type. -/
def prependTypeBit {k : ℕ} (b : Bool) (τ : GHatType k) : GHatType (k + 1)
  | ⟨0, _⟩ => b
  | ⟨n + 1, hn⟩ => τ ⟨n, Nat.lt_of_succ_lt_succ hn⟩

/-- Drop the first `prefixLen` bits of a type.

In the `fromHToG` recurrence the natural index is the number of prefix bits
already converted to the Bernoulli polynomial.  This helper turns a full
`k`-type into the remaining tail `τ_{≥ prefixLen}` using zero-based indexing.

Note: because `k - prefixLen` uses `Nat` subtraction, passing `prefixLen > k`
silently returns `GHatType 0` (the empty tuple) rather than being a type error.
Callers in the `fromHToG` recurrence always satisfy `prefixLen ≤ k`, so this
wraparound is never triggered; reviewers should treat `prefixLen ≤ k` as an
invariant of all call sites. -/
def gHatTypeSuffix {k : ℕ} (prefixLen : ℕ) (τ : GHatType k) : GHatType (k - prefixLen) :=
  fun i => τ ⟨prefixLen + i.val, by omega⟩

/-- The operator contribution of one type bit: `G` for `1`, `I - G` for `0`. -/
noncomputable def gHatTypeBitOperator (G : MIPStarRE.Quantum.Op ι) (bit : Bool) :
    MIPStarRE.Quantum.Op ι :=
  if bit then G else 1 - G

/-- The operator monomial associated with a type `τ`. -/
noncomputable def gHatTypeOperator (G : MIPStarRE.Quantum.Op ι) {k : ℕ}
    (τ : GHatType k) : MIPStarRE.Quantum.Op ι :=
  G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)

/-- `def:truncated-type-sums`.

Fixing a tail type `τ_tail`, this sums the source-style monomials contributed by
all prefixes whose total Hamming weight can still reach the interpolation
threshold `d + 1`. The parameter `prefixLen` is the paper's `ℓ - 1`. -/
noncomputable def truncatedTypeSums (G : MIPStarRE.Quantum.Op ι)
    (d prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    MIPStarRE.Quantum.Op ι :=
  ∑ τprefix : GHatType prefixLen,
    if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail then
      gHatTypeOperator G τprefix
    else 0

/-- The Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`:
`F(X) = ∑_{r=degree+1}^{k} C(k,r) · X^r · (I - X)^{k-r}`.
This is the matrix-valued Bernoulli tail probability. -/
noncomputable def bernoulliTailOperator (k degree : ℕ)
    (X : MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r))

/-- Multiply each outcome operator by a total operator on the right. -/
noncomputable def multiplyByTotalOnRight {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily α ι where
  outcome := fun a => A.outcome a * B.total
  total := A.total * B.total

/-- Multiply each outcome operator by a total operator on the left. -/
noncomputable def multiplyByTotalOnLeft {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily β ι where
  outcome := fun b => A.total * B.outcome b
  total := A.total * B.total

/-- Average an indexed family against a named distribution. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    SubMeas Outcome ι where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total := averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
  outcome_pos := by
    intro a
    exact Finset.sum_nonneg fun q _ => smul_nonneg (𝒟.nonnegative q) ((A q).outcome_pos a)
  sum_eq_total := by
    classical
    calc
      ∑ a, averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
          = ∑ q ∈ 𝒟.support, ∑ a, 𝒟.weight q • (A q).outcome a := by
              simp_rw [averageOperatorOverDistribution]
              rw [Finset.sum_comm]
      _ = ∑ q ∈ 𝒟.support, 𝒟.weight q • ∑ a, (A q).outcome a := by
            apply Finset.sum_congr rfl
            intro q _
            rw [← Finset.smul_sum]
      _ = ∑ q ∈ 𝒟.support, 𝒟.weight q • (A q).total := by
            apply Finset.sum_congr rfl
            intro q _
            rw [(A q).sum_eq_total]
      _ = averageOperatorOverDistribution 𝒟 (fun q => (A q).total) := by
            simp [averageOperatorOverDistribution]
  total_le_one := by
    calc
      averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
        ≤ ∑ q ∈ 𝒟.support, 𝒟.weight q • (1 : MIPStarRE.Quantum.Op ι) := by
            simp only [averageOperatorOverDistribution]
            exact Finset.sum_le_sum fun q _ =>
              smul_le_smul_of_nonneg_left (A q).total_le_one (𝒟.nonnegative q)
      _ = (∑ q ∈ 𝒟.support, 𝒟.weight q) • (1 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_smul]
      _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
            exact smul_le_smul_of_nonneg_right h𝒟 zero_le_one
      _ = 1 := by simp

/-- Record which completed-slice outcomes are genuine polynomial outcomes. -/
def gHatTupleType {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : GHatType k :=
  fun i => Option.isSome (gs i)

/-- The support of a completed-slice tuple, i.e. the indices whose outcomes are
genuine polynomials rather than `⊥`. This matches the paper's support of the type
`τ ∈ {0,1}^k`. -/
noncomputable def gHatTupleSupport {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Finset (Fin k) :=
  open Classical in
    Finset.univ.filter fun i => (gs i).isSome

/-- The Hamming weight of a completed-slice tuple. -/
noncomputable def gHatTupleHammingWeight {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : ℕ :=
  (gHatTupleSupport gs).card

/-- The set `\mathsf{Outcomes}_\tau` of completed-slice tuples whose `Some`/`none`
pattern is prescribed by the type `τ`. -/
def outcomesByType {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (τ : GHatType k) : Set (GHatTupleOutcome params k) :=
  { gs | ∀ i : Fin k, (gs i).isSome = τ i }

/-- A completed-slice tuple is eligible for interpolation exactly when its type has
Hamming weight at least `d + 1`, matching the paper's `|w| ≥ d+1` filter. -/
def InterpolationEligible (params : Parameters) {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Prop :=
  params.d + 1 ≤ gHatTupleHammingWeight gs

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

/-- A completed-slice tuple `gs` is globally consistent at evaluation
points `xs` if there exists a single polynomial `h` in `m+1` variables
whose restriction to each genuine slice height `xᵢ` agrees with the
corresponding slice polynomial `gᵢ`.

This matches the paper's `Global_τ(x)` predicate from
`references/ldt-paper/ld-pasting.tex` lines 1123-1131. -/
def IsGloballyConsistent (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : Prop :=
  ∃ h : Polynomial params.next,
    ∀ i : Fin k, ∀ (hi : (gs i).isSome = true),
      (Polynomial.restrictAtHeight params h (xs i)).poly =
        ((gs i).get hi).poly

/-- `IsGloballyConsistent params xs` is decidable (classically),
needed for `restrictSubMeas` filtering. -/
noncomputable instance isGloballyConsistent_decidablePred
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (xs : PointTuple params k) :
    DecidablePred (IsGloballyConsistent params xs) :=
  fun _gs => Classical.dec _

/-- The subset `\mathsf{Global}_\tau(x)` of `\mathsf{Outcomes}_\tau` consisting of
tuples that arise from restrictions of a single global polynomial at the slice
heights `xs`. -/
def globallyConsistentOutcomesByType (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (τ : GHatType k) :
    Set (GHatTupleOutcome params k) :=
  { gs | gs ∈ outcomesByType τ ∧ IsGloballyConsistent params xs gs }

/-- The complement `\overline{\mathsf{Global}_\tau(x)}` inside
`\mathsf{Outcomes}_\tau`. -/
def nonglobalOutcomesByType (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (τ : GHatType k) :
    Set (GHatTupleOutcome params k) :=
  outcomesByType τ \ globallyConsistentOutcomesByType params xs τ

/-- Recover a global polynomial from a completed-slice tuple.

On the actual pasting path this map is only applied after restricting to tuples in
`Global_τ(x)`, so it may choose any globally consistent witness. When no such
witness exists, it falls back to the distinguished zero polynomial. -/
noncomputable def interpolateCompletedSlices (params : Parameters) [FieldModel params.q] :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | k + 1, xs, gs => by
      classical
      exact if hEligible : InterpolationEligible params gs then
        let σ := interpolationSupportSubset gs hEligible
        interpolateCompletedSlicesFromSupport params xs gs σ
          (interpolationSupportSubset_card gs hEligible)
      else
        fallbackInterpolatedPolynomial params

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- The total operator of the complete part is the original slice total. -/
@[simp] theorem completePartSubMeas_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).total = (family.meas x).total := by
  simp [completePartSubMeas, postprocess_total]

/-- The unique outcome of the complete part equals its total operator. -/
@[simp] theorem completePartSubMeas_outcome_unit (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).outcome () =
      (completePartSubMeas params family x).total := by
  rw [← (completePartSubMeas params family x).sum_eq_total]
  simp [completePartSubMeas]

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  let X := 1 - (completePartSubMeas params family x).total
  { outcome := fun _ => X
    total := X
    outcome_pos := by
      intro _
      exact sub_nonneg.mpr (completePartSubMeas params family x).total_le_one
    sum_eq_total := by
      simp
    total_le_one := by
      exact sub_le_self _ (completePartSubMeas params family x).total_nonneg }

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- The submeasurement view of the completed family `\widehat G`. -/
noncomputable def gHatIdxSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Fq params) (GHatOutcome params) ι :=
  IdxMeas.toIdxSubMeas (gHatIdxMeas params family)

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)

end MIPStarRE.LDT.Pasting
