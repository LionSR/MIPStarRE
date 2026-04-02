import MIPStarRE.LDT.Commutativity.Theorems
set_option linter.style.longLine false

/-!
Matching scaffold for Section 12 of the low individual degree paper in
`references/ldt-paper/ld-pasting.tex`.

This file contains the core definitions, type abbreviations, utility operators, tuple
helpers, interpolation, and basic `\widehat G` / part-family constructors used
throughout the Section 12 pasting scaffold.  The displayed error formulas and
statement structures live in `Pasting/Statements.lean`.
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

/-- Placeholder outcome type for the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) := Option (Polynomial params)
abbrev SliceQuestion (params : Parameters) := Fq params
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params
abbrev GHatTupleOutcome (params : Parameters) (k : ℕ) := Fin k → GHatOutcome params
abbrev GHatType (k : ℕ) := Fin k → Bool
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) := Point params × PointTuple params k
abbrev VerticalLineQuestion (params : Parameters) := Point params

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
    SubMeas α ι where
  outcome := fun a => A.outcome a * B.total
  total := A.total * B.total
  outcome_pos := by
    intro a
    /-
    This is false for arbitrary submeasurements without an extra commutativity
    hypothesis. Even when `0 ≤ A.outcome a` and `0 ≤ B.total`, the product
    `A.outcome a * B.total` need not be Hermitian, hence need not be PSD.
    For example in dimension `2`, take
      X = [[1, 0], [0, 0]]
      Y = (1 / 2) * [[1, 1], [1, 1]];
    then `0 ≤ X`, `0 ≤ Y`, but `X * Y = (1 / 2) * [[1, 1], [0, 0]]` is not
    Hermitian.
    -/
    sorry
  sum_eq_total := by
    calc
      ∑ a, A.outcome a * B.total = (∑ a, A.outcome a) * B.total := by
        simpa using (Finset.sum_mul Finset.univ (fun a => A.outcome a) B.total).symm
      _ = A.total * B.total := by rw [A.sum_eq_total]
  total_le_one := by
    /-
    This is also false without commutativity. From `A.total ≤ 1` and
    `B.total ≤ 1` we cannot conclude `A.total * B.total ≤ 1` in the Loewner
    order unless the factors commute (or one has a stronger structural
    relation, such as a sandwich form). The same `2 x 2` example above shows
    that the product of two PSD contractions need not even be Hermitian.
    -/
    sorry

/-- Multiply each outcome operator by a total operator on the left. -/
noncomputable def multiplyByTotalOnLeft {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas β ι where
  outcome := fun b => A.total * B.outcome b
  total := A.total * B.total
  outcome_pos := by
    intro b
    /-
    This has the same obstruction as `multiplyByTotalOnRight.outcome_pos`:
    the product of two PSD operators need not be PSD without commutativity.
    In general `A.total * B.outcome b` need not even be Hermitian.
    -/
    sorry
  sum_eq_total := by
    calc
      ∑ b, A.total * B.outcome b = A.total * ∑ b, B.outcome b := by
        simpa using (Finset.mul_sum Finset.univ (fun b => B.outcome b) A.total).symm
      _ = A.total * B.total := by rw [B.sum_eq_total]
  total_le_one := by
    /-
    As above, `A.total ≤ 1` and `B.total ≤ 1` do not imply
    `A.total * B.total ≤ 1` for arbitrary PSD contractions. A commutativity
    hypothesis is needed to use the standard product bound.
    -/
    sorry

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
    (gs : GHatTupleOutcome params k) : GHatType k :=
  fun i => Option.isSome (gs i)

/-- Remove the first coordinate from a tuple of slice questions. -/
def pointTupleTail {params : Parameters} {k : ℕ}
    (xs : PointTuple params (k + 1)) : PointTuple params k :=
  fun i => xs i.succ

/-- Remove the first coordinate from a tuple of completed slice outcomes. -/
def gHatTupleOutcomeTail {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params (k + 1)) : GHatTupleOutcome params k :=
  fun i => gs i.succ

/-- Fallback global polynomial used when all completed slice outcomes are `⊥`.
Uses the zero polynomial (trivially low individual degree). -/
noncomputable def fallbackInterpolatedPolynomial (params : Parameters) : Polynomial params.next where
  poly := 0
  lowIndividualDegree := by
    intro i
    simp [MvPolynomial.degreeOf_zero]

/-- Count how many completed slice outcomes are genuine (non-`⊥`) polynomial slices. -/
noncomputable def nonBottomSliceCount {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params k) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => Option.isSome (gs i)).card

/-- The set of genuine (non-⊥) slice indices. -/
noncomputable def genuineSliceIndices {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params k) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i => (gs i).isSome

/-- Extract the polynomial from a genuine slice outcome. -/
noncomputable def extractSlicePoly {params : Parameters} {k : ℕ}
    (gs : GHatTupleOutcome params k) (i : Fin k)
    (hi : i ∈ genuineSliceIndices gs) : Polynomial params := by
  classical
  exact (gs i).get (by
    simp only [genuineSliceIndices, Finset.mem_filter] at hi
    exact hi.2)

/-- Extract the polynomial from a genuine (Some) slice outcome, or fallback to zero. -/
noncomputable def extractSliceOr0 {params : Parameters}
    (g : GHatOutcome params) : PolynomialModel params :=
  match g with
  | some p => p.poly
  | none => 0

/-- Interpolate from `d+1` or more genuine slice polynomials to recover
a polynomial in `m+1` variables. Uses a weighted sum of lifted slice polynomials,
with Lagrange-style coefficients determined by the evaluation heights.

The interpolated polynomial `h(u₁,...,uₘ,x) = ∑ᵢ Lᵢ(x) · gᵢ(u₁,...,uₘ)` where
`Lᵢ` is the Lagrange basis polynomial at height `xᵢ`, and `gᵢ` is the slice
polynomial at that height lifted to the ambient `(m+1)`-variable space.

When fewer than `d+1` genuine slices are available, returns the zero polynomial. -/
noncomputable def interpolateCompletedSlices (params : Parameters) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | k + 1, xs, gs => by
      classical
      exact if params.d + 1 ≤ nonBottomSliceCount gs then
        -- Genuine slice indices
        let τ := genuineSliceIndices gs
        -- Evaluation points in the scalar field
        let v : Fin (k + 1) → Scalar params := fun i => decodeScalar (xs i)
        -- The interpolated polynomial: ∑_{i ∈ τ} L_i(X_m) · g_i(u₁,...,u_m)
        -- where L_i is the Lagrange basis polynomial for height x_i
        -- and g_i is the slice polynomial lifted to (m+1) variables.
        { poly := ∑ i ∈ τ,
            -- Lift slice poly to (m+1) variables by renaming coords 0..m-1 ↦ 0..m-1
            let slicePoly := MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))
            -- Multiply by the Lagrange basis coefficient for height xᵢ
            -- Note: honest Lagrange interpolation requires Field (ZMod q), which
            -- holds only for prime q. For prime-power q, use GaloisField via
            -- PrimePowerFieldSpec. For now, use Lagrange basis coefficient = 1
            -- as a structural placeholder; the degree bound is sorry'd regardless.
            slicePoly
          lowIndividualDegree := sorry }
      else
        fallbackInterpolatedPolynomial params

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters)
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
      have hnonneg : 0 ≤ (completePartSubMeas params family x).total := by
        rw [← (completePartSubMeas params family x).sum_eq_total]
        exact Finset.sum_nonneg fun _ _ =>
          (completePartSubMeas params family x).outcome_pos ()
      exact sub_le_self _ hnonneg }

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- The submeasurement view of the completed family `\widehat G`. -/
noncomputable def gHatIdxSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Fq params) (GHatOutcome params) ι :=
  IdxMeas.toIdxSubMeas (gHatIdxMeas params family)

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)

end MIPStarRE.LDT.Pasting
