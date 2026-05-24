import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Basic.OpFamily
import Mathlib.LinearAlgebra.Lagrange

/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
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

/-- The Bernoulli-tail polynomial commutes with left tensor placement. -/
theorem bernoulliTailOperator_leftTensor (A : MIPStarRE.Quantum.Op ι)
    (k degree : ℕ) :
    bernoulliTailOperator k degree (leftTensor (ι₂ := ι) A) =
      leftTensor (ι₂ := ι) (bernoulliTailOperator k degree A) := by
  unfold bernoulliTailOperator
  rw [← leftTensor_finset_sum (ι₂ := ι) (Finset.Icc (degree + 1) k)
    (fun r => (Nat.choose k r : ℂ) • (A ^ r * (1 - A) ^ (k - r)))]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [leftTensor_pow]
  rw [show (1 : MIPStarRE.Quantum.Op (ι × ι)) - leftTensor (ι₂ := ι) A =
      leftTensor (ι₂ := ι) (1 - A) by
        rw [← leftTensor_one (ι₁ := ι) (ι₂ := ι), leftTensor_sub]]
  rw [leftTensor_pow, leftTensor_mul_leftTensor]
  exact leftTensor_smul (ι₁ := ι) (ι₂ := ι) (Nat.choose k r : ℂ)
    (A ^ r * (1 - A) ^ (k - r))

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

/-- Record which completed-slice outcomes are genuine polynomial outcomes. -/
def gHatTupleType {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : GHatType k :=
  fun i => Option.isSome (gs i)

/-- The support of a completed-slice tuple, i.e. the indices whose outcomes are
genuine polynomials rather than `⊥`. This matches the paper's support of the type
`τ ∈ {0,1}^k`. -/
def gHatTupleSupport {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Finset (Fin k) :=
  Finset.univ.filter fun i => (gs i).isSome

/-- The Hamming weight of a completed-slice tuple. -/
def gHatTupleHammingWeight {params : Parameters} {k : ℕ}
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

end MIPStarRE.LDT.Pasting
