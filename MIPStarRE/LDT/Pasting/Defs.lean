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

noncomputable section

/-- The set of `k`-tuples with distinct coordinates. -/
def distinctTuples (params : Parameters) (k : ℕ) : Set (PointTuple params k) :=
  { xs | Function.Injective xs }

/-- TODO: Should be uniform on pairwise-distinct `k`-tuples from `Fq`; currently a named placeholder. -/
def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) where

/-- Placeholder outcome type for the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) := Option (Polynomial params)
abbrev SliceQuestion (params : Parameters) := Fq params
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params
abbrev GHatTupleOutcome (params : Parameters) (k : ℕ) := Fin k → GHatOutcome params
abbrev GHatType (k : ℕ) := Fin k → Bool
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) := Point params × PointTuple params k
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- TODO: this should be the operator-polynomial tail construction from `lem:chernoff-bernoulli-matrix`. -/
def bernoulliTailOperator (k _degree : ℕ) (X : MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  X ^ k  -- placeholder

/-- Multiply each outcome operator by a total operator on the right. -/
def multiplyByTotalOnRight {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas α ι where
  outcome := fun a => A.outcome a * B.total
  total := A.total * B.total

/-- Multiply each outcome operator by a total operator on the left. -/
def multiplyByTotalOnLeft {α β : Type*}
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas β ι where
  outcome := fun b => A.total * B.outcome b
  total := A.total * B.total

/-- Average an indexed family against a named distribution. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*}
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome ι) :
    SubMeas Outcome ι where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total := averageOperatorOverDistribution 𝒟 (fun q => (A q).total)

/-- Complement operator `I - X` in the same ambient space as `X`. -/
def operatorComplement (X : MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  1 - X

/-- Regard an operator expression as a `Unit`-valued submeasurement placeholder. -/
def operatorAsSubMeas (X : MIPStarRE.Quantum.Op ι) : SubMeas Unit ι :=
  { outcome := fun _ => X
    total := X }

/-- Regard the Bernoulli tail operator as a `Unit`-valued submeasurement placeholder. -/
def bernoulliTailSubMeas (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) : SubMeas Unit ι :=
  operatorAsSubMeas (bernoulliTailOperator k degree X)

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

/-- TODO: paper defines `H_h` by interpolating from available slices once `|τ| ≥ d+1`.
This scaffold now enforces the `|τ| ≥ d+1` threshold before interpolation, but still
uses a first-available slice stand-in instead of the honest interpolation formula. -/
noncomputable def interpolateCompletedSlices (params : Parameters) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | k + 1, xs, gs =>
      if params.d + 1 ≤ nonBottomSliceCount gs then
        match gs 0 with
        | some g => Polynomial.appendAtHeight params g (xs 0)
        | none => interpolateCompletedSlices params k (pointTupleTail xs) (gHatTupleOutcomeTail gs)
      else
        fallbackInterpolatedPolynomial params

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
def completePartSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
def incompletePartSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  operatorAsSubMeas (operatorComplement (completePartSubMeas params family x).total)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
def gHatIdxMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- The submeasurement view of the completed family `\widehat G`. -/
def gHatIdxSubMeas (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Fq params) (GHatOutcome params) ι :=
  IdxMeas.toIdxSubMeas (gHatIdxMeas params family)

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
def completePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
def completePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
def incompletePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
def incompletePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)


end

end MIPStarRE.LDT.Pasting
