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

noncomputable section

/-- The set of `k`-tuples with distinct coordinates. -/
def distinctTuples (params : Parameters) (k : ℕ) : Set (PointTuple params k) :=
  { xs | Function.Injective xs }

/-- TODO: Should be uniform on pairwise-distinct `k`-tuples from `Fq`; currently a named placeholder. -/
def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) where
  name := s!"Distinct({params.q},{k})"

/-- Placeholder outcome type for the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) := Option (Polynomial params)
abbrev SliceQuestion (params : Parameters) := Fq params
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params
abbrev GHatTupleOutcome (params : Parameters) (k : ℕ) := Fin k → GHatOutcome params
abbrev GHatType (k : ℕ) := Fin k → Bool
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) := Point params × PointTuple params k
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- TODO: this should be the operator-polynomial tail construction from `lem:chernoff-bernoulli-matrix`. -/
def bernoulliTailOperator {d : ℕ} (k degree : ℕ) (X : Operator d) : Operator d where
  name := s!"BernoulliTail(k={k},d={degree}; {X.name}^r (I-{X.name})^(k-r))"

/-- Add a descriptive tag to a paper-local submeasurement placeholder. -/
def tagSubMeas {α : Type*} (tag : String) (A : SubMeas α d) : SubMeas α d where
  name := s!"{A.name}.{tag}"
  outcomeOperator := A.outcomeOperator
  totalOperator := A.totalOperator

/-- Multiply each outcome operator by a total operator on the right. -/
def multiplyByTotalOnRight {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas α d where
  name := label
  outcomeOperator := fun a => opMul (A.outcomeOperator a) B.totalOperator
  totalOperator := opMul A.totalOperator B.totalOperator

/-- Multiply each outcome operator by a total operator on the left. -/
def multiplyByTotalOnLeft {α β : Type*}
    (label : String) (A : SubMeas α d) (B : SubMeas β d) :
    SubMeas β d where
  name := label
  outcomeOperator := fun b => opMul A.totalOperator (B.outcomeOperator b)
  totalOperator := opMul A.totalOperator B.totalOperator

/-- Average an indexed family against a named distribution. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*}
    (label : String) (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome d) :
    SubMeas Outcome d where
  name := label
  outcomeOperator := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcomeOperator a)
  totalOperator := averageOperatorOverDistribution 𝒟 (fun q => (A q).totalOperator)

/-- Complement operator `I - X` in the same ambient space as `X`. -/
def operatorComplement (X : Operator d) : Operator d :=
  opDiff (identityLike X) X

/-- Regard an operator expression as a `Unit`-valued submeasurement placeholder. -/
def operatorAsSubMeas (X : Operator d) : SubMeas Unit d :=
  { name := s!"operator({X.name})"
    outcomeOperator := fun _ => X
    totalOperator := X }

/-- Regard the Bernoulli tail operator as a `Unit`-valued submeasurement placeholder. -/
def bernoulliTailSubMeas {d : ℕ} (k degree : ℕ) (X : Operator d) : SubMeas Unit d :=
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

/-- Fallback global polynomial used when all completed slice outcomes are `⊥`. -/
noncomputable def fallbackInterpolatedPolynomial (params : Parameters) : Polynomial params.next where
  poly := MvPolynomial.X ⟨params.m, Nat.lt_succ_self params.m⟩
  lowIndividualDegree := by
    intro i
    sorry

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
    (family : IdxPolyFamily params d) (x : Fq params) : SubMeas Unit d :=
  tagSubMeas "complete"
    (postprocess ((family.meas x).toSubMeas) (fun _ => ()))

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
def incompletePartSubMeas (params : Parameters)
    (family : IdxPolyFamily params d) (x : Fq params) : SubMeas Unit d :=
  operatorAsSubMeas (operatorComplement (completePartSubMeas params family x).totalOperator)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
def gHatIdxMeas (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxMeas (Fq params) (GHatOutcome params) d :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- The submeasurement view of the completed family `\widehat G`. -/
def gHatIdxSubMeas (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (Fq params) (GHatOutcome params) d :=
  IdxMeas.toIdxSubMeas (gHatIdxMeas params family)

/-- Left tensor-placement for the complete part `G^x`. -/
def completePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) Unit d :=
  fun x => leftPlacedSubMeas (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`. -/
def completePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) Unit d :=
  fun x => rightPlacedSubMeas (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`. -/
def incompletePartLeftFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) Unit d :=
  fun x => leftPlacedSubMeas (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`. -/
def incompletePartRightFamily (params : Parameters)
    (family : IdxPolyFamily params d) :
    IdxSubMeas (SliceQuestion params) Unit d :=
  fun x => rightPlacedSubMeas (incompletePartSubMeas params family x)


end

end MIPStarRE.LDT.Pasting
