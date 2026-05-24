import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Basic.SubMeasurementCore
import MIPStarRE.Quantum.Measurement

/-!
# Section 5 — Making measurements projective: definitions

Definitions for Naimark dilation and orthonormalization, matching
Section 5 of `references/ldt-paper/orthonormalization.tex` and
Chapter 4 of the blueprint (`blueprint/src/chapter/ch04_projective.tex`).

## Naimark dilation structure

The key mathematical content is the **Naimark dilation theorem**: given
submeasurements on a bipartite space, there exist auxiliary registers and
projective measurements on the enlarged space that preserve all correlations
exactly.

### One-measurement Naimark (Lemma 5.2)

The building block is the one-measurement Naimark lemma. Given a
submeasurement `{M_a}_{a ∈ α}` on `Op d`, it produces a projective
submeasurement on the enlarged space `Op (d × Option α)`. The auxiliary
register has dimension `|α| + 1`, with the extra dimension absorbing the
"missing mass" `I − ∑ M_a`. The construction uses the isometry
`V|ψ⟩ = ∑_a √M_a |ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩` and defines
`P̂_a = V† (I ⊗ |a⟩⟨a|) V`.

### Questionwise Naimark data

For a prospective full bipartite assembly, one-measurement Naimark is applied
independently to each question on each side.  The current formal interface
records these questionwise local data and their marginal preservation
identities, not the full tensor-product correlation theorem.

## Matrix-level witnesses

Concrete `Matrix d d ℂ` witnesses are provided alongside the abstract
operator-algebra formulation, giving honest probability and overlap formulas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Finite Hilbert space infrastructure -/

/-- A finite-dimensional Hilbert space represented by a finite index type. -/
structure FiniteHilbertSpace where
  carrier : Type*
  instFintype : Fintype carrier
  instDecidableEq : DecidableEq carrier
  instNonempty : Nonempty carrier

attribute [instance] FiniteHilbertSpace.instFintype
attribute [instance] FiniteHilbertSpace.instDecidableEq
attribute [instance] FiniteHilbertSpace.instNonempty

/-- Concrete operators on a finite Hilbert space. -/
abbrev MatrixOperator (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Op H.carrier

/-- A positive operator used as a possibly unnormalized state witness. -/
structure PositiveMatrixState (H : FiniteHilbertSpace) where
  matrix : MatrixOperator H
  positive : 0 ≤ matrix

/-- Concrete submeasurements on a finite Hilbert space. -/
abbrev MatrixSubmeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Submeasurement Outcome H.carrier

/-- Concrete measurements on a finite Hilbert space. -/
abbrev MatrixMeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Measurement Outcome H.carrier

/-- The concrete expectation `τ(ρ X)` on the local matrix layer. -/
noncomputable def matrixExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X : MatrixOperator H) : ℂ :=
  MIPStarRE.Quantum.normalizedTrace (ρ.matrix * X)

/-! ### One-measurement Naimark dilation (Lemma 5.2)

The one-measurement Naimark dilation is the building block for the full
theorem. Given a submeasurement `M` on space `d`, it produces a projective
submeasurement on the enlarged space `d × Option α`, where `Option α`
models the auxiliary register with one extra dimension `none = ⊥` for the
missing mass `I − ∑ M_a`. -/

/-- The auxiliary pure-state projector `|⊥⟩⟨⊥|` on `Option α`, where `⊥ = none`.
This is the initial state of the auxiliary register before the Naimark
isometry is applied. -/
def naimarkAuxProjector (α : Type*) [Fintype α] [DecidableEq α] :
    MIPStarRE.Quantum.Op (Option α) :=
  Matrix.single none none 1

/-- The lifted density matrix for one-measurement Naimark dilation:
`ρ_lifted = |Option α| · (ρ ⊗ |⊥⟩⟨⊥|)`.
The scaling by `|Option α|` ensures the normalized trace is preserved:
`τ'(ρ_lifted) = τ(ρ)`, where `τ'` is the normalized trace on the enlarged space. -/
noncomputable def oneMeasLiftedDensity {d : Type*} [Fintype d] [DecidableEq d]
    (α : Type*) [Fintype α] [DecidableEq α]
    (ρ : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.Op (d × Option α) :=
  (Fintype.card (Option α) : ℂ) • Matrix.kronecker ρ (naimarkAuxProjector α)

/-- One-measurement Naimark dilation data at the matrix level.

Given a submeasurement `M : Submeasurement α d`, this witnesses the existence
of a projective submeasurement on the enlarged space `d × Option α` that
preserves all expectation values. This is Lemma 5.2 of the paper.

The construction: let `V : H → H ⊗ ℂ^{|α|+1}` be the isometry
`V|ψ⟩ = ∑_a √M_a |ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩`.
Then `P̂_a = V† (I ⊗ |a⟩⟨a|) V` is a projection, and
`⟨ψ|M_a|ψ⟩ = ⟨ψ⊗⊥|P̂_a|ψ⊗⊥⟩`. -/
structure OneMeasNaimarkData (α : Type*) [Fintype α] [DecidableEq α]
    (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The source submeasurement being dilated. -/
  source : MIPStarRE.Quantum.Submeasurement α d
  /-- The dilated projective effects on `d × Option α`.
  For outcome `some a`, this is the Naimark projector `P̂_a`.
  For outcome `none`, this is the projector for the "missing mass". -/
  liftedEffect : Option α → MIPStarRE.Quantum.Op (d × Option α)
  /-- Each lifted effect is a genuine orthogonal projection. Positivity follows
  from `MIPStarRE.Quantum.IsProj.nonneg`. -/
  lifted_isProj : ∀ a, MIPStarRE.Quantum.IsProj (liftedEffect a)
  /-- The lifted projections sum to at most identity (which together with
  `lifted_isProj` implies mutual orthogonality). -/
  lifted_sum_le_one : ∑ a, liftedEffect a ≤ 1
  /-- **Expectation preservation**: for any operator `ρ` on `Op d`,
  the expectation of outcome `a` under the original submeasurement equals
  the expectation under the dilated projective submeasurement with the
  Naimark-lifted state. The identity is linear, so it holds for all operators,
  not just density matrices. This is the core content of the dilation. -/
  expectation_preservation : ∀ (ρ : MIPStarRE.Quantum.Op d) (a : α),
    MIPStarRE.Quantum.normalizedTrace (ρ * source.effect a) =
      MIPStarRE.Quantum.normalizedTrace
        (oneMeasLiftedDensity α ρ * liftedEffect (some a))

/-- Positivity of a lifted Naimark effect, derived from its projectivity.

Lean-only consequence of the one-measurement Naimark data: the paper records
the lifted effects as projections, and positivity is supplied here by the
Mathlib star-projection order theorem through `MIPStarRE.Quantum.IsProj.nonneg`. -/
theorem OneMeasNaimarkData.lifted_pos {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) (a : Option α) :
    0 ≤ data.liftedEffect a :=
  MIPStarRE.Quantum.IsProj.nonneg (data.liftedEffect a) (data.lifted_isProj a)

/-! ### Questionwise Naimark data

The current Lean data applies one-measurement Naimark independently to each
question on each side. -/

/-- Questionwise Naimark data for the prospective full assembly.

Given submeasurements on space `ι`, this carries the questionwise
one-measurement Naimark dilations used as the local building blocks for the
full tensor-product assembly. -/
structure NaimarkData (QuestionA OutcomeA QuestionB OutcomeB : Type*)
    (ι : Type*)
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι] where
  /-- Alice's questionwise one-measurement Naimark dilations. -/
  left : (x : QuestionA) → OneMeasNaimarkData OutcomeA ι
  /-- Bob's questionwise one-measurement Naimark dilations. -/
  right : (y : QuestionB) → OneMeasNaimarkData OutcomeB ι

-- NOTE: no global `Inhabited` instance for `NaimarkData`:
-- constructing defaults for projective measurements is mathematically non-canonical
-- and would require additional assumptions on outcome types.

/-! ### Error functions for orthonormalization -/

/-- The explicit error in `thm:orthonormalization`. -/
noncomputable def orthonormalizationError (ζ : Error) : Error :=
  100 * Real.rpow ζ (1 / (4 : Error))

/-- Error bound of the direct completion-route orthonormalization theorem.

The paper proves the sharper `orthonormalizationError ζ`.  The direct completion
route first converts the completed measurement's `2ζ` self-consistency estimate
into a `4ζ` source-almost-projective estimate, and therefore uses this weaker
named envelope. -/
noncomputable def orthonormalizationCompletionRouteError (ζ : Error) : Error :=
  120 * Real.rpow ζ (1 / (4 : Error))

/-- The explicit error in the measurement version of the lemma. -/
noncomputable def orthonormalizationMainLemmaError (ζ : Error) : Error :=
  84 * Real.rpow ζ (1 / (4 : Error))

/-- The almost-projective error extracted from a consistency hypothesis. -/
def consistencyToAlmostProjectiveError (ζ : Error) : Error :=
  2 * ζ

/-- The spectral-truncation error when rounding one almost-projective effect to a
    projection via eigenvalue truncation. Dominated by `√ζ`. -/
noncomputable def spectralTruncationError (ζ : Error) : Error :=
  Real.rpow ζ (1 / (2 : Error))

/-- The rounding error when converting an almost-projective POVM to a projective submeasurement. -/
noncomputable def roundingToProjectiveError (ζ : Error) : Error :=
  12 * Real.rpow ζ (1 / (2 : Error))

end MIPStarRE.LDT.MakingMeasurementsProjective
