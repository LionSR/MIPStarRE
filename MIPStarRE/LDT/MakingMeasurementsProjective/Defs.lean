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

### Full Naimark dilation (Theorem 5.1)

For the full bipartite setting, one-measurement Naimark is applied
independently to each question on each side. The lifted index type is
`ι × (QuestionA → Option OutcomeA) × (QuestionB → Option OutcomeB)`,
reflecting the tensor product of per-question auxiliary registers.

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

/-- A normalized density operator. -/
structure DensityMatrixState (H : FiniteHilbertSpace)
    extends PositiveMatrixState H where
  normalized : MIPStarRE.Quantum.normalizedTrace matrix = 1

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

/-- The concrete single-outcome probability `τ(ρ A_a)`. -/
noncomputable def matrixSingleOutcomeProbability {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement Outcome H) (a : Outcome) : ℂ :=
  matrixExpectation ρ (A.effect a)

/-- The concrete joint outcome probability `τ(ρ A_a B_b)` on one ambient algebra. -/
noncomputable def matrixJointOutcomeProbability {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement OutcomeA H)
    (B : MatrixSubmeasurement OutcomeB H)
    (a : OutcomeA) (b : OutcomeB) : ℂ :=
  matrixExpectation ρ (A.effect a * B.effect b)

/-- The concrete squared `τ`-distance between two effects. -/
noncomputable def matrixOutcomeTauDistance {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A B : MatrixSubmeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a - B.effect a))

/-- The concrete idempotence defect `‖A_a^2 - A_a‖_τ^2`. -/
noncomputable def matrixIdempotenceDefect {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A : MatrixMeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a * A.effect a - A.effect a))

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
  /-- Each lifted effect is a genuine orthogonal projection. -/
  lifted_isProj : ∀ a, MIPStarRE.Quantum.IsProj (liftedEffect a)
  /-- Each lifted effect is positive semidefinite, so the family forms a submeasurement.
  Note: this is mathematically redundant with `lifted_isProj` (projections are PSD),
  but kept as a convenience field for downstream `Submeasurement` packaging until
  `IsProj.pos` is available in Mathlib. -/
  lifted_pos : ∀ a, 0 ≤ liftedEffect a
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

/-- Matrix-level witness for the Naimark dilation statement.

This carries separate `originalSpace` and `liftedSpace`, with the lifted
space being larger. The witness includes projective measurements on the
lifted space and the key probability preservation identities. -/
structure MatrixNaimarkWitness (QuestionA OutcomeA QuestionB OutcomeB : Type*)
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB] where
  originalSpace : FiniteHilbertSpace
  liftedSpace : FiniteHilbertSpace
  originalState : DensityMatrixState originalSpace
  liftedState : DensityMatrixState liftedSpace
  originalLeft : QuestionA → MatrixSubmeasurement OutcomeA originalSpace
  originalRight : QuestionB → MatrixSubmeasurement OutcomeB originalSpace
  liftedLeft : QuestionA → MatrixMeasurement OutcomeA liftedSpace
  liftedRight : QuestionB → MatrixMeasurement OutcomeB liftedSpace
  liftedLeftProjective :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      MIPStarRE.Quantum.IsProj ((liftedLeft x).effect a)
  liftedRightProjective :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      MIPStarRE.Quantum.IsProj ((liftedRight y).effect b)
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      matrixSingleOutcomeProbability originalState.toPositiveMatrixState (originalLeft x) a =
        matrixSingleOutcomeProbability liftedState.toPositiveMatrixState
          ((liftedLeft x).toSubmeasurement) a
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      matrixSingleOutcomeProbability originalState.toPositiveMatrixState (originalRight y) b =
        matrixSingleOutcomeProbability liftedState.toPositiveMatrixState
          ((liftedRight y).toSubmeasurement) b
  jointOutcomePreservation :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        matrixJointOutcomeProbability originalState.toPositiveMatrixState
          (originalLeft x) (originalRight y) a b =
          matrixJointOutcomeProbability liftedState.toPositiveMatrixState
            ((liftedLeft x).toSubmeasurement) ((liftedRight y).toSubmeasurement) a b

/-! ### Full Naimark dilation (Theorem 5.1)

The full Naimark dilation applies one-measurement Naimark independently
to each question on each side. The lifted index type is
`ι × (QuestionA → Option OutcomeA) × (QuestionB → Option OutcomeB)`. -/

/-- The lifted index type for Naimark dilation. For each question on each
side, an auxiliary register of dimension `|Outcome| + 1` is tensored in.
The type `QuestionA → Option OutcomeA` represents the tensor product
`⊗_x ℂ^{|OutcomeA|+1}` of per-question Alice auxiliaries, and similarly
for Bob. -/
-- Note: The `Fintype` instance for `QuestionA → Option OutcomeA` has cardinality
-- `(|OutcomeA| + 1)^|QuestionA|`, which grows exponentially. This is fine for the
-- abstract proofs but may cause performance issues with `decide`/`Finset.sum` when
-- filling in real proofs. See #98 for tracking.
abbrev NaimarkLiftedIndex (ι : Type*) (QuestionA OutcomeA QuestionB OutcomeB : Type*) :=
  ι × (QuestionA → Option OutcomeA) × (QuestionB → Option OutcomeB)

/-- Output data for the paper's Naimark dilation theorem.

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

/-! ### Abstract-level probability definitions -/

/-- The single-outcome probability `⟨ψ|A_a|ψ⟩`. -/
noncomputable def singleOutcomeProbability {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : SubMeas Outcome ι) (a : Outcome) : Error :=
  ev ψ (A.outcome a)

/-- The joint outcome probability `Tr(ρ · A_a · B_b)`.
Uses the operator product on the shared algebra, matching `matrixJointOutcomeProbability`.
When the measurements commute (as guaranteed after Naimark dilation), this
equals the tensor-product formulation `⟨ψ| (A_a ⊗ B_b) |ψ⟩`. -/
noncomputable def jointOutcomeProbability {OutcomeA OutcomeB : Type*}
    {ι : Type*} [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : SubMeas OutcomeA ι)
    (B : SubMeas OutcomeB ι)
    (a : OutcomeA) (b : OutcomeB) : Error :=
  ev ψ (A.outcome a * B.outcome b)

/-! ### Error functions for orthonormalization -/

/-- The explicit error in `thm:orthonormalization`. -/
noncomputable def orthonormalizationError (ζ : Error) : Error :=
  100 * Real.rpow ζ (1 / (4 : Error))

/-- The strong self-consistency error after completing a submeasurement to a measurement. -/
def orthonormalizationCompletionError (ζ : Error) : Error :=
  2 * ζ

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

/-! ### Almost-projective and rounding witnesses -/

/-- Matrix-level witness for the almost-projective stage. -/
structure MatrixAlmostProjectiveWitness {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ζ : Error) where
  space : FiniteHilbertSpace
  state : DensityMatrixState space
  measurement : MatrixMeasurement Outcome space
  overlapDecomposition :
    MIPStarRE.Quantum.inconsistency measurement.effect measurement.effect +
        MIPStarRE.Quantum.diagOverlap measurement.effect measurement.effect = 1
  pointwiseIdempotence :
    ∀ a : Outcome,
      matrixIdempotenceDefect measurement a ≤ ζ

/-- Matrix-level witness for the rounding-to-projective stage. -/
structure MatrixRoundedProjectiveWitness {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ζ : Error) where
  space : FiniteHilbertSpace
  state : DensityMatrixState space
  source : MatrixMeasurement Outcome space
  target : MatrixSubmeasurement Outcome space
  targetProjective :
    ∀ a : Outcome,
      MIPStarRE.Quantum.IsProj (target.effect a)
  pointwiseTauDistance :
    ∀ a : Outcome,
      matrixOutcomeTauDistance source.toSubmeasurement target a ≤ ζ

/-! ### Truncation witnesses -/

/-- Matrix-level witness for truncating a single effect to a projection.

This captures the passage from an almost-projective operator to a genuine projection
by truncating the spectrum at `1/2`. The key bound is that the τ-distance between
the source and target is controlled by the idempotence defect of the source. -/
structure MatrixSpectralTruncationWitness {d : Type*}
    [Fintype d] [DecidableEq d] where
  source : MIPStarRE.Quantum.Op d
  target : MIPStarRE.Quantum.Op d
  truncation : MIPStarRE.Quantum.SpectralTruncation source target

/-- Matrix-level witness for rounding every effect of a measurement to a projection.

Each effect `A_a` is independently spectrally truncated to a projection `P_a`.
The resulting family is not necessarily a measurement (the projections may not sum
to the identity), but the τ-distance per outcome is controlled. -/
structure MatrixSpectralTruncationMeasurementWitness {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome] (ζ : Error) where
  space : FiniteHilbertSpace
  source : MatrixMeasurement Outcome space
  target : Outcome → MIPStarRE.Quantum.Op space.carrier
  perOutcomeTruncation :
    ∀ a : Outcome,
      MIPStarRE.Quantum.SpectralTruncation (source.effect a) (target a)
  perOutcomeProjective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (target a)

end MIPStarRE.LDT.MakingMeasurementsProjective
