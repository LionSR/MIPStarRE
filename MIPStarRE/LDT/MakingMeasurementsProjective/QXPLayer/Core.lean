import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization

/-!
# Section 5 — Q/X/XHat/P core data

Core data structures and shared operator-family definitions for the paper's
`Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

/-- The quarter-root error term is nonnegative on nonnegative input. -/
lemma zetaQuarterRoot_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ zetaQuarterRoot ζ := by
  dsimp [zetaQuarterRoot]
  exact Real.rpow_nonneg hζ _

/-- A raw operator family viewed as a constant indexed family on the trivial
question set. -/
def constOpFamily {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : OpFamily Outcome ι) :
    IdxOpFamily Unit Outcome ι :=
  fun _ => A

/-- Data for the paper's intermediate `Q`-layer: the rank-reduced family
`Q_a`, its total operator `Q`, and the auxiliary projective measurement `T_a`
used to define `X_a`, `XHat_a`, and `P_a`. -/
structure QLayerData (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  auxSpace : FiniteHilbertSpace.{uι}
  q : OpFamily Outcome ι
  t : ProjMeas Outcome auxSpace.carrier

/-- The paper's operator `Q_a`. -/
def Qa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.q.outcome a

/-- The paper's total operator `Q = ∑_a Q_a`. -/
def QTotal {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) :
    MIPStarRE.Quantum.Op ι :=
  data.q.total

/-- The paper's auxiliary projector `T_a`. -/
def Ta {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op data.auxSpace.carrier :=
  data.t.outcome a

/-- Witness package for `lem:projective-non-measurement`. -/
structure RoundingToProjectorsWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (R : OpFamily Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (R.outcome a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily R)
      (2 * spectralTruncationError ζ)
  total_le :
    R.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Witness package for `lem:projective-low-rank-sum`. -/
structure RankReductionWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (data : QLayerData Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa data a)
  outcome_nonneg :
    ∀ a : Outcome, 0 ≤ Qa data a
  sum_eq_total :
    ∑ a, Qa data a = QTotal data
  source_almost_projective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily data.q)
      (roundingToProjectiveError ζ)
  total_le :
    QTotal data ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)
  auxDim_le :
    Fintype.card data.auxSpace.carrier ≤ Fintype.card ι

/-- Temporary bridge package for the paper's `lem:projective-non-measurement`
stage, which starts from the `2 * ζ` source-idempotence defect and directly
produces the rounded family `R_a` with the paper's `2 * sqrt ζ` closeness and
`(1 + 2 * sqrt ζ) I` total-mass bound. -/
structure ProjectiveNonMeasurementBridgePackage {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Prop where
  fromSourceAlmostProjective :
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) →
      ∃ R : OpFamily Outcome ι,
        RoundingToProjectorsWitness ψ A ζ R ∧
          ∑ a, R.outcome a = R.total

/-- Output of the auxiliary-space construction used inside
`lem:projective-low-rank-sum`: the paper's auxiliary Hilbert space `ℂ^m`
together with an auxiliary projective measurement `T_a` on it, and the
paper's rank bound `m ≤ d`.

The paper's intended construction (orthonormalization.tex Lem 5.5) takes
`T_a = ∑_i |a,i⟩⟨a,i|` on `ℂ^m` with `m = ∑_a rank(Q_a)`, i.e. the
indexed-slab diagonal form over the eigenvector basis of each rounded
projector `R_a`.  That diagonal/basis structure is *not* enforced as a
predicate here — it is the obligation of the concrete bridge instance.
Downstream proofs that rely on the diagonal action of `T_a` (e.g.
`xa_t`, `qaRestated`) will therefore require the bridge instance to also
expose that predicate, or to be refined with additional fields when the
supporting spectral lemmas land. -/
structure RankReductionAuxOutput (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  /-- Auxiliary Hilbert space (paper's `ℂ^m`). -/
  auxSpace : FiniteHilbertSpace.{uι}
  /-- Auxiliary projective measurement `T_a` on the auxiliary space.
  Intended to be the paper's diagonal/indexed-slab form, but the diagonal
  predicate is not part of this structure — see the structure-level
  docstring. -/
  t : ProjMeas Outcome auxSpace.carrier
  /-- Paper's rank bound `m ≤ d`. -/
  auxDim_le : Fintype.card auxSpace.carrier ≤ Fintype.card ι

/-- Temporary bridge package for the auxiliary-space-and-`T` construction in
the rank-reduction step (`lem:projective-low-rank-sum`, orthonormalization.tex
Lem 5.5).

Given a specific rounded projective family `q = R_a` on `ι` satisfying
`RoundingToProjectorsWitness ψ A ζ q` (so that its total stays bounded by
`(1 + 2√ζ)·I`), the paper's proof constructs an auxiliary Hilbert space
`ℂ^m` with `m = ∑_a rank(Q_a) ≤ d` and a projective measurement
`T_a = ∑_i |a,i⟩⟨a,i|` on it, used downstream in the `X/XHat/P` layer
construction.

The matrix-level spectral argument — eigenvector basis of each rounded
projector `R_a`, followed by the indexed-slab construction on
`Σ_a Fin (rank R_a)` — is isolated here as an opaque producer until the
supporting spectral lemmas (e.g. `Matrix.IsHermitian.eigenvectorBasis`
restricted to the 1-eigenspace of a projector, plus a matrix-level
`rank_of_isProj`) land in Mathlib or in the project.

This is the second Lean bridge scaffold in this chapter alongside the
earlier `ProjectiveNonMeasurementBridgePackage`.  Unlike that bridge, this
one is `Type`-valued (not `Prop`-valued) because `RankReductionAuxOutput`
carries data (`auxSpace`, `t`).  It is parametric on the *specific*
`(q, hq)` the consumer holds, so a future implementation that can only
build `(auxSpace, T_a)` for the selected rounded family suffices — no
universal quantification over all rounded families is required.  The
closest sibling abbrevs in `MakingMeasurementsProjective/Statements.lean`
are `SpectralTruncationStatement` (output-shaped, not a producer) and
`ProjectivizationRepairInput` (`Prop`-valued existential over the repaired
family), neither of which uses the `structure ... where fromX` form
employed here. -/
structure RankReductionBridgePackage {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (q : OpFamily Outcome ι)
    (hq : RoundingToProjectorsWitness ψ A ζ q) where
  /-- The paper's `(auxSpace, T_a)` construction output together with the
  `m ≤ d` rank bound for the specific rounded family `q`. -/
  out : RankReductionAuxOutput Outcome ι

/-- The raw operator family obtained by sandwiching the auxiliary projectors
`T_a` with a candidate `XHat`. This is the family later named `P`. -/
noncomputable def pFamilyFromXHat {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ) :
    OpFamily Outcome ι where
  outcome := fun a => xHatᴴ * Ta qLayer a * xHat
  total := ∑ a, xHatᴴ * Ta qLayer a * xHat

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.  The square matrices `u`, `v`, `sigmaLeft`,
and `sigmaRight` are placeholders for the SVD objects appearing in the paper's
formulas. -/
structure QXPLayerData (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  u : MatrixOperator qLayer.auxSpace
  v : MIPStarRE.Quantum.Op ι
  sigmaLeft : MatrixOperator qLayer.auxSpace
  sigmaRight : MIPStarRE.Quantum.Op ι
  qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x
  qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (qLayer.q.outcome a)
  xHat_coisometry : xHat * xHatᴴ = 1
  x_gram_right : xᴴ * x = QTotal qLayer
  x_gram_left_svd : x * xᴴ = u * (sigmaLeft * sigmaLeft) * uᴴ
  q_total_svd : QTotal qLayer = v * (sigmaRight * sigmaRight) * vᴴ
  xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)
  xHat_left_svd : x * xHatᴴ = u * sigmaLeft * uᴴ
  /-- We store the paper's final `P`-vs-`Q` estimate on the witness package so
  a chosen `X/XHat/P` decomposition carries its own comparison bound. The
  public interface remains `pQApprox`, which is the only place this field is
  projected out. -/
  pQApprox_bound :
    ∀ (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error),
      RankReductionWitness ψ A ζ qLayer →
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily qLayer.q)
          (constOpFamily (pFamilyFromXHat qLayer xHat))
          (30 * zetaQuarterRoot ζ)

/-- The paper's matrix `X_a = T_a · X`. -/
def Xa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.x

/-- The paper's matrix `XHat_a = T_a · XHat`. -/
def XHatA {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.xHat

/-- The paper's operator `P_a = XHat† · T_a · XHat`. -/
def Pa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.xHatᴴ * Ta data.qLayer a * data.xHat

/-- The raw operator family `P = {P_a}`. -/
noncomputable def PFamily {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι :=
  pFamilyFromXHat data.qLayer data.xHat

/-- Paper label `def:matrix-decomposition-Q`.

The Lean formalization stores the chosen decomposition data for `Q_a` in the
`QLayerData` package. -/
abbrev matrixDecompositionQ (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  QLayerData Outcome ι

/-- Paper label `def:svd-of-X`.

The singular-value-decomposition scaffolding for the `X/XHat/P` layer is stored
in `QXPLayerData`. -/
abbrev svdOfX (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  QXPLayerData Outcome ι

/-- Paper label `def:projective-P`.

The projective family `P = {P_a}` extracted from `XHat`. -/
noncomputable def projectiveP {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι :=
  PFamily data


end

end MIPStarRE.LDT.MakingMeasurementsProjective
