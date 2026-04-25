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

/-- Witness package for the paper's `lem:projective-non-measurement`.

A value `RoundingToProjectorsWitness ψ A ζ R` is the honest output consumed by
this QXP rank-reduction layer: a chosen rounded family `R_a` together with the
paper's `2√ζ` closeness estimate and `(1 + 2√ζ) I` total-mass bound. -/
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
  sum_eq_total :
    ∑ a, R.outcome a = R.total
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
auxiliary projectors `T_a`.

The local API deliberately stores only the primitive identities used by the
subsequent `P`-vs-`Q` arguments.  Earlier versions also carried explicit SVD
matrices for `X * Xᴴ`, `Xᴴ * X`, and `X * XHatᴴ`; those fields required a
general rectangular complex-matrix SVD producer that is not available in the
current Mathlib toolchain and was not consumed by the downstream proofs. -/
structure QXPLayerData (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x
  qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (qLayer.q.outcome a)
  xHat_coisometry : xHat * xHatᴴ = 1
  x_gram_right : xᴴ * x = QTotal qLayer
  xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)

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

The paper describes this stage via an SVD of `X`; the Lean API records the
constructive `X/XHat/P` identities needed downstream, avoiding an explicit
rectangular complex-SVD package. -/
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
