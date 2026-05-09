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

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; full rounding-to-projectors
lemma with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Witness structure for the paper's rounding-to-projectors lemma.

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

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:540-553`
(`\label{lem:projective-low-rank-sum}`; rank-reduction lemma with
`12√ζ` closeness, `(1+2√ζ)·I` total bound, and rank constraint
`∑ rank(Q_a) ≤ d`).

Witness structure for the rank-reduction lemma. -/
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
  totalRank_le :
    ∑ a : Outcome, (Qa data a).rank ≤ Fintype.card ι
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
`QLayerData` structure. -/
abbrev matrixDecompositionQ (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  QLayerData Outcome ι

/-- Paper label `def:svd-of-X`.

The paper describes this stage via an SVD of `X`; the Lean API records the
constructive `X/XHat/P` identities needed downstream, avoiding an explicit
rectangular complex-SVD structure. -/
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

/-- Local producer for the `X/Xhat/P` data layer.

Given a `Q`-layer (`def:matrix-decomposition-Q`), the matrix decomposition `X`
of the paper, the chosen `Xhat`, and the two genuinely SVD-derived identities
`Xhat * Xhatᴴ = I` (`lem:X-hat-squared`) and `Xᴴ * Xhat = √Q`
(`lem:X-times-X-hat`), this assembles the `QXPLayerData` package consumed by
the downstream `lem:P-Q-approx` argument.

Exactly one propositional field is proved inside this producer:
`x_gram_right` (`Xᴴ * X = Q`, paper label `lem:X-squared`) follows from the
embedding `Q_a = Xᴴ * T_a * X` (`qa_eq`) together with the fact that the
auxiliary measurement `T = {T_a}` sums to the identity. The other propositional
fields, including `qa_projective`, are supplied by the caller.

The hypothesis `qa_eq` records exactly the `lem:qa-restated` choice, and the
two SVD-derived hypotheses are precisely what the paper proves about
`Xhat = U · I_{m×d} · V†`. The producer therefore feeds directly into
`QXPLayerData` once a rectangular complex SVD of `X` is available; that SVD
existence is the only remaining gap and is independent of this producer. -/
noncomputable def QXPLayerData.ofQLayerAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa qLayer a))
    (q_sum_eq_total : ∑ a : Outcome, Qa qLayer a = QTotal qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry : xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι where
  qLayer := qLayer
  x := x
  xHat := xHat
  qa_eq := qa_eq
  qa_projective := qa_projective
  xHat_coisometry := xHat_coisometry
  x_gram_right := by
    have hT_sum :
        (∑ a : Outcome, Ta qLayer a) =
          (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier) := by
      simpa [Ta] using qLayer.t.sum_eq
    have hmul_sum :
        xᴴ * (∑ a : Outcome, Ta qLayer a) =
          ∑ a : Outcome, xᴴ * Ta qLayer a := by
      simpa using
        (Matrix.mul_sum (s := Finset.univ)
          (f := fun a : Outcome => Ta qLayer a) (M := xᴴ))
    have hsum_mul :
        (∑ a : Outcome, xᴴ * Ta qLayer a) * x =
          ∑ a : Outcome, xᴴ * Ta qLayer a * x := by
      simpa using
        (Matrix.sum_mul (s := Finset.univ)
          (f := fun a : Outcome => xᴴ * Ta qLayer a) (M := x))
    calc
      xᴴ * x
          = xᴴ * (∑ a : Outcome, Ta qLayer a) * x := by
            rw [hT_sum, Matrix.mul_one]
      _ = (∑ a : Outcome, xᴴ * Ta qLayer a) * x := by
            rw [hmul_sum]
      _ = ∑ a : Outcome, xᴴ * Ta qLayer a * x := hsum_mul
      _ = ∑ a : Outcome, qLayer.q.outcome a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact (qa_eq a).symm
      _ = ∑ a : Outcome, Qa qLayer a := rfl
      _ = QTotal qLayer := q_sum_eq_total
  xHat_mixed := xHat_mixed

/-- Existence form of `QXPLayerData.ofQLayerAndSvdIdentities`,
matching the shape requested by issue #1117.

Given a `Q`-layer, supplied projectivity and total-sum hypotheses, the matrix
decomposition `X`, the chosen `Xhat`, and the two SVD-derived primitives, there
is a `QXPLayerData` whose `qLayer`, `x`, and `xHat` are exactly the supplied
data, with the latter two compared after transport along the `qLayer` equality.
The propositional fields are filled by the supplied hypotheses, except
`x_gram_right`, which is proved internally from `qa_eq` and the measurement
identity for `T`. -/
theorem exists_qxpLayerData_ofQLayerAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa qLayer a))
    (q_sum_eq_total : ∑ a : Outcome, Qa qLayer a = QTotal qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry : xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = xHat :=
  ⟨QXPLayerData.ofQLayerAndSvdIdentities qLayer qa_projective q_sum_eq_total
      x xHat qa_eq xHat_coisometry xHat_mixed, rfl, rfl, rfl⟩


end

end MIPStarRE.LDT.MakingMeasurementsProjective
