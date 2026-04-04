import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — Q/X/XHat/P intermediate layer

Paper-faithful proof infrastructure for the internal orthonormalization chain in
`references/ldt-paper/orthonormalization.tex`.

This file adds the intermediate `Q/X/XHat/P` objects and the 17 helper-lemma
stubs tracked in issue #197. The actual proofs are deferred, but the signatures
are intended to match the paper's decomposition of the argument.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

/-- The square-root error term `ζ^(1/2)` used throughout the paper's spectral
truncation and rank-reduction estimates. -/
noncomputable def zetaSqrt (ζ : Error) : Error :=
  Real.rpow ζ (1 / (2 : Error))

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
structure QLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  auxSpace : FiniteHilbertSpace
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
      (2 * zetaSqrt ζ)
  total_le :
    R.total ≤ (((1 : Error) + 2 * zetaSqrt ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Witness package for `lem:projective-low-rank-sum`. -/
structure RankReductionWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (data : QLayerData Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa data a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily data.q)
      (roundingToProjectiveError ζ)
  total_le :
    QTotal data ≤ (((1 : Error) + 2 * zetaSqrt ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)
  auxDim_le :
    Fintype.card data.auxSpace.carrier ≤ Fintype.card ι

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.  The square matrices `u`, `v`, `sigmaLeft`,
and `sigmaRight` are placeholders for the SVD objects appearing in the paper's
formulas. -/
structure QXPLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  u : MatrixOperator qLayer.auxSpace
  v : MIPStarRE.Quantum.Op ι
  sigmaLeft : MatrixOperator qLayer.auxSpace
  sigmaRight : MIPStarRE.Quantum.Op ι

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
    OpFamily Outcome ι where
  outcome := Pa data
  total := ∑ a, Pa data a

/-- **Almost-projective estimate** (`eq:A-looks-projective`).

This is the opening inequality in the proof of
`lem:orthonormalization-main-lemma`, extracted as an explicit Lean lemma so the
later `Q/X/XHat/P` layer can depend on it directly. -/
lemma aLooksProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A B : Measurement Outcome ι) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **Scalar truncation inequality** (`lem:trunc-inequality`).

For `x ∈ [0,1]`, truncating at threshold `1 - δ` changes `x` by at most
`(1 / δ) * (x - x^2)` in squared distance. -/
lemma truncationInequality (δ x : Error) :
    0 < δ →
      δ ≤ 1 / 2 →
      0 ≤ x →
      x ≤ 1 →
      let trunc : Error := if 1 - δ ≤ x then 1 else 0
      (x - trunc) ^ (2 : Nat) ≤ (1 / δ) * (x - x ^ (2 : Nat)) := by
  -- TODO: prove (issue #197)
  sorry

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

From the estimate `eq:A-looks-projective`, construct a family `R_a` of
projectors close to `A_a` whose total is bounded by `(1 + 2√ζ)I`. -/
lemma projectiveNonMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) →
      ∃ R : OpFamily Outcome ι,
        RoundingToProjectorsWitness ψ A ζ R := by
  -- TODO: prove (issue #197)
  sorry

/-- **Rank reduction** (`lem:projective-low-rank-sum`).

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension. -/
lemma projectiveLowRankSum {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `Q`** (`lem:Q-completeness`).

If `Q_a` is the rank-reduced family from `lem:projective-low-rank-sum`, then
its total operator `Q` has expectation at least `1 - 11 ζ^(1/4)`. -/
lemma qCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `sqrt Q`** (`lem:sqrt-Q-completeness`).

The square root of the total operator `Q` remains almost complete on `ψ`. -/
lemma sqrtQCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (CFC.sqrt (QTotal data)) ≥ 1 - 12 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **`Q` is almost projective** (`lem:q-almost-projective`).

The rank-reduced family satisfies the operator inequality
`∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ · I`. -/
lemma qAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a)) ≤
        (((4 : Error) * zetaSqrt ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X_a = T_a X`** (`lem:xa-t`). -/
lemma xa_t {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Xa data a = Ta data.qLayer a * data.x := by
  -- TODO: prove (issue #197)
  sorry

/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X` squared** (`lem:X-squared`).

Identifies both Gram matrices of `X` with the paper's SVD data and the total
operator `Q`. -/
lemma xSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xᴴ = data.u * (data.sigmaLeft * data.sigmaLeft) * data.uᴴ ∧
      data.xᴴ * data.x = QTotal data.qLayer ∧
      QTotal data.qLayer = data.v * (data.sigmaRight * data.sigmaRight) * data.vᴴ := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  -- TODO: prove (issue #197)
  sorry

/-- **`P_a` restated** (`lem:pa-restated`).

Rewrites `P_a` in terms of `XHat`, `XHat_a`, and `T_a`. -/
lemma paRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat ∧
      Pa data a = (XHatA data a)ᴴ * data.xHat := by
  -- TODO: prove (issue #197)
  sorry

/-- **`XHat` squared** (`lem:X-hat-squared`).

The unitary-part matrix `XHat` has `XHat XHat† = I` on the auxiliary space. -/
lemma xHatSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHat * data.xHatᴴ =
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X` times `XHat`** (`lem:X-times-X-hat`).

Relates the mixed products `X XHat†` and `X† XHat` to the SVD data and to
`sqrt Q`. -/
lemma xTimesXHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xHatᴴ = data.u * data.sigmaLeft * data.uᴴ ∧
      data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := by
  -- TODO: prove (issue #197)
  sorry

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  -- TODO: prove (issue #197)
  sorry

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  -- TODO: prove (issue #197)
  sorry

/-- **`P` is close to `Q`** (`lem:P-Q-approx`).

The final internal comparison in the paper's repair step shows that `P_a`
is `30 ζ^(1/4)`-close to `Q_a` in the project's `≈`-style raw-family metric. -/
lemma pQApprox {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data.qLayer →
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (30 * zetaQuarterRoot ζ) := by
  -- TODO: prove (issue #197)
  sorry

end

end MIPStarRE.LDT.MakingMeasurementsProjective
