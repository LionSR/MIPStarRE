import MIPStarRE.LDT.Test.Classical

/-!
# Surface-versus-point classical infrastructure

Geometric surface questions, bivariate polynomial answers, and deterministic
classical acceptance probabilities for the overview-level Raz--Safra
surface-versus-point low-degree test.

## References

- arXiv:2009.12982, Introduction, Theorem 1.1 (`thm:raz-safra`).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A parameterized affine surface in `F_q^m`, encoded by a base point together
with two direction vectors.

The intended geometric surface is the image of
`(t₁, t₂) ↦ base + t₁ • direction₁ + t₂ • direction₂`. We keep this ordered
frame representation, rather than quotienting by reparametrizations, because the
surface prover's answer is a polynomial on a specific chosen parameterization.
The actual verifier sampling later restricts to the genuine 2-dimensional cases,
i.e. those with linearly independent directions. -/
structure Surface (params : Parameters) where
  base : Point params
  direction₁ : Point params
  direction₂ : Point params
  deriving DecidableEq, Inhabited, Fintype

/-- Parameter coordinates on a sampled surface, identified with `F_q^2`. -/
abbrev SurfaceParameter (params : Parameters) := PointTuple params 2

namespace Surface

/-- The canonical affine parameterization of a surface question. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (s : Surface params) : SurfaceParameter params → Point params :=
  fun t =>
    addPoint s.base
      (addPoint (smulPoint (t 0) s.direction₁)
        (smulPoint (t 1) s.direction₂))

/-- The two direction vectors are linearly independent over the coded field, so
this parameterized affine surface is genuinely 2-dimensional.

This is the repository's encoded `Fq params = Fin params.q` formulation of the
usual linear-independence condition over `Scalar params`; after decoding through
`decodeScalar`, it is equivalent to saying the two direction vectors are linearly
independent in the `Scalar params`-vector space `Point params → Scalar params`. -/
def IsTwoDimensional {params : Parameters} [FieldModel params.q]
    (s : Surface params) : Prop :=
  ∀ a b : Fq params,
    addPoint (smulPoint a s.direction₁) (smulPoint b s.direction₂) = zeroPoint →
      a = zeroCoord ∧ b = zeroCoord

instance {params : Parameters} [FieldModel params.q] :
    DecidablePred (Surface.IsTwoDimensional (params := params)) := by
  intro s
  unfold Surface.IsTwoDimensional
  infer_instance

end Surface

/-- Multivariate polynomial model for answers on a sampled affine surface. -/
abbrev SurfacePolynomialModel (params : Parameters) [FieldModel params.q] :=
  MvPolynomial (Fin 2) (Scalar params)

/-- Decode a coded surface parameter into the chosen field model. -/
def decodeSurfaceParameter {params : Parameters} [FieldModel params.q]
    (t : SurfaceParameter params) : Fin 2 → Scalar params :=
  fun i => decodeScalar (t i)

/-- Evaluate a bivariate surface polynomial answer on coded surface parameters. -/
noncomputable def evalSurfacePolynomialModel (params : Parameters) [FieldModel params.q]
    (p : SurfacePolynomialModel params) (t : SurfaceParameter params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodeSurfaceParameter t) p)

/-- Surface answers in the classical Raz--Safra test are genuine bivariate
polynomials whose total degree is at most `d`. -/
structure SurfacePolynomial (params : Parameters) [FieldModel params.q] where
  poly : SurfacePolynomialModel params
  totalDegreeBounded : poly.totalDegree ≤ params.d

namespace SurfacePolynomial

/-- Evaluation of a surface answer on the two surface parameters. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q]
    (f : SurfacePolynomial params) : SurfaceParameter params → Fq params :=
  evalSurfacePolynomialModel params f.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (SurfacePolynomial params) (fun _ => SurfaceParameter params → Fq params) :=
  ⟨SurfacePolynomial.toFun⟩

@[ext] theorem ext {params : Parameters} [FieldModel params.q]
    {f g : SurfacePolynomial params} (hpoly : f.poly = g.poly) : f = g := by
  cases f
  cases g
  cases hpoly
  congr

end SurfacePolynomial

namespace Test

/-- A sampled surface-versus-point question consists of a parameterized surface
`S` together with a hidden parameter `t ∈ F_q^2`; the queried point is then
`S.pointAt t`. The surface prover sees only `S`, not `t`. -/
abbrev SurfaceVsPointSample (params : Parameters) :=
  Surface params × SurfaceParameter params

/-- The finite support of the modeled surface-versus-point distribution: the
sampled surface must be genuinely 2-dimensional, while the point parameter is
left unrestricted. -/
noncomputable def surfaceVsPointSupport (params : Parameters) [FieldModel params.q] :
    Finset (SurfaceVsPointSample params) :=
  Finset.univ.filter (fun sample => sample.1.IsTwoDimensional)

/-- The distribution of the classical surface-versus-point test questions.

The paper samples `u ∈ F_q^m` uniformly and then a uniformly random
2-dimensional affine surface containing `u`. Since `Surface params` is encoded
by a base point together with an ordered pair of direction vectors, we realize
this as the normalized uniform distribution on the framed incident pairs
`(S, t)`, where `S` is a genuine 2-dimensional parameterized surface and the
queried point is `S.pointAt t`. The hidden parameter `t` keeps the queried point
invisible to the surface prover while still allowing surface answers to be
modeled by ordinary bivariate polynomials in the chosen coordinates.

Because the 2-dimensionality constraint depends only on the surface frame, the
parameter `t` remains uniform conditional on `S`, and the induced queried-point
marginal is still uniform on `Point params`. When `params.m < 2`, no genuine
2-dimensional surfaces exist, so this support is empty; the surrounding
Raz--Safra wrapper remains an explicit quoted-theorem interface in that edge
case rather than a direct formalization of the classical result. -/
noncomputable def surfaceVsPointDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (SurfaceVsPointSample params) :=
  let support := surfaceVsPointSupport params
  { support := support
    weight := fun sample => if sample ∈ support then 1 / (support.card : Error) else 0
    nonnegative := by
      intro sample
      by_cases hs : sample ∈ support <;> simp [hs]
    outsideSupport := by
      intro sample hs
      simp [hs] }

/-- Deterministic classical answers for the `k = 2` surface-versus-point test:
Prover A answers point queries, and Prover B answers surface queries. -/
structure TwoProverClassicalSurfaceVsPointStrategy (params : Parameters)
    [FieldModel params.q] where
  /-- Prover A's answer to a point query. -/
  pointAnswerA : Point params → Fq params
  /-- Prover B's answer to a surface query. -/
  surfaceAnswerB : Surface params → SurfacePolynomial params

namespace TwoProverClassicalSurfaceVsPointStrategy

/-- Whether the deterministic classical strategy is accepted on a sampled
surface-versus-point instance. If `sample = (S, t)`, the point prover is queried
at `S.pointAt t`, while the surface prover sees only `S` and must answer with a
surface polynomial whose evaluation at the hidden parameter `t` matches the
point answer. -/
def accepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params)
    (sample : SurfaceVsPointSample params) : Prop :=
  strategy.surfaceAnswerB sample.1 sample.2 =
    strategy.pointAnswerA (sample.1.pointAt sample.2)

noncomputable instance {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params)
    (sample : SurfaceVsPointSample params) : Decidable (strategy.accepts sample) := by
  unfold TwoProverClassicalSurfaceVsPointStrategy.accepts
  infer_instance

/-- Acceptance probability of the classical surface-versus-point test, written
as an average over the modeled distribution of genuine 2-dimensional framed
surface/point pairs. -/
noncomputable def acceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params) : Error :=
  avgOver (surfaceVsPointDistribution params) fun sample =>
    if strategy.accepts sample then (1 : Error) else 0

/-- Passing the classical surface-versus-point test with error `eps`, stated in
acceptance-probability form. -/
structure ClassicallyPassesSurfaceVsPointTest {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params) (eps : Error) : Prop where
  /-- The modeled classical acceptance probability is at least `1 - eps`. -/
  acceptanceLowerBound :
    1 - eps ≤ strategy.acceptanceProbability

end TwoProverClassicalSurfaceVsPointStrategy

end Test

end MIPStarRE.LDT
