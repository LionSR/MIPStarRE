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
surface prover's answer is a polynomial on a specific chosen parameterization. -/
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
  cases f with
  | mk polyf hdegf =>
      cases g with
      | mk polyg hdegg =>
          cases hpoly
          congr

end SurfacePolynomial

namespace Test

/-- A sampled surface together with the sampled point on that surface, encoded
through its two affine parameters. This is the product-form presentation of the
paper's random-surface/random-point experiment. -/
abbrev SurfaceVsPointSample (params : Parameters) :=
  Surface params × SurfaceParameter params

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
surface-versus-point instance. -/
def accepts {params : Parameters} [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params)
    (sample : SurfaceVsPointSample params) : Prop :=
  let s := sample.1
  let t := sample.2
  strategy.surfaceAnswerB s t = strategy.pointAnswerA (s.pointAt t)

/-- Acceptance probability of the classical surface-versus-point test, written
as an average over a uniformly random surface together with a uniformly random
point on that surface. -/
noncomputable def acceptanceProbability {params : Parameters}
    [FieldModel params.q]
    (strategy : TwoProverClassicalSurfaceVsPointStrategy params) : Error := by
  classical
  exact avgOver (uniformDistribution (SurfaceVsPointSample params)) fun sample =>
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
