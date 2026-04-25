import MIPStarRE.LDT.GlobalVariance.Defs.Core

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-! ## Weighted operators and variance families -/

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the matrix
square root of the PSD operator `G.outcome g`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (G.outcome g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`, modeled as a density-matrix
transformation: `ρ_g = W_g ρ W_g†` where `W_g = I ⊗ √(G_g)`.

This is not necessarily normalized — normalization would require dividing by
`Tr(G_g ρ_B)`. We keep it unnormalized since the variance quantities in the
paper use unnormalized weighted expectations. -/
noncomputable def weightedPolynomialState (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    QuantumState (ι × ι) :=
  let sqrtG := polynomialWeightSqrtOperator params G g
  let W := rightTensor (ι₁ := ι) sqrtG
  { density := W * strategy.state.density * Wᴴ
    density_psd :=
      ((Matrix.nonneg_iff_posSemidef.mp strategy.state.density_psd).mul_mul_conjTranspose_same
        W).nonneg }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op ι :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  localVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  globalVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match `g(u)` at the queried point `u` on the left side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u then
        some ()
      else
        none)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match the restriction of `g` to `ℓ` on the right side of `lem:generalize-b`. -/
noncomputable def generalizeBRightEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let ℓ := qu.1
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f.poly = gRestricted.poly then
        some ()
      else
        none)

/-- The residual projective `Option Unit` event from the proof of
`lem:generalize-b`: axis-line answers that collide with `g` at the sampled point
`u`, but are not the restricted polynomial `g|_ℓ`.  After the
projective-measurement expansion, the squared difference is controlled by this
collision event. -/
noncomputable def generalizeBCollisionEventProjMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : ProjMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  ProjMeas.postprocess (strategy.axisParallelMeasurement ℓ)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u ∧ f.poly ≠ gRestricted.poly then
        some ()
      else
        none)

/-- The residual event above, forgetting projectivity to a submeasurement.  Keeping
this definition as the `toSubMeas` of `generalizeBCollisionEventProjMeasAtPolynomial`
prevents the projective and submeasurement views from drifting apart. -/
noncomputable def generalizeBCollisionEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).toSubMeas

/-- The event operator for the residual line-collision event in `lem:generalize-b`. -/
noncomputable def generalizeBCollisionOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBCollisionEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The weighted left operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

end MIPStarRE.LDT.GlobalVariance
