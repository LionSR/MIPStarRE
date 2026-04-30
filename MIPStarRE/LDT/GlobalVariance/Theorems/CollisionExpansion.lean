import MIPStarRE.LDT.GlobalVariance.Theorems.AlgebraicIdentity
namespace MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-! ## Abstract theorem wrappers -/

private lemma generalizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  refine
    { aggregateFamilyComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (axisParallelLineQuestionDistribution params)
          (generalizeBLeftFamily params strategy G)
          (generalizeBRightFamily params strategy G)
          (fun qu g =>
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
          (fun qu g =>
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
          (by
            intro qu
            simp [generalizeBLeftFamily])
          (by
            intro qu
            simp [generalizeBRightFamily])
          (generalizeBError params) (by
            intro g
            simpa [generalizeBDeviationAtPolynomial] using hpoint g)
      pointwiseNormBound := hpoint
      averagedNormBound := by
        simpa [generalizeBDeviation] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
            (generalizeBError params) hpoint }

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  -- The analytic pointwise estimate is an explicit input here. In the
  -- self-improvement pipeline it is supplied as an explicit theorem
  -- hypothesis.
  exact generalizeB_of_pointwise params strategy G ψbi hpoint

/-- The finite reparametrization of incident axis-parallel line questions by a
line `ℓ` and affine parameter `t`, sending `(ℓ,t)` to `(ℓ, ℓ(t))`. -/
private noncomputable def axisParallelLineQuestionParameterEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃
      {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} where
  toFun := fun ℓt => ⟨(ℓt.1, ℓt.1.pointAt ℓt.2), ⟨ℓt.2, rfl⟩⟩
  invFun := fun qu => (qu.1.1, axisParallelLineQuestionParameter qu.1)
  left_inv := by
    intro ℓt
    cases ℓt with
    | mk ℓ t =>
        simp [axisParallelLineQuestionParameter_pointAt]
  right_inv := by
    intro qu
    rcases qu with ⟨qu, hqu⟩
    rcases qu with ⟨ℓ, u⟩
    rcases hqu with ⟨t, ht⟩
    apply Subtype.ext
    dsimp only
    have hparam : axisParallelLineQuestionParameter (ℓ, u) = t := by
      calc
        axisParallelLineQuestionParameter (ℓ, u) =
            axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) := by rw [ht]
        _ = t := axisParallelLineQuestionParameter_pointAt ℓ t
    ext <;> simp [hparam, ht]

/-- Reindex the axis-parallel line-question distribution as a uniform average over
line/parameter seeds `(ℓ,t)` with sampled point `u = ℓ(t)`.

This is the distributional bookkeeping used in `expansion.tex`, lines 281--288. -/
lemma avgOver_axisParallelLineQuestionDistribution
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (axisParallelLineQuestionDistribution params) f =
      avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
  classical
  let e := axisParallelLineQuestionParameterEquiv params
  haveI :
      Nonempty {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} := by
    exact ⟨e (Classical.choice
      (inferInstance : Nonempty (AxisParallelLine params × Fq params)))⟩
  calc
    avgOver (axisParallelLineQuestionDistribution params) f =
        avgOver (uniformDistribution
          {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu})
          (fun qu => f qu.1) := by
          let p : AxisParallelLineQuestion params → Prop := pointOnLine (params := params)
          have hcard : ((Finset.univ.filter p).card : Error) =
              (Fintype.card {qu : AxisParallelLineQuestion params // p qu} : Error) := by
            simp [p, Fintype.card_subtype]
          unfold axisParallelLineQuestionDistribution avgOver uniformDistribution
          dsimp only
          rw [← hcard]
          let support : Finset (AxisParallelLineQuestion params) := Finset.univ.filter p
          change (∑ x ∈ support,
              (if x ∈ support then 1 / (support.card : Error) else 0) * f x) =
            ∑ x : {qu : AxisParallelLineQuestion params // p qu},
              (1 / (support.card : Error)) * f x.1
          calc
            (∑ x ∈ support,
                (if x ∈ support then 1 / (support.card : Error) else 0) * f x)
              = ∑ x ∈ support, (1 / (support.card : Error)) * f x := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  simp [hx]
            _ = ∑ x : {qu : AxisParallelLineQuestion params // p qu},
                (1 / (support.card : Error)) * f x.1 := by
                  simpa [support, p] using
                    (Finset.sum_subtype_eq_sum_filter
                      (s := (Finset.univ : Finset (AxisParallelLineQuestion params)))
                      (f := fun qu : AxisParallelLineQuestion params =>
                        (1 / ((Finset.univ.filter p).card : Error)) * f qu)
                      (p := p)).symm
    _ = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          have h := (avgOver_uniform_equiv (e := e.symm)
            (f := fun qu :
              {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} =>
                f qu.1))
          simpa [e, axisParallelLineQuestionParameterEquiv] using h

/-- Reindex a line representative and affine parameter by the sampled point on
that line, keeping the direction and parameter as auxiliary data.

This is the finite bookkeeping behind `expansion.tex`, lines 300--302: averaging
over a line representative `ℓ` and a parameter `t` is the same as averaging over
the sampled base point `u = ℓ(t)`, the direction, and the forgotten parameter. -/
noncomputable def axisParallelLinePointParamEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃ AxisParallelTestSample params × Fq params where
  toFun := fun ℓt => ((ℓt.1.pointAt ℓt.2, ℓt.1.direction), ℓt.2)
  invFun := fun st =>
    (({ base := fun j => if j = st.1.2 then subCoord (st.1.1 j) st.2 else st.1.1 j,
        direction := st.1.2 } : AxisParallelLine params), st.2)
  left_inv := by
    intro ℓt
    cases ℓt with
    | mk ℓ t =>
        cases ℓ with
        | mk base direction =>
            simp only [Prod.mk.injEq, AxisParallelLine.mk.injEq, and_true]
            funext j
            by_cases hj : j = direction <;>
              simp [AxisParallelLine.pointAt, hj, subCoord_addCoord_right]
  right_inv := by
    intro st
    cases st with
    | mk s t =>
        cases s with
        | mk u direction =>
            simp only [Prod.mk.injEq, and_true]
            ext j
            by_cases hj : j = direction <;>
              simp [AxisParallelLine.pointAt, hj]

/-- Marginalizing the uniform line/parameter presentation to the sampled point
and direction gives the native axis-parallel base-point test distribution. -/
private lemma avgOver_axisParallelLinePointParam
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelTestSample params → Error) :
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
      (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction)) =
    avgOver (uniformDistribution (AxisParallelTestSample params)) f := by
  let e := axisParallelLinePointParamEquiv params
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
      = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f ((e.symm st).1.pointAt (e.symm st).2, (e.symm st).1.direction)) := by
          exact avgOver_uniform_equiv (e := e)
            (f := fun ℓt : AxisParallelLine params × Fq params =>
              f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f st.1) := by
          apply avgOver_congr
          intro st
          have h := congrArg Prod.fst (e.right_inv st)
          exact congrArg f h
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) f :=
        avgOver_uniform_fst f

/-- Combining the incident-pair distribution with the sampled-point marginal gives
the native base-point test distribution. -/
lemma avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelTestSample params → Error) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu => f (qu.2, qu.1.direction)) =
    avgOver (uniformDistribution (AxisParallelTestSample params)) f := by
  rw [avgOver_axisParallelLineQuestionDistribution]
  exact avgOver_axisParallelLinePointParam params f

/-- Expanding the postprocessed collision event at the seeded question
`(ℓ, ℓ(t))` gives the line-answer sum from `expansion.tex`, lines 283--286. -/
private lemma generalizeBCollisionSeed_integrand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t))
        (G.outcome g)) =
      ∑ f : AxisLinePolynomial params,
        (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)) := by
  classical
  unfold generalizeBCollisionOperatorAtPolynomial generalizeBCollisionEventSubMeasAtPolynomial
    generalizeBCollisionEventProjMeasAtPolynomial
  simp only [ProjMeas.postprocess, postprocess, axisParallelLineQuestionParameter_pointAt,
    Polynomial.restrictToAxisParallelLine_apply]
  rw [opTensor_sum_left_finset]
  rw [ev_finset_sum]
  simp [Finset.sum_filter]

private lemma generalizeBLineCollisionTensorMass_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    0 ≤ ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
      (G.outcome g)) := by
  simpa [leftTensor_mul_rightTensor_eq_opTensor] using
    ev_leftTensor_mul_rightTensor_nonneg strategy.state
      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome_pos f)
      (G.outcome_pos g)

/-- The total tensor mass left after summing over line answers is at most one.

This is the normalization half of `expansion.tex`, lines 286--288: the
left-register line measurement sums to its total operator, the right-register
operator is the single submeasurement outcome `G_g ≤ 1`, and the strategy state
is normalized. -/
private lemma generalizeBLineCollisionTensorMass_sum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
        (G.outcome g))) ≤ 1 := by
  let B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor (B.outcome f) (G.outcome g)))
      = ev strategy.state (∑ f : AxisLinePolynomial params,
          opTensor (B.outcome f) (G.outcome g)) := by
          rw [ev_sum]
    _ = ev strategy.state (leftTensor (ι₂ := ι) B.total *
          rightTensor (ι₁ := ι) (G.outcome g)) := by
          congr 1
          calc
            (∑ f : AxisLinePolynomial params, opTensor (B.outcome f) (G.outcome g))
              = ∑ f : AxisLinePolynomial params,
                  leftTensor (ι₂ := ι) (B.outcome f) *
                    rightTensor (ι₁ := ι) (G.outcome g) := by
                    simp [leftTensor_mul_rightTensor_eq_opTensor]
            _ = (∑ f : AxisLinePolynomial params, leftTensor (ι₂ := ι) (B.outcome f)) *
                  rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [Finset.sum_mul]
            _ = leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ B.outcome]
                    rw [B.sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          apply ev_mono strategy.state _ _
          calc
            leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g)
              = opTensor B.total (G.outcome g) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) B.total :=
                  opTensor_le_leftTensor (SubMeas.total_nonneg B) (SubMeas.outcome_le_one G g)
            _ ≤ 1 := leftTensor_le_one (ι₂ := ι) B.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

private lemma generalizeBLineCollisionCoefficient_le
    (params : Parameters)
    [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    avgOver (uniformDistribution (Fq params))
      (fun t =>
        if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) ≤ generalizeBError params := by
  classical
  let h := Polynomial.restrictToAxisParallelLine params g ℓ
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  by_cases hneq : f.poly ≠ h.poly
  · have hline := axisLinePolynomialAgreement_avg_le_mdq params f h hneq
    simpa [h, δ, generalizeBError, hneq] using hline
  · rw [show
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : Error)
            else 0) = 0 by
          simpa [h, hneq] using (avgOver_zero (uniformDistribution (Fq params)))]
    exact hδ_nonneg

/-- Commuting the uniform parameter average past the finite sum over line answers.

This is the purely finite-sum bookkeeping between the paper's seed average over
`(ℓ,t)` and the coefficient-weighted display in `expansion.tex`, lines 286--288.
The remaining #753 residual is now only the incident-question/postprocess equality
between `generalizeBCollisionResidual` and `generalizeBSeedCollisionExpansion`. -/
lemma generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy ψbi G g =
      generalizeBLineCollisionExpansion params strategy ψbi G g := by
  classical
  unfold generalizeBSeedCollisionExpansion generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt =>
          ∑ f : AxisLinePolynomial params,
            (if f ℓt.2 = (Polynomial.restrictToAxisParallelLine params g ℓt.1) ℓt.2 ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓt.1).poly then
              (1 : Error)
            else 0) *
              ev ψbi (opTensor
                ((strategy.axisParallelMeasurement ℓt.1).toSubMeas.outcome f)
                (G.outcome g)))
      = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => avgOver (uniformDistribution (Fq params))
            (fun t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              avgOver (uniformDistribution (Fq params))
                (fun t =>
                  (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                      f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                    (1 : Error)
                  else 0) *
                    ev ψbi (opTensor
                      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                      (G.outcome g)))) := by
          apply avgOver_congr
          intro ℓ
          exact avgOver_sum (uniformDistribution (Fq params))
            (fun t f =>
              (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
                ev ψbi (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              avgOver (uniformDistribution (Fq params))
                (fun t =>
                  if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                      f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                    (1 : Error)
                  else 0) *
                ev ψbi (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
          apply avgOver_congr
          intro ℓ
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [avgOver_mul_const]

/-- The incident-question collision residual is exactly the uniform line/parameter
seed expansion from `expansion.tex`, lines 286--288.

The proof reindexes the axis-parallel line-test distribution by `(ℓ,t)` with
sampled point `u = ℓ(t)`, then expands the `ProjMeas.postprocess` fiber for the
collision event `f(t) = g|_ℓ(t)` and `f ≠ g|_ℓ`. -/
lemma generalizeBCollisionResidual_eq_seedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g =
      generalizeBSeedCollisionExpansion params strategy strategy.state G g := by
  classical
  unfold generalizeBCollisionResidual generalizeBSeedCollisionExpansion
  rw [avgOver_axisParallelLineQuestionDistribution]
  apply avgOver_congr
  intro ℓt
  cases ℓt with
  | mk ℓ t =>
      exact generalizeBCollisionSeed_integrand params strategy strategy.state G g ℓ t

/-- The explicit line/parameter collision expansion is bounded by `m*d/q`.

This proves the Schwartz--Zippel and normalization parts of the residual estimate
from `expansion.tex`, lines 286--288.  The preceding
`generalizeBCollisionResidual_eq_seedCollisionExpansion` theorem supplies the
incident-question/postprocess identity needed to apply this bound to the original
collision residual. -/
lemma generalizeBLineCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBLineCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  classical
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  unfold generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params))
      (fun ℓ =>
        ∑ f : AxisLinePolynomial params,
          avgOver (uniformDistribution (Fq params))
            (fun t =>
              if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g)))
      ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              δ * ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            refine Finset.sum_le_sum ?_
            intro f _
            exact mul_le_mul_of_nonneg_right
              (by simpa [δ] using generalizeBLineCollisionCoefficient_le params g ℓ f)
              (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => δ * ∑ f : AxisLinePolynomial params,
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g))) := by
            apply avgOver_congr
            intro ℓ
            rw [Finset.mul_sum]
    _ ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun _ℓ => δ * 1) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            exact mul_le_mul_of_nonneg_left
              (generalizeBLineCollisionTensorMass_sum_le_one params strategy G g ℓ)
              hδ_nonneg
    _ = δ := by
            simpa using (avgOver_uniform_const (α := AxisParallelLine params) (c := δ))
    _ = generalizeBError params := rfl

/-- The uniform line/parameter seed collision expansion is bounded by `m*d/q`.

The proof first commutes the finite seed average into the coefficient-weighted
line expansion, then applies the Schwartz--Zippel coefficient bound and tensor
normalization estimate above. -/
lemma generalizeBSeedCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- The pointwise collision residual in `lem:generalize-b` is bounded by `m*d/q`.

This combines the incident-question reindexing with the seed/line expansion,
Schwartz--Zippel coefficient bound, and submeasurement-normalization estimate
from `expansion.tex`, lines 281--288. -/
lemma generalizeBCollisionResidual_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBCollisionResidual_eq_seedCollisionExpansion]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Compatibility wrapper: a seed-expansion equality hypothesis also gives the
collision-residual estimate.

The equality is now provided by
`generalizeBCollisionResidual_eq_seedCollisionExpansion`; this lemma is retained
for callers that still pass the reindexing identity explicitly. -/
lemma generalizeBCollisionResidual_le_of_seedExpansion_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (hreindex :
      generalizeBCollisionResidual params strategy strategy.state G g =
        generalizeBSeedCollisionExpansion params strategy strategy.state G g) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [hreindex]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Compatibility reduction from the older line-expansion equality hypothesis. -/
lemma generalizeBCollisionResidual_le_of_lineExpansion_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (hreindex :
      generalizeBCollisionResidual params strategy strategy.state G g =
        generalizeBLineCollisionExpansion params strategy strategy.state G g) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [hreindex]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- Strategy-state reduction for `lem:generalize-b` after the projective expansion.

This theorem removes the conclusion-shaped pointwise norm hypothesis from the
legacy wrapper.  The residual input is exactly the line-collision quantity
bounded above by `generalizeBCollisionResidual_le_error`, following
`expansion.tex`, lines 286--288. -/
lemma generalizeBFromCollisionResidual
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hcollision :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g ≤
          generalizeBError params) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeB_of_pointwise params strategy G strategy.state ?_
  intro g
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact hcollision g

/-- Pointwise Schwartz--Zippel bound for the strategy-state form of
`lem:generalize-b`.

This is the paper's estimate at `expansion.tex`, lines 281--288, after the
projective expansion converts the squared norm into the collision residual. -/
lemma generalizeBPointwiseSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact generalizeBCollisionResidual_le_error params strategy G g

/-- `lem:generalize-b` for the strategy state, with the pointwise
Schwartz--Zippel estimate discharged internally.  The good-strategy hypothesis is
kept in the statement to match the paper context of `expansion.tex`,
lines 271--288, although the algebraic Schwartz--Zippel proof itself does not
use `ε`, `δ`, or `γ`. -/
lemma generalizeBFromSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι) :
    GeneralizeBStatement params strategy strategy.state G := by
  exact generalizeBFromCollisionResidual params strategy G
    (generalizeBCollisionResidual_le_error params strategy G)

/-- Strategy-state reduction for `lem:generalize-b` from the uniform line/parameter
seed collision expansion.

This compatibility route keeps the older explicit seed-expansion interface.
The equality input is now provided by
`generalizeBCollisionResidual_eq_seedCollisionExpansion`; callers that do not
need to supply it separately can use `generalizeBFromSchwartzZippel`. -/
lemma generalizeBFromSeedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hreindex :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g =
          generalizeBSeedCollisionExpansion params strategy strategy.state G g) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeBFromCollisionResidual params strategy G ?_
  intro g
  exact generalizeBCollisionResidual_le_of_seedExpansion_eq
    params strategy G g (hreindex g)

/-- Strategy-state reduction for `lem:generalize-b` from the explicit line/parameter
collision expansion.

This compatibility route keeps the older explicit line-expansion interface.
The seed-expansion route now proves the needed reindexing identity and pointwise
bound directly via `generalizeBCollisionResidual_le_error`. -/
lemma generalizeBFromLineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hreindex :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g =
          generalizeBLineCollisionExpansion params strategy strategy.state G g) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeBFromCollisionResidual params strategy G ?_
  intro g
  exact generalizeBCollisionResidual_le_of_lineExpansion_eq
    params strategy G g (hreindex g)


end MIPStarRE.LDT.GlobalVariance
