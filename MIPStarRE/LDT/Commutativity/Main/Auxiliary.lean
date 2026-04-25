import MIPStarRE.LDT.Commutativity.Transport.FullSlice
import MIPStarRE.LDT.Commutativity.Transport.EvaluationSpecialization
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages

/-!
# Section 11 commutativity: auxiliary transport lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real-line triangle helper for the #713 hybrid scalar/tensor route.

If the scalar full endpoint is within `sqrtz` of a full tensor endpoint, the two
tensor endpoints are within `mdq`, and the evaluated scalar endpoint is within
`sqrtz` of the evaluated tensor endpoint, then the scalar endpoints are within
`mdq + 2 * sqrtz`. -/
private lemma abs_sub_le_of_tensor_triangle
    {fullScalar evalScalar fullTensor evalTensor mdq sqrtz : Error}
    (hfull : |fullScalar - fullTensor| ≤ sqrtz)
    (htensor : |fullTensor - evalTensor| ≤ mdq)
    (heval : |evalScalar - evalTensor| ≤ sqrtz) :
    |fullScalar - evalScalar| ≤ mdq + 2 * sqrtz := by
  have heval' : |evalTensor - evalScalar| ≤ sqrtz := by
    rwa [abs_sub_comm]
  have htri :
      |fullScalar - evalScalar| ≤
        |fullScalar - fullTensor| + |fullTensor - evalTensor| +
          |evalTensor - evalScalar| := by
    have hdecomp :
        fullScalar - evalScalar =
          (fullScalar - fullTensor) + (fullTensor - evalTensor) +
            (evalTensor - evalScalar) := by
      ring
    calc
      |fullScalar - evalScalar|
        = |(fullScalar - fullTensor) + (fullTensor - evalTensor) +
            (evalTensor - evalScalar)| := by rw [hdecomp]
      _ ≤ |(fullScalar - fullTensor) + (fullTensor - evalTensor)| +
            |evalTensor - evalScalar| := abs_add_le _ _
      _ ≤ (|fullScalar - fullTensor| + |fullTensor - evalTensor|) +
            |evalTensor - evalScalar| := by
          gcongr
          exact abs_add_le _ _
      _ = |fullScalar - fullTensor| + |fullTensor - evalTensor| +
            |evalTensor - evalScalar| := by ring
  linarith

/-- Tensor-triangle witnesses for the `x`-marginalization scalar wrapper.

The three fields separate the two mathematical ingredients flagged by #720/#730:
* `full_bridge` and `evaluated_bridge` are the two scalar↔tensor
  `closenessOfIP` legs, consuming `hnorm` and `hself` through the FullSlice
  bridge infrastructure from #735;
* `tensor_marginalize` is the `BAB ⊗ A` Schwartz-Zippel tensor
  marginalization, whose remaining finite-sum/postprocessing expansion is #730.

The tensor endpoints themselves remain private to `Transport.FullSlice` per #713,
so this witness is the narrow residual boundary until #730 exports the missing
identity. -/
private structure FullSliceScalarMarginalizeXTensorTriangle
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error) where
  fullTensor : Error
  evaluatedTensor : Error
  full_bridge :
    |fullSliceABAAvg params strategy family - fullTensor| ≤ Real.sqrt zeta
  tensor_marginalize :
    |fullTensor - evaluatedTensor| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q
  evaluated_bridge :
    |evaluatedSliceABAAvg params strategy family - evaluatedTensor| ≤ Real.sqrt zeta

/-- Residual witness construction for the `x` side.

Blocked exactly where the active #730 work sits: exporting/finishing the tensor
marginalization identity and connecting it to the existing scalar↔tensor bridge
endpoints from `Transport.FullSlice`. -/
private noncomputable def fullSlice_scalar_marginalize_x_tensor_triangle_residual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    FullSliceScalarMarginalizeXTensorTriangle params strategy family zeta := by
  -- The eventual proof should instantiate the hidden `BAB ⊗ A` tensor endpoints,
  -- use the #735 `closenessOfIP` bridges for `full_bridge`/`evaluated_bridge`,
  -- and use #730 for `tensor_marginalize`.
  sorry

/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354), in the scalar public API chosen by #713.

Schwartz-Zippel marginalization on the `x` variable after the scalar↔tensor
bridges: replacing the full polynomial sum by the point-evaluated sum costs at
most `(params.m · params.d) / params.q + 2√ζ`.  The extra `2√ζ` is the price of
the two `closenessOfIP` legs in the hybrid scalar/tensor triangle. -/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + 2 * Real.sqrt zeta := by
  let tri :=
    fullSlice_scalar_marginalize_x_tensor_triangle_residual
      params strategy family zeta hnorm hself
  exact abs_sub_le_of_tensor_triangle
    (fullScalar := fullSliceABAAvg params strategy family)
    (evalScalar := evaluatedSliceABAAvg params strategy family)
    (fullTensor := tri.fullTensor)
    (evalTensor := tri.evaluatedTensor)
    (mdq := (↑params.m : Error) * ↑params.d / ↑params.q)
    (sqrtz := Real.sqrt zeta)
    tri.full_bridge tri.tensor_marginalize tri.evaluated_bridge

/-- Tensor-triangle witnesses for the `y`-marginalization scalar wrapper.

This is the y-side analogue of
`FullSliceScalarMarginalizeXTensorTriangle`; here the tensor marginalization
field is the `ABA ⊗ B` Schwartz-Zippel step from #730. -/
private structure FullSliceScalarMarginalizeYTensorTriangle
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error) where
  fullTensor : Error
  evaluatedTensor : Error
  full_bridge :
    |fullSliceABABAvg params strategy family - fullTensor| ≤ Real.sqrt zeta
  tensor_marginalize :
    |fullTensor - evaluatedTensor| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q
  evaluated_bridge :
    |evaluatedSliceABABAvg params strategy family - evaluatedTensor| ≤ Real.sqrt zeta

/-- Residual witness construction for the `y` side.

Blocked exactly on the #730 postprocessing expansion from the hidden `ABA ⊗ B`
tensor endpoints to the proved y-collision residual in `Transport.FullSlice`,
together with exposing the #735 scalar↔tensor bridge endpoints. -/
private noncomputable def fullSlice_scalar_marginalize_y_tensor_triangle_residual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    FullSliceScalarMarginalizeYTensorTriangle params strategy family zeta := by
  -- The eventual proof should instantiate the hidden `ABA ⊗ B` tensor endpoints,
  -- use the #735 `closenessOfIP` bridges for `full_bridge`/`evaluated_bridge`,
  -- and use #730 for `tensor_marginalize`.
  sorry

/-- Paper `eq:evaluate-gcom-at-points-part-dos`
(`commutativity-G.tex` lines 369-385), in the scalar public API chosen by #713.

Schwartz-Zippel marginalization on the `y` variable after the scalar↔tensor
bridges costs at most `(params.m · params.d) / params.q + 2√ζ`. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + 2 * Real.sqrt zeta := by
  let tri :=
    fullSlice_scalar_marginalize_y_tensor_triangle_residual
      params strategy family zeta hnorm hself
  exact abs_sub_le_of_tensor_triangle
    (fullScalar := fullSliceABABAvg params strategy family)
    (evalScalar := evaluatedSliceABABAvg params strategy family)
    (fullTensor := tri.fullTensor)
    (evalTensor := tri.evaluatedTensor)
    (mdq := (↑params.m : Error) * ↑params.d / ↑params.q)
    (sqrtz := Real.sqrt zeta)
    tri.full_bridge tri.tensor_marginalize tri.evaluated_bridge

/-- The evaluated-slice mixed term with a right-register copy of the second
factor, i.e.
`\(\mathbb E_{u,v,x,y} \sum_{a,b} \langle\psi,
   G^x_{[g(u)=a]} G^y_{[h(v)=b]} G^x_{[g(u)=a]} \otimes G^y_{[h(v)=b]}\, \psi\rangle\)`.

This remains a private `def` (rather than a local `let`) because the #720/#730
transport bridge documentation reuses the same named intermediate scalar
quantity. -/
private noncomputable def evaluatedSliceSandwichedRightAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
                ((evaluatedSliceSecondFactor params family q).outcome ab.2) *
                ((evaluatedSliceFirstFactor params family q).outcome ab.1)) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome ab.2)))

/-- The evaluated-slice mixed term with only the linear ordered product on the
left and the right-register copy of the second factor, i.e.
`\(\mathbb E_{u,v,x,y} \sum_{a,b} \langle\psi,
   G^x_{[g(u)=a]} G^y_{[h(v)=b]} \otimes G^y_{[h(v)=b]}\, \psi\rangle\)`.

As with `evaluatedSliceSandwichedRightAvg`, we keep this as a private named
intermediate because the evaluated-side transport documentation references the
same quantity. -/
private noncomputable def evaluatedSliceLinearRightAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
                ((evaluatedSliceSecondFactor params family q).outcome ab.2)) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome ab.2)))

/-- The `hEval` hypothesis already yields the paper's line-394
`\(\sqrt{\nu_{\mathrm{evaluation}}}\)` step: after specializing the full-slice
products to evaluated questions, one `closenessOfIP` application transports the
sandwiched right-register term to the linear right-register term. -/
private lemma evaluatedSlice_hEval_sandwichedRight_to_linearRight
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceSandwichedRightAvg params strategy family -
        evaluatedSliceLinearRightAvg params strategy family| ≤
      Real.sqrt (commDataProcessedGError params gamma zeta) := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => (evaluatedSliceProductLeft params strategy family q).outcome ab
  let B : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => (evaluatedSliceProductRight params strategy family q).outcome ab
  let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → Unit →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab _ =>
      leftTensor (ι₂ := ι)
        ((evaluatedSliceFirstFactor params family q).outcome ab.1) *
        rightTensor (ι₁ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome ab.2)
  have h𝒟 :
      ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB :
      avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤
        commDataProcessedGError params gamma zeta := by
    simpa [𝒟, A, B, qSDDOp] using
      (evaluatedSliceCommutation_of_evaluationSpecialization
        params strategy family
        (commDataProcessedGError params gamma zeta) hEval).squaredDistanceBound
  have hC :
      ∀ q,
        ∑ ab : EvaluatedSliceOutcome params,
            (∑ _ : Unit, C q ab ()) * (∑ _ : Unit, C q ab ())ᴴ ≤ 1 := by
    intro q
    let Aq : ProjSubMeas (Fq params) ι := evaluatedSliceFirstProj params family q
    let Bq : ProjSubMeas (Fq params) ι := evaluatedSliceSecondProj params family q
    calc
      ∑ ab : EvaluatedSliceOutcome params,
          (∑ _ : Unit, C q ab ()) * (∑ _ : Unit, C q ab ())ᴴ
        = ∑ ab : EvaluatedSliceOutcome params,
            leftTensor (ι₂ := ι) (Aq.outcome ab.1) *
              rightTensor (ι₁ := ι) (Bq.outcome ab.2) := by
            refine Finset.sum_congr rfl ?_
            intro ab _
            rcases ab with ⟨a, b⟩
            have hAherm : (Aq.outcome a)ᴴ = Aq.outcome a := Aq.outcome_hermitian a
            have hBherm : (Bq.outcome b)ᴴ = Bq.outcome b := Bq.outcome_hermitian b
            have hAproj : Aq.outcome a * Aq.outcome a = Aq.outcome a := Aq.proj a
            have hBproj : Bq.outcome b * Bq.outcome b = Bq.outcome b := Bq.proj b
            calc
              (∑ _ : Unit, C q (a, b) ()) * (∑ _ : Unit, C q (a, b) ())ᴴ
                = (opTensor (Aq.outcome a) (Bq.outcome b)) *
                    (opTensor (Aq.outcome a) (Bq.outcome b))ᴴ := by
                    simp [C, Aq, Bq, evaluatedSliceFirstProj, evaluatedSliceSecondProj,
                      leftTensor_mul_rightTensor_eq_opTensor]
              _ = opTensor (Aq.outcome a * Aq.outcome a)
                    (Bq.outcome b * Bq.outcome b) := by
                    rw [conjTranspose_opTensor]
                    simp [hAherm, hBherm, opTensor_mul]
              _ = leftTensor (ι₂ := ι) (Aq.outcome a) *
                    rightTensor (ι₁ := ι) (Bq.outcome b) := by
                    rw [hAproj, hBproj, leftTensor_mul_rightTensor_eq_opTensor]
      _ = leftTensor (ι₂ := ι) Aq.total * rightTensor (ι₁ := ι) Bq.total := by
            rw [Fintype.sum_prod_type]
            calc
              ∑ a : Fq params,
                  ∑ b : Fq params,
                    leftTensor (ι₂ := ι) (Aq.outcome a) *
                      rightTensor (ι₁ := ι) (Bq.outcome b)
                = ∑ a : Fq params,
                    leftTensor (ι₂ := ι) (Aq.outcome a) *
                      rightTensor (ι₁ := ι) Bq.total := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [← Matrix.mul_sum]
                      rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ Bq.outcome]
                      rw [Bq.sum_eq_total]
              _ = leftTensor (ι₂ := ι) Aq.total * rightTensor (ι₁ := ι) Bq.total := by
                      rw [← Finset.sum_mul]
                      rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ Aq.outcome]
                      rw [Aq.sum_eq_total]
      _ ≤ 1 := by
            have hop :
                leftTensor (ι₂ := ι) Aq.total * rightTensor (ι₁ := ι) Bq.total ≤
                  leftTensor (ι₂ := ι) Aq.total := by
              simpa [leftTensor_mul_rightTensor_eq_opTensor] using
                (opTensor_le_leftTensor (ι₂ := ι) Aq.total_nonneg Bq.total_le_one)
            exact le_trans hop (leftTensor_le_one (ι₂ := ι) Aq.total_le_one)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C
      (commDataProcessedGError params gamma zeta) hAB hC
  have hLinear :
      avgOver 𝒟
          (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
            ev strategy.state (C q ab () * A q ab)) =
        evaluatedSliceLinearRightAvg params strategy family := by
    unfold evaluatedSliceLinearRightAvg
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro ab _
    rcases ab with ⟨a, b⟩
    have hAproj :
        ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceFirstFactor params family q).outcome a) =
          ((evaluatedSliceFirstFactor params family q).outcome a) := by
      simpa [evaluatedSliceFirstFactor] using
        evaluatedPointFamily_outcome_proj params family q.1 a
    let P := (evaluatedSliceFirstFactor params family q).outcome a
    let Q := (evaluatedSliceSecondFactor params family q).outcome b
    have hPproj : P * P = P := by
      simpa [P] using hAproj
    calc
      ∑ _ : Unit, ev strategy.state (C q (a, b) () * A q (a, b))
        = ev strategy.state (C q (a, b) () * A q (a, b)) := by simp
      _ = ev strategy.state ((leftTensor (ι₂ := ι) P * rightTensor (ι₁ := ι) Q) *
            leftTensor (ι₂ := ι) (P * Q)) := by
            simp [A, C, evaluatedSliceProductLeft, leftOrderedProductOpFamily,
              OpFamily.leftPlacedOpFamily, orderedProductOpFamily, P, Q]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) P * (rightTensor (ι₁ := ι) Q *
              leftTensor (ι₂ := ι) (P * Q))) := by
            rw [mul_assoc]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) P * (leftTensor (ι₂ := ι) (P * Q) *
              rightTensor (ι₁ := ι) Q)) := by
            rw [rightTensor_mul_leftTensor_eq_opTensor,
              ← leftTensor_mul_rightTensor_eq_opTensor]
      _ = ev strategy.state
            ((leftTensor (ι₂ := ι) P * leftTensor (ι₂ := ι) (P * Q)) *
              rightTensor (ι₁ := ι) Q) := by
            rw [← mul_assoc]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (P * (P * Q)) *
              rightTensor (ι₁ := ι) Q) := by
            rw [leftTensor_mul_leftTensor]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) ((P * P) * Q) *
              rightTensor (ι₁ := ι) Q) := by
            congr 1
            rw [mul_assoc]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (P * Q) * rightTensor (ι₁ := ι) Q) := by
            rw [hPproj]
  have hSandwiched :
      avgOver 𝒟
          (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
            ev strategy.state (C q ab () * B q ab)) =
        evaluatedSliceSandwichedRightAvg params strategy family := by
    unfold evaluatedSliceSandwichedRightAvg
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro ab _
    rcases ab with ⟨a, b⟩
    let P := (evaluatedSliceFirstFactor params family q).outcome a
    let Q := (evaluatedSliceSecondFactor params family q).outcome b
    calc
      ∑ _ : Unit, ev strategy.state (C q (a, b) () * B q (a, b))
        = ev strategy.state (C q (a, b) () * B q (a, b)) := by simp
      _ = ev strategy.state ((leftTensor (ι₂ := ι) P * rightTensor (ι₁ := ι) Q) *
            leftTensor (ι₂ := ι) (Q * P)) := by
            simp [B, C, evaluatedSliceProductRight,
              OpFamily.leftPlacedOpFamily, reversedProductOpFamily, P, Q]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) P * (rightTensor (ι₁ := ι) Q *
              leftTensor (ι₂ := ι) (Q * P))) := by
            rw [mul_assoc]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) P * (leftTensor (ι₂ := ι) (Q * P) *
              rightTensor (ι₁ := ι) Q)) := by
            rw [rightTensor_mul_leftTensor_eq_opTensor,
              ← leftTensor_mul_rightTensor_eq_opTensor]
      _ = ev strategy.state
            ((leftTensor (ι₂ := ι) P * leftTensor (ι₂ := ι) (Q * P)) *
              rightTensor (ι₁ := ι) Q) := by
            rw [← mul_assoc]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (P * (Q * P)) *
              rightTensor (ι₁ := ι) Q) := by
            rw [leftTensor_mul_leftTensor]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (((P * Q) * P)) *
              rightTensor (ι₁ := ι) Q) := by
            congr 1
            rw [mul_assoc]
  calc
    |evaluatedSliceSandwichedRightAvg params strategy family -
        evaluatedSliceLinearRightAvg params strategy family|
      = |avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
              ev strategy.state (C q ab () * B q ab)) -
          avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
              ev strategy.state (C q ab () * A q ab))| := by
            rw [hSandwiched, hLinear]
    _ = |avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
              ev strategy.state (C q ab () * A q ab)) -
          avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params, ∑ _ : Unit,
              ev strategy.state (C q ab () * B q ab))| := by
            rw [abs_sub_comm]
    _ ≤ Real.sqrt (commDataProcessedGError params gamma zeta) := hclose

private noncomputable def zeroEvaluatedSliceOpFamily
    (params : Parameters) [FieldModel params.q] :
    OpFamily (EvaluatedSliceOutcome params) (ι × ι) where
  outcome := fun _ => 0
  total := 0

private lemma evaluatedSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (evaluatedSliceProductLeft params strategy family q)
      (zeroEvaluatedSliceOpFamily (ι := ι) params) ≤ 1 := by
  let A : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
  let B : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas B A
  unfold qSDDOp qSDDCore evaluatedSliceProductLeft leftOrderedProductOpFamily
  calc
    ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (((leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2) - 0)ᴴ) *
            (leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2) - 0))
      = ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _
          rcases ab with ⟨a, b⟩
          have hAherm : (A.outcome a)ᴴ = A.outcome a := A.outcome_hermitian a
          have hBherm : (B.outcome b)ᴴ = B.outcome b := B.outcome_hermitian b
          have hAproj : A.outcome a * A.outcome a = A.outcome a := by
            simpa [A, evaluatedSliceFirstFactor] using
              evaluatedPointFamily_outcome_proj params family q.1 a
          have hleftH :
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ =
                leftTensor (ι₂ := ι) ((A.outcome a * B.outcome b)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (A.outcome a * B.outcome b)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((A.outcome a * B.outcome b)ᴴ) *
                (A.outcome a * B.outcome b)) =
              B.outcome b * A.outcome a * B.outcome b := by
            calc
              (((A.outcome a * B.outcome b)ᴴ) *
                  (A.outcome a * B.outcome b))
                = (((B.outcome b)ᴴ * (A.outcome a)ᴴ) *
                    (A.outcome a * B.outcome b)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = B.outcome b * (A.outcome a * A.outcome a) * B.outcome b := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = B.outcome b * A.outcome a * B.outcome b := by
                    simp [hAproj, mul_assoc]
          calc
            ev strategy.state
                (((leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) - 0)ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) - 0))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ) *
                    leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((A.outcome a * B.outcome b)ᴴ) *
                      (A.outcome a * B.outcome b))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (B.outcome b * A.outcome a * B.outcome b)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun ab : EvaluatedSliceOutcome params =>
              leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2))]
          congr 1
          calc
            ∑ ab : EvaluatedSliceOutcome params,
                leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
              = leftTensor (ι₂ := ι)
                  (∑ ab : EvaluatedSliceOutcome params,
                    B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun ab : EvaluatedSliceOutcome params =>
                        B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    calc
                      ∑ ab : EvaluatedSliceOutcome params,
                          B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2
                        = ∑ ba : Fq params × Fq params,
                            B.outcome ba.1 * A.outcome ba.2 * B.outcome ba.1 := by
                              exact Fintype.sum_equiv
                                (Equiv.prodComm (Fq params) (Fq params))
                                (fun ab : Fq params × Fq params =>
                                  B.outcome ab.2 * A.outcome ab.1 * B.outcome ab.2)
                                (fun ba : Fq params × Fq params =>
                                  B.outcome ba.1 * A.outcome ba.2 * B.outcome ba.1)
                                (by intro ab; simp)
                      _ = S.total := by
                            simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

private lemma zero_qSDDOp_evaluatedSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (zeroEvaluatedSliceOpFamily (ι := ι) params)
      (evaluatedSliceProductRight params strategy family q) ≤ 1 := by
  let A : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
  let B : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas A B
  unfold qSDDOp qSDDCore evaluatedSliceProductRight
  calc
    ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (((0 - leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1))ᴴ) *
            (0 - leftTensor (ι₂ := ι) (B.outcome ab.2 * A.outcome ab.1)))
      = ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)) := by
          refine Finset.sum_congr rfl ?_
          intro ab _
          rcases ab with ⟨a, b⟩
          have hAherm : (A.outcome a)ᴴ = A.outcome a := A.outcome_hermitian a
          have hBherm : (B.outcome b)ᴴ = B.outcome b := B.outcome_hermitian b
          have hBproj : B.outcome b * B.outcome b = B.outcome b := by
            simpa [B, evaluatedSliceSecondFactor] using
              evaluatedPointFamily_outcome_proj params family q.2 b
          have hleftH :
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ =
                leftTensor (ι₂ := ι) ((B.outcome b * A.outcome a)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (B.outcome b * A.outcome a)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((B.outcome b * A.outcome a)ᴴ) *
                (B.outcome b * A.outcome a)) =
              A.outcome a * B.outcome b * A.outcome a := by
            calc
              (((B.outcome b * A.outcome a)ᴴ) *
                  (B.outcome b * A.outcome a))
                = (((A.outcome a)ᴴ * (B.outcome b)ᴴ) *
                    (B.outcome b * A.outcome a)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = A.outcome a * B.outcome b * A.outcome a := by
                    simp [hBproj, mul_assoc]
          calc
            ev strategy.state
                (((0 - leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ) *
                  (0 - leftTensor (ι₂ := ι) (B.outcome b * A.outcome a)))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (B.outcome b * A.outcome a))ᴴ) *
                    leftTensor (ι₂ := ι) (B.outcome b * A.outcome a)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((B.outcome b * A.outcome a)ᴴ) *
                      (B.outcome b * A.outcome a))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (A.outcome a * B.outcome b * A.outcome a)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun ab : EvaluatedSliceOutcome params =>
              leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1))]
          congr 1
          calc
            ∑ ab : EvaluatedSliceOutcome params,
                leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)
              = leftTensor (ι₂ := ι)
                  (∑ ab : EvaluatedSliceOutcome params,
                    A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun ab : EvaluatedSliceOutcome params =>
                        A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

private lemma evaluatedSliceProductLeft_to_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (evaluatedSliceProductLeft params strategy family q)
            (zeroEvaluatedSliceOpFamily (ι := ι) params))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact evaluatedSliceProductLeft_qSDDOp_zero_le_one params strategy family hnorm q
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

private lemma zero_to_evaluatedSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
      (evaluatedSliceProductRight params strategy family)
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (zeroEvaluatedSliceOpFamily (ι := ι) params)
            (evaluatedSliceProductRight params strategy family q))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact zero_qSDDOp_evaluatedSliceProductRight_le_one params strategy family hnorm q
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

/-- Strong evaluated-side `hEval` transport bound.

The direct evaluated-side route transports `hEval` to
`evaluatedSliceProductLeft/Right`, rewrites the resulting `SDDOpRel` via
`evaluatedSliceCommutation_qSDDOp_avg_eq`, and combines it with the a priori
normalized-state bound `sddErrorOp ≤ 4` for the evaluated product families.  It
yields the sharper estimate
`|evaluatedSliceABAAvg - evaluatedSliceABABAvg| ≤ √ν`, where
`ν = commDataProcessedGError params gamma zeta`.  The paper-envelope wrapper
`fullSlice_closenessOfIP_CAB_hEval` below recovers the older `6√ζ + √ν`
statement when that displayed Section 11 bound is convenient. -/
lemma fullSlice_closenessOfIP_CAB_hEval_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (_hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      Real.sqrt (commDataProcessedGError params gamma zeta) := by
  let δ := commDataProcessedGError params gamma zeta
  let d : Error :=
    evaluatedSliceABAAvg params strategy family -
      evaluatedSliceABABAvg params strategy family
  have hEval' :=
    evaluatedSliceCommutation_of_evaluationSpecialization
      params strategy family δ _hEval
  have hδ :
      sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSliceProductLeft params strategy family)
        (evaluatedSliceProductRight params strategy family) ≤ δ :=
    hEval'.squaredDistanceBound
  have h4 :
      sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSliceProductLeft params strategy family)
        (evaluatedSliceProductRight params strategy family) ≤ 4 := by
    have hleft :=
      evaluatedSliceProductLeft_to_zero_le_one params strategy family hnorm
    have hright :=
      zero_to_evaluatedSliceProductRight_le_one params strategy family hnorm
    have htri :=
      MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
        strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSliceProductLeft params strategy family)
        (fun _ => zeroEvaluatedSliceOpFamily (ι := ι) params)
        (evaluatedSliceProductRight params strategy family)
        1 1 hleft hright
    linarith [htri.squaredDistanceBound]
  have hExpand :=
    evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family
  have hd_nonneg : 0 ≤ d := by
    have hsdd_nonneg :
        0 ≤ sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (evaluatedSliceProductLeft params strategy family)
          (evaluatedSliceProductRight params strategy family) := by
      unfold sddErrorOp
      exact avgOver_nonneg (uniformDistribution (EvaluatedSliceQuestion params)) _
        (fun q => MIPStarRE.LDT.Preliminaries.qSDDOp_nonneg strategy.state _ _)
    rw [hExpand] at hsdd_nonneg
    simpa [d, evaluatedSliceABAAvg, evaluatedSliceABABAvg] using hsdd_nonneg
  have hδ' : 2 * d ≤ δ := by
    rw [hExpand] at hδ
    simpa [d, evaluatedSliceABAAvg, evaluatedSliceABABAvg] using hδ
  have h4' : 2 * d ≤ 4 := by
    rw [hExpand] at h4
    simpa [d, evaluatedSliceABAAvg, evaluatedSliceABABAvg] using h4
  have hδ_nonneg : 0 ≤ δ := by
    linarith [hδ', hd_nonneg]
  have hd_le_sqrt : d ≤ Real.sqrt δ := by
    by_cases hδ4 : δ ≤ 4
    · have hd_half : d ≤ δ / 2 := by
        linarith [hδ']
      have hhalf_le : δ / 2 ≤ Real.sqrt δ := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
        nlinarith [Real.sq_sqrt hδ_nonneg, hδ4, hsqrt_nonneg]
      exact hd_half.trans hhalf_le
    · have h4le : 4 ≤ δ := le_of_lt (lt_of_not_ge hδ4)
      have hd_two : d ≤ 2 := by
        linarith [h4']
      have htwo_le : 2 ≤ Real.sqrt δ := by
        have hsqrt : Real.sqrt (4 : Error) ≤ Real.sqrt δ :=
          Real.sqrt_le_sqrt h4le
        norm_num at hsqrt
        exact hsqrt
      exact hd_two.trans htwo_le
  calc
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family|
      = d := by
          dsimp [d]
          exact abs_of_nonneg hd_nonneg
    _ ≤ Real.sqrt δ := hd_le_sqrt
    _ = Real.sqrt (commDataProcessedGError params gamma zeta) := by
          rfl

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396), stated with the
paper's displayed `6√ζ + √ν` envelope. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) := by
  have h :=
    fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta
      hnorm hEval
  calc
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family|
      ≤ Real.sqrt (commDataProcessedGError params gamma zeta) := h
    _ ≤ 6 * Real.sqrt zeta +
          Real.sqrt (commDataProcessedGError params gamma zeta) := by
          have hz : 0 ≤ 6 * Real.sqrt zeta := by positivity
          linarith


end MIPStarRE.LDT.Commutativity
