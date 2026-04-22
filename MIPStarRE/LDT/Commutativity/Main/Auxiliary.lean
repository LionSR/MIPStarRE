import MIPStarRE.LDT.Commutativity.Transport.FullSlice
import MIPStarRE.LDT.Commutativity.Transport.EvaluationSpecialization

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
/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354).

Schwartz-Zippel marginalization on the `x` variable: replacing the full
polynomial sum `∑_g G^x_g` by the point-evaluated sum `E_u ∑_a G^x_[g(u)=a]`
inside the ABA term costs at most `params.m · params.d / params.q`.

TODO(#361): apply `schwartzZippel_individualDegree` from
`MIPStarRE/LDT/Preliminaries/Polynomials.lean` to the polynomial-agreement
collision term `1[g(u) = g'(u)]`, then bound the off-diagonal fiber sum using
the sub-measurement property of `G^x`. -/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Paper `eq:evaluate-gcom-at-points-part-dos`
(`commutativity-G.tex` lines 369-385).

Schwartz-Zippel marginalization on the `y` variable: replacing the full
polynomial sum `∑_h G^y_h` by the point-evaluated sum `E_v ∑_b G^y_[h(v)=b]`
inside the ABAB term costs at most `params.m · params.d / params.q`.  Symmetric
in structure to `fullSlice_scalar_marginalize_x`; the paper's difference-
expression label at line 379 is idiosyncratic, so we cite the enclosing
approximation statement. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- The evaluated-slice mixed term with a right-register copy of the second
factor, i.e.
`\(\mathbb E_{u,v,x,y} \sum_{a,b} \langle\psi,
   G^x_{[g(u)=a]} G^y_{[h(v)=b]} G^x_{[g(u)=a]} \otimes G^y_{[h(v)=b]}\, \psi\rangle\)`.

This remains a private `def` (rather than a local `let`) because the remaining
`TODO(#361)` transport bridges are expected to reuse the same named intermediate
scalar quantities. -/
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
intermediate because the remaining evaluated-side `TODO(#361)` bridges are
expected to reference the same quantity. -/
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

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396).

Using `hEval` together with the evaluated-question `closenessOfIP` steps from
the paper: two on the ABA side (line 301: `2√ζ`) and four on the ABAB side
(line 334: `√ζ`, lines 359-360: `2√ζ`, line 396: `√ζ`), plus the line-394
`√ν_evaluation` bridge.  The latter is now packaged by
`evaluatedSlice_hEval_sandwichedRight_to_linearRight`; the remaining work is to
supply the pure `√ζ` bridges coming from postprocessed self-consistency and then
chain everything into the final
`6√ζ + √(commDataProcessedGError)` bound.

TODO(#361): add the remaining evaluated-side `closenessOfIP` bridges on the ABA
and ABAB branches (using postprocessed self-consistency from `_hself` and
`normalizationCondition_sandwich_bound` for the relevant `C` families), then
combine them with `evaluatedSlice_hEval_sandwichedRight_to_linearRight`. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hgamma_nonneg : 0 ≤ gamma) (_hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) := by
  sorry


end MIPStarRE.LDT.Commutativity
