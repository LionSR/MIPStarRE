import MIPStarRE.LDT.Commutativity.Transport.FullSlice
import MIPStarRE.LDT.Commutativity.Transport.EvaluationSpecialization
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left

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

private def evaluatedSliceQuestionEquiv_local (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × Point params) × FullSliceQuestion params where
  toFun := fun q =>
    ((truncatePoint params q.1, truncatePoint params q.2),
      fullSliceQuestionOfEvaluatedSlice params q)
  invFun := fun r =>
    ((appendPoint params r.1.1 r.2.1), (appendPoint params r.1.2 r.2.2))
  left_inv := by
    rintro ⟨u, v⟩
    change
      (appendPoint params (truncatePoint params u) (pointHeight params u),
        appendPoint params (truncatePoint params v) (pointHeight params v)) =
        (u, v)
    exact Prod.ext
      ((CommutativityPoints.pointNextEquiv params).left_inv u)
      ((CommutativityPoints.pointNextEquiv params).left_inv v)
  right_inv := by
    rintro ⟨⟨u, v⟩, x, y⟩
    simp [fullSliceQuestionOfEvaluatedSlice]

private lemma avgOver_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (f : FullSliceQuestion params → Error) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => f (fullSliceQuestionOfEvaluatedSlice params q)) =
    avgOver (uniformDistribution (FullSliceQuestion params)) f := by
  let e := evaluatedSliceQuestionEquiv_local params
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => f (fullSliceQuestionOfEvaluatedSlice params q))
      = avgOver
          (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
          (fun r => f r.2) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q => f (fullSliceQuestionOfEvaluatedSlice params q))
                = avgOver
                    (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                    (fun r => f (fullSliceQuestionOfEvaluatedSlice params (e.symm r))) := by
                      simpa [e] using
                        (avgOver_uniform_equiv e
                          (fun q => f (fullSliceQuestionOfEvaluatedSlice params q)))
              _ = avgOver
                    (uniformDistribution ((Point params × Point params) × FullSliceQuestion params))
                    (fun r => f r.2) := by
                      apply avgOver_congr
                      rintro ⟨⟨u, v⟩, x, y⟩
                      simp [e, evaluatedSliceQuestionEquiv_local,
                        fullSliceQuestionOfEvaluatedSlice]
    _ = avgOver (uniformDistribution (FullSliceQuestion params)) f := by
          simpa using
            (avgOver_uniform_snd
              (α := Point params × Point params)
              (β := FullSliceQuestion params)
              (f := f))

private lemma avgOver_pointHeight_eq_uniform_q
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error) :
    avgOver (uniformDistribution (Point params.next))
      (fun u => f (pointHeight params u)) =
    avgOver (uniformDistribution (Fq params)) f := by
  let e := CommutativityPoints.pointNextEquiv params
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun u => f (pointHeight params u))
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (pointHeight params (e.symm ux))) := by
            simpa [e] using
              (avgOver_uniform_equiv e
                (fun u => f (pointHeight params u)))
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f ux.2) := by
            apply avgOver_congr
            rintro ⟨u, x⟩
            simp [e, CommutativityPoints.pointNextEquiv, pointHeight_appendPoint]
    _ = avgOver (uniformDistribution (Fq params)) f := by
          simpa using
            (avgOver_uniform_snd (α := Point params) (β := Fq params) (f := f))

private lemma avgOver_evaluatedSlice_firstHeight_eq_uniform_q
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => f (pointHeight params q.1)) =
    avgOver (uniformDistribution (Fq params)) f := by
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => f (pointHeight params q.1))
      = avgOver (uniformDistribution (Point params.next))
          (fun u => f (pointHeight params u)) := by
            simpa using
              (avgOver_uniform_fst
                (α := Point params.next) (β := Point params.next)
                (f := fun u => f (pointHeight params u)))
    _ = avgOver (uniformDistribution (Fq params)) f :=
      avgOver_pointHeight_eq_uniform_q params f

private lemma evaluatedPointFamily_postprocessedSelfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta := by
  have hsliceSSC :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Fq params))
        (IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2) := by
    constructor
    calc
      bipartiteSSCError strategy.state
          (uniformDistribution (Fq params))
          (IdxProjSubMeas.toIdxSubMeas family.meas)
        = (1 / 2 : Error) *
            sddError strategy.state
              (uniformDistribution (Fq params))
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
              (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
            unfold bipartiteSSCError sddError
            rw [avgOver_congr (uniformDistribution (Fq params))
              (fun x =>
                qBipartiteSSCDefect strategy.state
                  ((IdxProjSubMeas.toIdxSubMeas family.meas) x))
              (fun x =>
                (1 / 2 : Error) *
                  qSDD strategy.state
                    (((family.meas x).toSubMeas).liftLeft)
                    (((family.meas x).toSubMeas).liftRight))
              (fun x => qBipartiteSSCDefect_eq_half_qSDD_of_proj
                strategy.state strategy.permInvState (family.meas x))]
            rw [avgOver_const_mul]
            rfl
      _ ≤ (1 / 2 : Error) * zeta := by
            exact mul_le_mul_of_nonneg_left
              hself.sliceSelfConsistency.squaredDistanceBound (by positivity)
      _ = zeta / 2 := by ring
  have hpost :
      ∀ u : Point params,
        SDDRel strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          zeta := by
    intro u
    have htmp :=
      Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
        strategy.state
        strategy.permInvState
        (uniformDistribution (Fq params))
        (IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2)
        (fun (_ : Fq params) (g : Polynomial params) => g u)
        hsliceSSC
    refine ⟨?_⟩
    have hbound :
        sddError strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas))) ≤
        2 * (zeta / 2) := by
      simpa [evaluateAt] using htmp.squaredDistanceBound
    calc
      sddError strategy.state
          (uniformDistribution (Fq params))
          (IdxSubMeas.liftLeft
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          (IdxSubMeas.liftRight
            (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
        ≤ 2 * (zeta / 2) := hbound
      _ = zeta := by ring
  constructor
  let e := CommutativityPoints.pointNextEquiv params
  let f : Point params → Fq params → Error :=
    fun u x =>
      qSDD strategy.state
        (leftPlacedSubMeas (ιB := ι)
          (evaluateAt params u ((family.meas x).toSubMeas)))
        (rightPlacedSubMeas (ιA := ι)
          (evaluateAt params u ((family.meas x).toSubMeas)))
  rw [sddError]
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun w =>
          qSDD strategy.state
            (evaluatedPointFamilyLeft params family w)
            (evaluatedPointFamilyRight params family w))
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f ux.1 ux.2) := by
              calc
                avgOver (uniformDistribution (Point params.next))
                    (fun w =>
                      qSDD strategy.state
                        (evaluatedPointFamilyLeft params family w)
                        (evaluatedPointFamilyRight params family w))
                  = avgOver (uniformDistribution (Point params × Fq params))
                      (fun ux =>
                        qSDD strategy.state
                          (evaluatedPointFamilyLeft params family (e.symm ux))
                          (evaluatedPointFamilyRight params family (e.symm ux))) :=
                      avgOver_uniform_equiv e
                        (fun w =>
                          qSDD strategy.state
                            (evaluatedPointFamilyLeft params family w)
                            (evaluatedPointFamilyRight params family w))
                _ = avgOver (uniformDistribution (Point params × Fq params))
                      (fun ux => f ux.1 ux.2) := by
                        apply avgOver_congr
                        intro ux
                        rcases ux with ⟨u, x⟩
                        change qSDD strategy.state
                          (evaluatedPointFamilyLeft params family (appendPoint params u x))
                          (evaluatedPointFamilyRight params family (appendPoint params u x)) =
                            qSDD strategy.state
                              (leftPlacedSubMeas (ιB := ι)
                                (evaluateAt params u ((family.meas x).toSubMeas)))
                              (rightPlacedSubMeas (ιA := ι)
                                (evaluateAt params u ((family.meas x).toSubMeas)))
                        simp [evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
                          evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint,
                          evaluateAt, truncatePoint_appendPoint, pointHeight_appendPoint]
    _ = avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x => f u x)) := by
            exact MIPStarRE.LDT.avgOver_uniform_prod f
    _ ≤ avgOver (uniformDistribution (Point params)) (fun _ => zeta) := by
          apply avgOver_mono
          intro u
          exact (hpost u).squaredDistanceBound
    _ = zeta := by
          have hq0 : (params.q : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hq
          have hq : ((params.q : Error) ^ params.m) ≠ 0 := by
            exact pow_ne_zero params.m hq0
          simp [avgOver, uniformDistribution]
          field_simp [hq]

/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354).

Schwartz-Zippel marginalization on the `x` variable: replacing the full
polynomial sum `∑_g G^x_g` by the point-evaluated sum `E_u ∑_a G^x_[g(u)=a]`
inside the ABA term costs at most `params.m · params.d / params.q`.

TODO(#361): the paper's `md/q` step is manifestly PSD on the tensor-form
comparison `BAB ⊗ A` (paper `eq:gcom4-diff`), but the current Lean stub is
phrased on the scalar `ABA ⊗ I` average.  So the direct positivity argument does
not apply verbatim here.  To close this theorem, we likely need either:
1. a bridge from `fullSliceABAAvg` / `evaluatedSliceABAAvg` to the paper's PSD
   tensor form; after that bridge, the old tactical step should still be to
   apply `polynomialAgreement_avg_le_mdq` (or directly
   `schwartzZippel_individualDegree`) to the off-diagonal collision term
   `1[g(u) = g'(u)]`, then bound the remaining fiber sum by the
   sub-measurement property of `G^x`, or
2. a genuinely new operator bound for the `ABA ⊗ I` difference.
-/
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
approximation statement.

TODO(#361): as for `fullSlice_scalar_marginalize_x`, the paper's
Schwartz-Zippel argument is manifestly PSD on the tensor-form `ABA ⊗ B`, while
this Lean stub is phrased on `ABAB ⊗ I`.  So the clean paper-faithful route is
to first bridge to the tensor form; after that bridge, one should again apply
`polynomialAgreement_avg_le_mdq` (or directly
`schwartzZippel_individualDegree`) to the off-diagonal collision term
`1[h(v) = h'(v)]`, then use the sub-measurement property of `G^y` to control
the remaining fiber sum.  Also, as with the former `x`-marginalization stub,
any honest scalar bound must carry an explicit normalization hypothesis because
`fullSliceABABAvg` and `evaluatedSliceABABAvg` scale linearly with the density
matrix. -/
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

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396).

The current proof takes the direct evaluated-side route suggested in the TODO:
transport `hEval` to `evaluatedSliceProductLeft/Right`, rewrite the resulting
`SDDOpRel` via `evaluatedSliceCommutation_qSDDOp_avg_eq`, and combine it with
the a priori normalized-state bound `sddErrorOp ≤ 4` for the evaluated product
families.  This already yields the stronger estimate
`|evaluatedSliceABAAvg - evaluatedSliceABABAvg| ≤ √ν`; we keep the paper's
`6√ζ + √ν` envelope here so the downstream transport arithmetic can continue to
quote the displayed bound verbatim. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
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
    _ ≤ 6 * Real.sqrt zeta + Real.sqrt δ := by
          have hz : 0 ≤ 6 * Real.sqrt zeta := by positivity
          linarith
    _ = 6 * Real.sqrt zeta +
          Real.sqrt (commDataProcessedGError params gamma zeta) := by
          rfl


end MIPStarRE.LDT.Commutativity
