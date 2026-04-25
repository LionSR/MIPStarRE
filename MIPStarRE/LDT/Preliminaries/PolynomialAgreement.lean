import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Preliminaries.Polynomials

/-!
# Polynomial agreement bound (Step 5 hammer)

Public packaging of Schwartz-Zippel for the project's `Polynomial params`
class. This is the building block invoked at:

* paper `references/ldt-paper/inductive_step.tex`, lines 119–133 — the
  `md/q` term in the `mainFormal` self-consistency cascade,
* paper `references/ldt-paper/commutativity-G.tex`, the analogous step in
  `comMain` (issue #297).

The earlier private form of this lemma lived in
`MIPStarRE.LDT.Commutativity.Scaffold.Symmetry`. Promoting it lets both `comMain`
and `mainFormal` Step 5 (#425) share one proof.

## References

* `references/ldt-paper/inductive_step.tex`
* `references/ldt-paper/preliminaries.tex`, Section 3
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Coordinatewise transport between coded `F_q` points and the underlying
scalar model. This is the equivalence used to apply Schwartz-Zippel inside
`MvPolynomial`'s scalar function space. -/
def pointScalarEquiv (params : Parameters) [FieldModel params.q] :
    Point params ≃ (Fin params.m → Scalar params) where
  toFun := decodePoint
  invFun := fun u i => encodeScalar (u i)
  left_inv := by
    intro u
    funext i
    simp [decodePoint, encode_decodeScalar]
  right_inv := by
    intro u
    funext i
    simp [decodePoint, decode_encodeScalar]

/-- Reindex evaluation equality from coded `Point params` points to the scalar
function space used by `schwartzZippel_individualDegree`. -/
lemma polynomialAgreement_avg_eq_scalarDomain
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) =
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) := by
  let e := pointScalarEquiv params
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u => if g (e.symm u) = g' (e.symm u) then (1 : Error) else 0) := by
            simpa [e] using
              (avgOver_uniform_equiv e
                (fun u : Point params => if g u = g' u then (1 : Error) else 0))
    _ = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) := by
            apply avgOver_congr
            intro u
            have hdecode : decodePoint (e.symm u) = u := by
              simpa [e, pointScalarEquiv] using e.right_inv u
            by_cases hEval : MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly
            · have hPointEval : g (e.symm u) = g' (e.symm u) := by
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly)
                congr 1
                simpa [hdecode] using hEval
              simp [hEval, hPointEval]
            · have hPointEval : ¬ g (e.symm u) = g' (e.symm u) := by
                intro hEq
                apply hEval
                apply (FieldModel.equiv (q := params.q)).injective
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly) at hEq
                simpa [encodeScalar, hdecode] using hEq
              simp [hEval, hPointEval]

/-- Schwartz-Zippel bound for the pointwise agreement indicator of two distinct
full polynomial outcomes.

Packages the `md/q` loss term that appears at:
- `references/ldt-paper/inductive_step.tex` lines 119–133 (the `mainFormal`
  Step 5 self-consistency cascade, issue #425),
- `references/ldt-paper/commutativity-G.tex` (the `comMain` step, issue #297).

Both call sites previously held a private duplicate of this proof; this is the
shared, reusable form. -/
lemma polynomialAgreement_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let gLow : polyFunc params.m (Scalar params) params.d :=
    ⟨g.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩
  let g'Low : polyFunc params.m (Scalar params) params.d :=
    ⟨g'.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g'.lowIndividualDegree⟩
  have hneqLow : gLow ≠ g'Low := by
    intro hEq
    have hpoly : g.poly = g'.poly := congrArg Subtype.val hEq
    apply hneq
    cases g
    cases g'
    cases hpoly
    rfl
  have hsz := schwartzZippel_individualDegree gLow g'Low hneqLow
  have havg_scalar :
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) =
      (polynomialAgreementProbability
        params.m (Scalar params) g.poly g'.poly : Error) := by
    calc
      avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0)
        = ∑ u : Fin params.m → Scalar params,
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (Fintype.card (Scalar params) ^ params.m : Error)⁻¹
            else 0 := by
              simp [avgOver, uniformDistribution]
      _ = Finset.sum
            ((Finset.univ : Finset (Fin params.m → Scalar params)).filter
              (fun u => MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly))
            (fun _ => (Fintype.card (Scalar params) ^ params.m : Error)⁻¹) := by
              rw [← Finset.sum_filter]
      _ = (((Finset.univ.filter fun u : Fin params.m → Scalar params =>
              MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly).card : ℕ) : Error) *
            (Fintype.card (Scalar params) ^ params.m : Error)⁻¹ := by
              simp
      _ = (polynomialAgreementProbability
            params.m (Scalar params) g.poly g'.poly : Error) := by
              simp [polynomialAgreementProbability, div_eq_mul_inv]
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) :=
            polynomialAgreement_avg_eq_scalarDomain params g g'
    _ = (polynomialAgreementProbability
          params.m (Scalar params) g.poly g'.poly : Error) :=
          havg_scalar
    _ ≤ ((((params.m * params.d : ℕ) : ℚ≥0) / Fintype.card (Scalar params)) : Error) := by
          exact_mod_cast hsz
    _ = (params.m * params.d : Error) / params.q := by
          simp [scalar_card, div_eq_mul_inv]

open Classical in
/-- Tensor-form Schwartz-Zippel collision bound.

For each off-diagonal pair of polynomial outcomes, the point-collision
coefficient is bounded by `params.m * params.d / params.q` via
`polynomialAgreement_avg_le_mdq`. The remaining tensor residual is bounded by
`1` using `sandwichTensor_residual_sum_le_one`, so the whole nonnegative
collision sum has the same `m d / q` bound. -/
lemma polynomialCollision_sandwichTensor_le_mdq
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (hnorm : ψ.IsNormalized)
    (Outer : SubMeas β ι)
    (Inner Right : SubMeas (Polynomial params) ι) :
    (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev ψ
            (leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ι) (Right.outcome gg.2))) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  have hcoef_le (gg : Polynomial params × Polynomial params) :
      (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) ≤ δ := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq, hδ_nonneg, δ]
    · simpa [hEq, δ] using
        polynomialAgreement_avg_le_mdq params gg.1 gg.2 hEq
  calc
    (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev ψ
            (leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ι) (Right.outcome gg.2)))
      ≤ ∑ gg : Polynomial params × Polynomial params, ∑ o : β,
          δ * ev ψ
            (leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ι) (Right.outcome gg.2)) := by
          refine Finset.sum_le_sum ?_
          intro gg _
          refine Finset.sum_le_sum ?_
          intro o _
          exact mul_le_mul_of_nonneg_right (hcoef_le gg)
            (sandwichTensorSummand_nonneg ψ Outer Inner Right o gg.1 gg.2)
    _ = δ * (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ι) (Right.outcome gg.2))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gg _
          rw [Finset.mul_sum]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (sandwichTensor_residual_sum_le_one ψ hnorm Outer Inner Right) hδ_nonneg
    _ = (params.m * params.d : Error) / params.q := by
          simp [δ]

end MIPStarRE.LDT.Preliminaries
