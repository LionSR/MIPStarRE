import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainBasic
import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree
import MIPStarRE.LDT.Commutativity.GCommStability.Scalar

/-!
# Phase 2 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 2 scalar bridge in
`ProcessedG`.  These definitions extract and bound the one-dimensional stability
defect controlled by `gCommStability_scalar` (the paper's `clm:g-comm-stability`),
reindex the question-level defect into the stability defect via finite
marginalization, and perform the subtraction algebra that rewrites the phase-2
insertion/removal difference as the negative defect.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar defect controlled by `gCommStability_scalar` after averaging out
all evaluated-slice variables except the second slice height `y`.

This is the paper's boundedness witness term for `clm:g-comm-stability`: for a
fixed `y`, `gCommStabilityR params family y` averages the left-register sandwich
`G^{u,x}_a G^y_g G^{u,x}_a`, while
`IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g` averages the
right-register point answer `A^{v,y}_{g(v)}` over the tail point `v`. -/
noncomputable def evaluatedSlicePhaseTwoStabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (y : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

/-- Direct `√ζ` control of the phase-2 stability defect.

The remaining bridge from the explicit evaluated-slice difference to this
one-dimensional defect is pure finite reindexing and averaging: expand
`totalSandwichFamily`, decompose the sampled second point as `(v,y)`, collect the
postprocessing fiber `∑_b ∑_{g : g(v)=b}` into `∑_g`, and average the first
sampled point into `gCommStabilityR`. -/
lemma evaluatedSlice_phaseTwo_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound_psd : ∀ x : Fq params, 0 ≤ family.witness x)
    (hbound_residual :
      avgOver (uniformDistribution (Fq params))
        (fun x => IdxPolyFamily.storedResidual strategy family G x) ≤ zeta)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  simpa [evaluatedSlicePhaseTwoStabilityDefect] using
    (gCommStability_scalar params strategy zeta hnorm family G hG
      hbound_psd hbound_residual hbound_dom)

/-- The still-unmarginalized phase-2 defect at a sampled evaluated-slice question.

This is the exact question-level term obtained after expanding
`totalSandwichFamily` and using
`S * G^y.total - S = -S * (1 - G^y.total)` for the left-register sandwich `S`.
The remaining reindexing residual averages this term to
`evaluatedSlicePhaseTwoStabilityDefect`. -/
noncomputable def evaluatedSlicePhaseTwoQuestionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ b : Fq params, ∑ a : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a)) *
            (1 - (G (pointHeight params q.2)).total)) *
        rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b))


/-- Postprocessing a sandwiched product by its second coordinate sums over the
outer outcome.

For the sandwiched submeasurement with outcomes `(a, b)` and effect
`A_a B_b A_a`, the `Prod.snd` postprocessing has outcome `b` equal to
`∑ a, A_a B_b A_a`.  This is the finite-fiber identity used to recognize the
`gCommStabilityR` averaged sandwich. -/
lemma postprocess_sandwichByOuter_prod_snd_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) (b : β) :
    (postprocess (sandwichByOuterSubMeas A B) Prod.snd).outcome b =
      ∑ a : α, A.outcome a * B.outcome b * A.outcome a := by
  classical
  have hfilter :
      (Finset.univ.filter (fun ab : α × β => ab.2 = b)) =
        (Finset.univ.image (fun a : α => (a, b))) := by
    ext ab
    constructor
    · intro hab
      rcases Finset.mem_filter.mp hab with ⟨_, hb⟩
      rcases ab with ⟨a, b'⟩
      change b' = b at hb
      subst b'
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · intro hab
      rcases Finset.mem_image.mp hab with ⟨a, _, rfl⟩
      simp
  calc
    (postprocess (sandwichByOuterSubMeas A B) Prod.snd).outcome b =
        ∑ ab ∈ (Finset.univ.filter (fun ab : α × β => ab.2 = b)),
          A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1 := by
          simp [postprocess, sandwichByOuterSubMeas]
    _ = ∑ ab ∈ (Finset.univ.image (fun a : α => (a, b))),
          A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1 := by
          rw [hfilter]
    _ = ∑ a : α, A.outcome a * B.outcome b * A.outcome a := by
          rw [Finset.sum_image]
          intro a _ a' _ h
          exact congrArg Prod.fst h

/-- Pull two finite averages into a bipartite expectation with averaged operators.

For a fixed polynomial outcome `g`, the left register is averaged over `𝒟Q`
while the right register is averaged over `𝒟V`.  The identity rewrites the
nested scalar average of
`ev ψ (leftTensor (F q g a * R) * rightTensor (P g v))` into the expectation of
`leftTensor ((E_q ∑_a F q g a) * R) * rightTensor (E_v P g v)`, preserving the
outer sum over `g`. -/
lemma avgOver_avgOver_phaseTwo_linear
    {Q V Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟Q : Distribution Q) (𝒟V : Distribution V)
    (ψ : QuantumState (ι × ι))
    (F : Q → Γ → Aidx → MIPStarRE.Quantum.Op ι)
    (P : Γ → V → MIPStarRE.Quantum.Op ι)
    (R : MIPStarRE.Quantum.Op ι) :
    avgOver 𝒟V (fun v =>
        avgOver 𝒟Q (fun q =>
          ∑ g : Γ, ∑ a : Aidx,
            ev ψ (leftTensor (ι₂ := ι) (F q g a * R) *
              rightTensor (ι₁ := ι) (P g v)))) =
      ∑ g : Γ,
        ev ψ
          (leftTensor (ι₂ := ι)
              ((averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a)) * R) *
            rightTensor (ι₁ := ι)
              (averageOperatorOverDistribution 𝒟V (fun v => P g v))) := by
  classical
  let T : Q → V → Γ → Aidx → Error := fun q v g a =>
    ev ψ (leftTensor (ι₂ := ι) (F q g a * R) *
      rightTensor (ι₁ := ι) (P g v)) * (𝒟Q.weight q * 𝒟V.weight v)
  have hreorder :
      (∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a) =
        ∑ g : Γ, ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
    calc
      (∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a)
          = ∑ v ∈ 𝒟V.support, ∑ g : Γ, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
            refine Finset.sum_congr rfl ?_
            intro v _
            rw [Finset.sum_comm]
      _ = ∑ g : Γ, ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := by
            rw [Finset.sum_comm]
  calc
    avgOver 𝒟V (fun v =>
        avgOver 𝒟Q (fun q =>
          ∑ g : Γ, ∑ a : Aidx,
            ev ψ (leftTensor (ι₂ := ι) (F q g a * R) *
              rightTensor (ι₁ := ι) (P g v))))
        = ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ g : Γ, ∑ a : Aidx, T q v g a := by
          simp [avgOver, T, Finset.mul_sum, mul_assoc, mul_comm]
    _ = ∑ g : Γ, ∑ v ∈ 𝒟V.support, ∑ q ∈ 𝒟Q.support, ∑ a : Aidx, T q v g a := hreorder
    _ = ∑ g : Γ,
        ev ψ
          (leftTensor (ι₂ := ι)
              ((averageOperatorOverDistribution 𝒟Q (fun q => ∑ a : Aidx, F q g a)) * R) *
            rightTensor (ι₁ := ι)
              (averageOperatorOverDistribution 𝒟V (fun v => P g v))) := by
          simp [T, averageOperatorOverDistribution, ev_finset_sum, ev_real_smul,
            ← leftTensor_finset_sum, ← rightTensor_finset_sum,
            Finset.smul_sum, Finset.sum_mul, Finset.mul_sum,
            leftTensor_mul_rightTensor_real_smul_left, leftTensor_mul_rightTensor_real_smul_right,
            mul_assoc, mul_comm]

set_option maxHeartbeats 210000 in
-- The explicit finite-fiber/tensor-linearity proof is just above the default
-- heartbeat budget, but avoids hiding the #714 residual in one large `simp`.
/-- Reindex the pointwise phase-2 question defect by polynomial outcomes.

When the sampled second point is `appendPoint v y`, the postprocessed slice
outcome `(evaluatedSliceSecondFactor ...).outcome b` is the sum of
`G^y_g` over the fiber `g v = b`.  Expanding this fiber inside the sandwiched
left-register expression and summing over `b` collapses the defect to a
polynomial-indexed sum whose right-register outcome is `A^{v,y}_{g(v)}`.

The proof is heartbeat-heavy because it keeps the finite-fiber and tensor
linearity steps explicit rather than hiding the #714 marginalization residual in
one large `simp`. -/
lemma evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q1 : Point params.next) (v : Point params) (y : Fq params) :
    evaluatedSlicePhaseTwoQuestionDefect params strategy family G
        (q1, appendPoint params v y) =
      ∑ g : Polynomial params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((((evaluatedPointFamily params family q1).outcome a) *
                ((family.meas y).toSubMeas.outcome g) *
                ((evaluatedPointFamily params family q1).outcome a)) *
                (1 - (G y).total)) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement (appendPoint params v y)).outcome (g v))) := by
  classical
  let E : Fq params → MIPStarRE.Quantum.Op ι :=
    fun a => (evaluatedPointFamily params family q1).outcome a
  let Y : Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun g => ((family.meas y).toSubMeas.outcome g)
  let P : Fq params → MIPStarRE.Quantum.Op ι :=
    fun b => (strategy.pointMeasurement (appendPoint params v y)).outcome b
  let R : MIPStarRE.Quantum.Op ι := 1 - (G y).total
  have hcollapse :
      (∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((E a * (∑ g ∈ (Finset.univ : Finset (Polynomial params)).filter
                  (fun g => g v = b), Y g) * E a) * R)) *
            rightTensor (ι₁ := ι) (P b))) =
      ∑ g : Polynomial params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
            rightTensor (ι₁ := ι) (P (g v))) := by
    calc
      (∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((E a * (∑ g ∈ (Finset.univ : Finset (Polynomial params)).filter
                  (fun g => g v = b), Y g) * E a) * R)) *
            rightTensor (ι₁ := ι) (P b)))
          = ∑ b : Fq params, ∑ a : Fq params,
              ∑ g ∈ (Finset.univ : Finset (Polynomial params)).filter (fun g => g v = b),
                ev strategy.state
                  (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    rightTensor (ι₁ := ι) (P b)) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [ev_leftTensor_mul_middle_finset_sum
                (ι := ι)
                (s := (Finset.univ : Finset (Polynomial params)).filter (fun g => g v = b))
                (ψ := strategy.state) (A := E a) (C := E a) (R := R)
                (D := P b) (B := Y)]
      _ = ∑ b : Fq params,
            ∑ g ∈ (Finset.univ : Finset (Polynomial params)).filter (fun g => g v = b),
              ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    rightTensor (ι₁ := ι) (P b)) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              rw [Finset.sum_comm]
      _ = ∑ b : Fq params,
            ∑ g ∈ (Finset.univ : Finset (Polynomial params)).filter (fun g => g v = b),
              ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                    rightTensor (ι₁ := ι) (P (g v))) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              refine Finset.sum_congr rfl ?_
              intro g hg
              have hgv : g v = b := (Finset.mem_filter.mp hg).2
              rw [hgv]
      _ = ∑ g : Polynomial params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                rightTensor (ι₁ := ι) (P (g v))) := by
              simpa using
                (Finset.sum_fiberwise (Finset.univ : Finset (Polynomial params))
                  (fun g : Polynomial params => g v)
                  (fun g : Polynomial params =>
                    ∑ a : Fq params,
                      ev strategy.state
                        (leftTensor (ι₂ := ι) (((E a * Y g * E a) * R)) *
                          rightTensor (ι₁ := ι) (P (g v)))))
  simpa [E, Y, P, R, evaluatedSlicePhaseTwoQuestionDefect,
    evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedSlicePointMeas,
    evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess, pointHeight_appendPoint, truncatePoint_appendPoint, Parameters.next,
    mul_assoc] using hcollapse

/-- Pointwise algebra for the phase-2 subtraction.

After expanding `totalSandwichFamily`, the inserted summand has the extra factor
`G^y.total` on the left register.  This lemma rewrites the difference with the
removed summand as the negative defect, using the noncommutative identity
`S * T - S = -(S * (1 - T))`. -/
lemma evaluatedSlice_phaseTwo_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b)) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            ((((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
              (1 - (G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
  have htotal := evaluatedPointFamily_total_eq_G_total params family G hG q.2
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b) *
      ((evaluatedSliceFirstFactor params family q).outcome a)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.2)).total
  let P : MIPStarRE.Quantum.Op ι := (evaluatedSlicePointMeas params strategy q.2).outcome b
  change
    ev strategy.state
        (leftTensor (ι₂ := ι) S *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
      ev strategy.state
        (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state
        (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [show ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b) =
        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P by
          simp [MIPStarRE.LDT.Preliminaries.totalSandwichFamily, htotal, T, P]]
  rw [← ev_sub]
  have hop :
      leftTensor (ι₂ := ι) S * (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P) -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P =
        -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
    calc
      leftTensor (ι₂ := ι) S * (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P) -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P
        = (leftTensor (ι₂ := ι) S * leftTensor (ι₂ := ι) T) *
            rightTensor (ι₁ := ι) P -
            leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P := by
              rw [mul_assoc]
      _ = leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
            leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P := by
              rw [leftTensor_mul_leftTensor]
      _ = opTensor (S * T) P - opTensor S P := by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (S * T - S) P := by
              rw [MIPStarRE.LDT.opTensor_sub_left]
      _ = opTensor (-(S * (1 - T))) P := by
              have hs : S * T - S = -(S * (1 - T)) := by noncomm_ring
              rw [hs]
      _ = -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
              have hneg : opTensor (-(S * (1 - T))) P = -(opTensor (S * (1 - T)) P) := by
                simpa [opTensor] using
                  (Matrix.smul_kronecker (-1 : ℂ) (S * (1 - T)) P)
              rw [hneg]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
  rw [hop]
  simpa using
    (ev_scale strategy.state (-1)
      (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P))

/-- Average the pointwise phase-2 algebra over evaluated-slice questions.

This proves the advertised sign rewrite
`avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed = -avgOver 𝒟 questionDefect`.
It leaves only the finite marginalization from the question-level defect to the
one-dimensional `evaluatedSlicePhaseTwoStabilityDefect`. -/
lemma evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a)) *
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              (evaluatedSlicePointMeas params strategy) q.2).outcome b))
    let removed : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a)) *
            rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b))
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q : EvaluatedSliceQuestion params =>
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a)) *
                ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                  (evaluatedPointFamily params family)
                  (evaluatedSlicePointMeas params strategy) q.2).outcome b))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q : EvaluatedSliceQuestion params =>
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a)) *
                rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q : EvaluatedSliceQuestion params =>
              (∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.2).outcome b))) -
              (∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a)) *
                    rightTensor (ι₁ := ι)
                        ((evaluatedSlicePointMeas params strategy q.2).outcome b)))) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => -evaluatedSlicePhaseTwoQuestionDefect params strategy family G q) := by
            apply avgOver_congr
            intro q
            calc
              (∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.2).outcome b))) -
                (∑ b : Fq params, ∑ a : Fq params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                        (((evaluatedSliceFirstFactor params family q).outcome a) *
                          ((evaluatedSliceSecondFactor params family q).outcome b) *
                          ((evaluatedSliceFirstFactor params family q).outcome a)) *
                      rightTensor (ι₁ := ι)
                        ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
                = ∑ b : Fq params, ∑ a : Fq params,
                    (ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a)) *
                        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                          (evaluatedPointFamily params family)
                          (evaluatedSlicePointMeas params strategy) q.2).outcome b)) -
                    ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a)) *
                        rightTensor (ι₁ := ι)
                        ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
                    simp [Finset.sum_sub_distrib]
              _ = ∑ b : Fq params, ∑ a : Fq params,
                    -ev strategy.state
                      (leftTensor (ι₂ := ι)
                          ((((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a)) *
                            (1 - (G (pointHeight params q.2)).total)) *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    exact evaluatedSlice_phaseTwo_term_diff params strategy family G hG q a b
              _ = -evaluatedSlicePhaseTwoQuestionDefect params strategy family G q := by
                    simp [evaluatedSlicePhaseTwoQuestionDefect]
    _ = -avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
            simp [avgOver]

/-- Exact finite reindexing identity for the phase-2 scalar bridge.

Paper origin: `references/ldt-paper/commutativity-G.tex:60-83`, the finite
averaging and reindexing step leading to the scalar `eq:add-an-a` bridge.

This statement contains no analytic estimate.  It says that the question-level
phase-2 defect averages to the one-dimensional scalar defect bounded by
`gCommStability_scalar`.  The proof is only finite marginalization and fiber
bookkeeping: decompose the second sampled point as `(v,y)`, collapse the
postprocessing fibers, and average the first sampled point into
`gCommStabilityR`. -/
lemma evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
    avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
  classical
  let defect := evaluatedSlicePhaseTwoQuestionDefect params strategy family G
  have hprod :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params)) defect =
      avgOver (uniformDistribution (Point params.next))
        (fun q2 => avgOver (uniformDistribution (Point params.next))
          (fun q1 => defect (q1, q2))) := by
    calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params)) defect =
          avgOver (uniformDistribution (Point params.next × Point params.next))
            (fun qq => defect qq) := by
            rfl
      _ = avgOver (uniformDistribution (Point params.next × Point params.next))
            (fun qq => defect (qq.2, qq.1)) := by
            simpa using
              (avgOver_uniform_equiv
                (e := Equiv.prodComm (Point params.next) (Point params.next))
                (f := fun qq : Point params.next × Point params.next => defect qq))
      _ = avgOver (uniformDistribution (Point params.next))
            (fun q2 => avgOver (uniformDistribution (Point params.next))
              (fun q1 => defect (q1, q2))) := by
            simpa using
              (avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
                (f := fun q2 q1 => defect (q1, q2)))
  have hdecomposeSecond :
      avgOver (uniformDistribution (Point params.next))
        (fun q2 => avgOver (uniformDistribution (Point params.next))
          (fun q1 => defect (q1, q2))) =
      avgOver (uniformDistribution (Fq params))
        (fun y => avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, appendPoint params v y)))) := by
    simpa using
      (avgOver_uniform_pointNext_decompose (params := params)
        (f := fun q2 => avgOver (uniformDistribution (Point params.next))
          (fun q1 => defect (q1, q2))))
  have hbody :
      ∀ y : Fq params,
        avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, appendPoint params v y))) =
        evaluatedSlicePhaseTwoStabilityDefect params strategy family G y := by
    intro y
    let Ffun : Point params.next → Polynomial params → Fq params → MIPStarRE.Quantum.Op ι :=
      fun q1 g a =>
        (evaluatedPointFamily params family q1).outcome a *
          ((family.meas y).toSubMeas.outcome g) *
          (evaluatedPointFamily params family q1).outcome a
    let Pfun : Polynomial params → Point params → MIPStarRE.Quantum.Op ι :=
      fun g v => (strategy.pointMeasurement (appendPoint params v y)).outcome (g v)
    let R : MIPStarRE.Quantum.Op ι := 1 - (G y).total
    have hFavg :
        ∀ g : Polynomial params,
          averageOperatorOverDistribution (uniformDistribution (Point params.next))
            (fun q1 => ∑ a : Fq params, Ffun q1 g a) =
          (gCommStabilityR params family y).outcome g := by
      intro g
      unfold gCommStabilityR averageIdxSubMeas
      refine averageOperatorOverDistribution_congr _ _ _ (fun q1 => ?_)
      rw [postprocess_sandwichByOuter_prod_snd_outcome]
    have hPavg :
        ∀ g : Polynomial params,
          averageOperatorOverDistribution (uniformDistribution (Point params))
            (fun v => Pfun g v) =
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g := by
      intro g
      rfl
    calc
      avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => defect (q1, appendPoint params v y))) =
        avgOver (uniformDistribution (Point params))
          (fun v => avgOver (uniformDistribution (Point params.next))
            (fun q1 => ∑ g : Polynomial params, ∑ a : Fq params,
              ev strategy.state
                (leftTensor (ι₂ := ι) (Ffun q1 g a * R) *
                  rightTensor (ι₁ := ι) (Pfun g v)))) := by
          apply avgOver_congr
          intro v
          apply avgOver_congr
          intro q1
          simpa [defect, Ffun, Pfun, R] using
            evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
              params strategy family G q1 v y
      _ = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q1 => ∑ a : Fq params, Ffun q1 g a)) * R) *
                rightTensor (ι₁ := ι)
                  (averageOperatorOverDistribution (uniformDistribution (Point params))
                    (fun v => Pfun g v))) := by
          exact avgOver_avgOver_phaseTwo_linear
            (𝒟Q := uniformDistribution (Point params.next))
            (𝒟V := uniformDistribution (Point params))
            (ψ := strategy.state) (F := Ffun) (P := Pfun) (R := R)
      _ = evaluatedSlicePhaseTwoStabilityDefect params strategy family G y := by
          unfold evaluatedSlicePhaseTwoStabilityDefect
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [hFavg g, hPavg g]
  rw [hprod, hdecomposeSecond]
  apply avgOver_congr
  intro y
  exact hbody y

end MIPStarRE.LDT.Commutativity
