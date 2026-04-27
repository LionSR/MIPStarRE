import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChain
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Phase67Residual
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Commutativity.GCommStability.Scalar

/-!
# Processed `G` scalar approximation

This file assembles the paper-faithful evaluated-slice scalar chain used in the proof of
`lem:comm-data-processed-g`.  The heavier endpoint and normalization lemmas are imported from
`ScalarApproximation.PaperChain` so this final assembly can reuse cached proofs.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Scalar approximation chain (proof of `lem:comm-data-processed-g`)

The paper's proof (`commutativity-G.tex`, lines 72–131) converts
`E[∑ ABAB]` into `E[∑ ABA]` through a ten-step scalar chain.
In the Lean development, this argument is packaged into a single bound
lemma (`evaluatedSlice_scalar_chain_bound`), and the proof is organized
conceptually into the following four phases.

**Phase 1** (eq:gcom8 → eq:gcom9): insert Bob's measurement and apply
`clm:g-comm-stability` to remove trailing `G^y`.
Error: `2√ζ + √ζ`.

**Phase 2** (eq:gcom9 → eq:gcom10): insert Bob's second measurement,
swap via `commutativityPoints`, then apply the boundedness part of
`clm:g-comm-stability2` to remove trailing `G^x`.  The paper states
`clm:g-comm-stability2` with an additional internal `6√(γ(m+1))` point-swap
loss; the local `hphase5paper` step below keeps the paper's combined
`√ζ + 6√(γ(m+1))` contribution explicit.
Error: `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`.

**Phase 3** (eq:gcom10 → eq:gonna-cite-this-in-just-a-bit): reverse the
`eq:add-an-a` insertions using projectivity.
Error: `2√ζ + 2√ζ`.

**Phase 4** (eq:gonna-cite-this-in-just-a-bit → BAB = ABA): apply postprocessed
self-consistency twice.
Error: `√ζ + √ζ`.

Total: `12√ζ + 12√(γ(m+1))`. Then `2 * total ≤ 48m(√γ + √ζ)`. -/

/-- The scalar defect controlled by `gCommStability_scalar` after averaging out
all evaluated-slice variables except the second slice height `y`.

This is the paper's boundedness witness term for `clm:g-comm-stability`: for a
fixed `y`, `gCommStabilityR params family y` averages the left-register sandwich
`G^{u,x}_a G^y_g G^{u,x}_a`, while
`IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g` averages the
right-register point answer `A^{v,y}_{g(v)}` over the tail point `v`. -/
private noncomputable def evaluatedSlicePhaseTwoStabilityDefect
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
private lemma evaluatedSlice_phaseTwo_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  simpa [evaluatedSlicePhaseTwoStabilityDefect] using
    (gCommStability_scalar params strategy zeta hnorm family G hG hbound)

/-- The still-unmarginalized phase-2 defect at a sampled evaluated-slice question.

This is the exact question-level term obtained after expanding
`totalSandwichFamily` and using
`S * G^y.total - S = -S * (1 - G^y.total)` for the left-register sandwich `S`.
The remaining reindexing residual averages this term to
`evaluatedSlicePhaseTwoStabilityDefect`. -/
private noncomputable def evaluatedSlicePhaseTwoQuestionDefect
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
private lemma postprocess_sandwichByOuter_prod_snd_outcome
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
private lemma avgOver_avgOver_phaseTwo_linear
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
private lemma evaluatedSlicePhaseTwoQuestionDefect_append_eq_sum_poly
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
private lemma evaluatedSlice_phaseTwo_term_diff
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
private lemma evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
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

/-- Exact finite reindexing residual for the phase-2 scalar bridge.

This statement contains no analytic estimate.  It says that the question-level
phase-2 defect averages to the one-dimensional scalar defect bounded by
`gCommStability_scalar`.  Proving it amounts to the marginalization/fiber
bookkeeping outlined in the docstring of
`evaluatedSlice_phaseTwo_stability_defect_bound`, with
`avgOver_uniform_pointNext_decompose` as the first marginalization step. -/
private def evaluatedSlicePhaseTwoReindexingResidual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) : Prop :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
    avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)

/-- The scalar defect controlled by `gCommStabilityTwo_scalar` after averaging out
all evaluated-slice variables except the slice height `x`.

This is the paper's boundedness witness term for `clm:g-comm-stability2`: for a
fixed `x`, `gCommStabilityTwoR params family G x` averages the left-register
sandwich `G^{v,y}_b G^x_g G^{v,y}_b`, while
`IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g` averages the
right-register point answer `A^{u,x}_{g(u)}` over the tail point `u`. -/
private noncomputable def evaluatedSlicePhaseFiveStabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))

/-- Direct `√ζ` control of the phase-5 stability defect.

No `γ` term is folded into this bound: the `6√(γ(m+1))` contribution in the
paper's lines 86--93 is the separate point-measurement swap step.  Once the
phase-5 scalar difference is reindexed into the defect above, the boundedness
hypothesis gives the displayed `√ζ` estimate exactly. -/
private lemma evaluatedSlice_phaseFive_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseFiveStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  simpa [evaluatedSlicePhaseFiveStabilityDefect] using
    (gCommStabilityTwo_scalar params strategy zeta hnorm family G hG hbound)

/-- The still-unmarginalized phase-5 defect at an evaluated-slice question.

This is the phase-5 analogue of `evaluatedSlicePhaseTwoQuestionDefect`: after
expanding `totalSandwichFamily`, the difference between the inserted `G^x.total`
summand and the removed summand is the negative of this defect. -/
private noncomputable def evaluatedSlicePhaseFiveQuestionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a))

/-- Pointwise algebra for the phase-5 subtraction.

After expanding `totalSandwichFamily`, the inserted summand has an extra
`G^x.total` factor on the left register.  This rewrites the difference with the
removed summand as the negative phase-5 question defect. -/
private lemma evaluatedSlice_phaseFive_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a)) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            ((((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a)) := by
  have htotal := evaluatedPointFamily_total_eq_G_total params family G hG q.1
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceSecondFactor params family q).outcome b) *
      ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let P : MIPStarRE.Quantum.Op ι := (evaluatedSlicePointMeas params strategy q.1).outcome a
  change
    ev strategy.state
        (leftTensor (ι₂ := ι) S *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
      ev strategy.state
        (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state
        (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [show ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a) =
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

/-- Average the pointwise phase-5 algebra over evaluated-slice questions. -/
private lemma evaluatedSlice_phaseFive_avg_diff_eq_neg_questionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b)) *
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              (evaluatedSlicePointMeas params strategy) q.1).outcome a))
    let removed : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFiveRemoved params strategy family
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q : EvaluatedSliceQuestion params =>
          ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b)) *
                ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                  (evaluatedPointFamily params family)
                  (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveRemoved params strategy family)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q : EvaluatedSliceQuestion params =>
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
              evaluatedSlicePhaseFiveRemoved params strategy family q) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => -evaluatedSlicePhaseFiveQuestionDefect params strategy family G q) := by
            apply avgOver_congr
            intro q
            calc
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
                evaluatedSlicePhaseFiveRemoved params strategy family q
                = ∑ a : Fq params, ∑ b : Fq params,
                    (ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                          (evaluatedPointFamily params family)
                          (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
                    ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
                    simp [evaluatedSlicePhaseFiveRemoved, Finset.sum_sub_distrib]
              _ = ∑ a : Fq params, ∑ b : Fq params,
                    -ev strategy.state
                      (leftTensor (ι₂ := ι)
                          ((((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                            (1 - (G (pointHeight params q.1)).total)) *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a)) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    exact evaluatedSlice_phaseFive_term_diff params strategy family G hG q a b
              _ = -evaluatedSlicePhaseFiveQuestionDefect params strategy family G q := by
                    simp [evaluatedSlicePhaseFiveQuestionDefect]
    _ = -avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) := by
            simp [avgOver]

/-- Collapse the postprocessing fiber appearing in the phase-5 reindexing step.

For a fixed tail point `u`, the evaluated outcome `a` indexes exactly the fiber
`{g | g u = a}`.  Linearity of tensor placement and expectation lets us expand
the left-register postprocessed sum before applying `Finset.sum_fiberwise`. -/
private lemma phaseFive_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (u : Point params)
    (B T : MIPStarRE.Quantum.Op ι)
    (Gx : SubMeas (Polynomial params) ι)
    (P : Fq params → MIPStarRE.Quantum.Op ι) :
    (∑ a : Fq params,
      ev ψ
        (leftTensor (ι₂ := ι)
            (((B * (∑ g ∈ Finset.univ.filter
                    (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
          rightTensor (ι₁ := ι) (P a))) =
      ∑ g : Polynomial params,
        ev ψ
          (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
            rightTensor (ι₁ := ι) (P (g u))) := by
  classical
  calc
    ∑ a : Fq params,
        ev ψ
          (leftTensor (ι₂ := ι)
              (((B * (∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
            rightTensor (ι₁ := ι) (P a))
      = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                rightTensor (ι₁ := ι) (P a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← ev_finset_sum ψ
            (Finset.univ.filter (fun g : Polynomial params => g u = a))]
          congr 1
          calc
            leftTensor (ι₂ := ι)
                  (((B * (∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
                    rightTensor (ι₁ := ι) (P a)
              = leftTensor (ι₂ := ι)
                  (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                    ((B * Gx.outcome g * B) * T)) *
                    rightTensor (ι₁ := ι) (P a) := by
                    congr 1
                    congr 1
                    symm
                    calc
                      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                          ((B * Gx.outcome g * B) * T)
                        = (∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            B * Gx.outcome g * B) * T := by
                            rw [Finset.sum_mul]
                      _ = ((∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            B * Gx.outcome g) * B) * T := by
                            congr 1
                            rw [Finset.sum_mul]
                      _ = (((B * (∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            Gx.outcome g)) * B) * T) := by
                            rw [Matrix.mul_sum]
            _ = (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                  leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T))) *
                    rightTensor (ι₁ := ι) (P a) := by
                    rw [leftTensor_finset_sum (ι₂ := ι)
                      (Finset.univ.filter (fun g : Polynomial params => g u = a))]
            _ = (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                  rightTensor (ι₁ := ι) (P a)) := by
                    rw [Finset.sum_mul]
    _ = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                rightTensor (ι₁ := ι) (P (g u))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro g hg
          have hgu : g u = a := (Finset.mem_filter.mp hg).2
          simp [hgu]
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
              rightTensor (ι₁ := ι) (P (g u))) := by
          simpa using
            (Finset.sum_fiberwise Finset.univ (fun g : Polynomial params => g u)
              (fun g : Polynomial params =>
                ev ψ
                  (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                    rightTensor (ι₁ := ι) (P (g u)))))


/-- Postprocessing the sandwich `B_b G_g B_b` by the polynomial coordinate sums
over the evaluated outcome `b`. -/
private lemma postprocess_sandwichByOuterSubMeas_snd_outcome
    (params : Parameters) [FieldModel params.q]
    (B : SubMeas (Fq params) ι)
    (Gx : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    (postprocess (sandwichByOuterSubMeas B Gx) Prod.snd).outcome g =
      ∑ b : Fq params, B.outcome b * Gx.outcome g * B.outcome b := by
  classical
  simp [postprocess, sandwichByOuterSubMeas, Finset.sum_filter, Fintype.sum_prod_type]

/-- Real scalar multiplication pulls out of expectations. -/
private lemma ev_smul_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (c : Error) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ (c • X) = c * ev ψ X := by
  simpa using ev_scale ψ c X

/-- Move the first finite sum past the third while keeping the second and fourth fixed. -/
private lemma phaseFive_sum_comm_four
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : γ → β → α → δ → Error) :
    (∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ, f g u a b) =
      ∑ a : α, ∑ u : β, ∑ g : γ, ∑ b : δ, f g u a b := by
  calc
    (∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ, f g u a b)
        = ∑ g : γ, ∑ a : α, ∑ u : β, ∑ b : δ, f g u a b := by
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ g : γ, ∑ u : β, ∑ b : δ, f g u a b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ u : β, ∑ g : γ, ∑ b : δ, f g u a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.sum_comm]

/-- Expand expectation against uniformly averaged left and right tensor factors. -/
private lemma phaseFive_bilinear_expand
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (ψ : QuantumState (ι × ι)) (c d : Error)
    (L : α → γ → δ → MIPStarRE.Quantum.Op ι)
    (R : β → γ → MIPStarRE.Quantum.Op ι) :
    (∑ g : γ,
      ev ψ (leftTensor (ι₂ := ι) (∑ a : α, c • ∑ b : δ, L a g b) *
        rightTensor (ι₁ := ι) (∑ u : β, d • R u g))) =
      ∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ,
        c * (d * ev ψ (leftTensor (ι₂ := ι) (L a g b) *
          rightTensor (ι₁ := ι) (R u g))) := by
  simp [opTensor_sum_left_univ, opTensor_sum_right_univ, opTensor_smul_left_error,
    opTensor_smul_right_error, opTensor_mul, one_mul, mul_one, ev_sum, ev_smul_error,
    Finset.smul_sum, smul_smul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  ring_nf

set_option linter.flexible false in
-- This finite-fiber expansion deliberately uses a broad `simp` to expose the
-- postprocessed slice outcome before applying the explicit fiber-collapse lemma.
/-- Expand the question-level phase-5 defect after decomposing the first point as `(u, x)`. -/
private lemma evaluatedSlicePhaseFiveQuestionDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFiveQuestionDefect params strategy family G (appendPoint params u x, vy) =
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((((evaluatedPointFamily params family vy).outcome b) *
                (G x).outcome g *
                ((evaluatedPointFamily params family vy).outcome b)) *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                (g u))) := by
  classical
  calc
    evaluatedSlicePhaseFiveQuestionDefect params strategy family G (appendPoint params u x, vy)
        = ∑ b : Fq params, ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))) := by
          simp [evaluatedSlicePhaseFiveQuestionDefect, evaluatedSliceFirstFactor,
            evaluatedSliceSecondFactor, evaluatedSlicePointMeas, pointHeight_appendPoint,
            evaluatedPointFamily_appendPoint_outcome, hG]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          have hfiber :=
            phaseFive_fiber_sum_ev (ι := ι) params strategy.state u
              ((evaluatedPointFamily params family vy).outcome b)
              (1 - (family.meas x).toSubMeas.total)
              ((family.meas x).toSubMeas)
              (fun a : Fq params =>
                (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome a)
          simpa using hfiber
    _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))) := by
          rw [Finset.sum_comm]

/-- Expand the stability defect into the same `(vy, u, g, b)` normal form. -/
private lemma evaluatedSlicePhaseFiveStabilityDefect_expansion_at
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    evaluatedSlicePhaseFiveStabilityDefect params strategy family G x =
      avgOver (uniformDistribution (Point params.next)) (fun vy =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))))) := by
  classical
  let cV : Error := 1 / (Fintype.card (Point params.next) : Error)
  let cU : Error := 1 / (Fintype.card (Point params) : Error)
  let L : Point params.next → Polynomial params → Fq params → MIPStarRE.Quantum.Op ι :=
    fun vy g b =>
      (((evaluatedPointFamily params family vy).outcome b) * (G x).outcome g *
        ((evaluatedPointFamily params family vy).outcome b)) * (1 - (G x).total)
  let R : Point params → Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun u g => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)
  calc
    evaluatedSlicePhaseFiveStabilityDefect params strategy family G x
        = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (∑ vy : Point params.next, cV • ∑ b : Fq params, L vy g b) *
                rightTensor (ι₁ := ι) (∑ u : Point params, cU • R u g)) := by
          simp [evaluatedSlicePhaseFiveStabilityDefect, gCommStabilityTwoR,
            averageIdxSubMeas, averageOperatorOverDistribution,
            postprocess_sandwichByOuterSubMeas_snd_outcome,
            IdxPolyFamily.averagedSlicePointEvaluationOperator, cV, cU, L, R,
            uniformDistribution, Finset.sum_mul, mul_assoc]
    _ = ∑ g : Polynomial params, ∑ u : Point params, ∑ vy : Point params.next,
          ∑ b : Fq params,
            cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))) := by
          exact phaseFive_bilinear_expand (ι := ι) strategy.state cV cU L R
    _ = ∑ vy : Point params.next, ∑ u : Point params, ∑ g : Polynomial params,
          ∑ b : Fq params,
            cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))) := by
          exact phaseFive_sum_comm_four (α := Point params.next) (β := Point params)
            (γ := Polynomial params) (δ := Fq params)
            (fun g u vy b => cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))))
    _ = avgOver (uniformDistribution (Point params.next)) (fun vy =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))))) := by
          simp [avgOver, uniformDistribution, cV, cU, L, R, Finset.mul_sum, mul_assoc]

/-- Exact finite reindexing residual for the phase-5 scalar bridge. -/
private lemma evaluatedSlice_phaseFive_reindex_to_stability_defect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) =
      avgOver (uniformDistribution (Fq params))
        (evaluatedSlicePhaseFiveStabilityDefect params strategy family G) := by
  classical
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveQuestionDefect params strategy family G)
        = avgOver (uniformDistribution (Point params.next)) (fun ux =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFiveQuestionDefect params strategy family G (ux, vy))) := by
          simpa using
            (avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
              (f := fun ux vy =>
                evaluatedSlicePhaseFiveQuestionDefect params strategy family G (ux, vy)))
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFiveQuestionDefect params strategy family G
                (appendPoint params u x, vy)))) := by
          rw [avgOver_uniform_pointNext_decompose params]
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u)))))) := by
          apply avgOver_congr
          intro x
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro vy
          exact evaluatedSlicePhaseFiveQuestionDefect_appendPoint_expansion
            params strategy family G hG x u vy
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params.next)) (fun vy =>
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u)))))) := by
          apply avgOver_congr
          intro x
          exact avgOver_uniform_comm (α := Point params) (β := Point params.next)
            (fun u vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u))))
    _ = avgOver (uniformDistribution (Fq params))
          (evaluatedSlicePhaseFiveStabilityDefect params strategy family G) := by
          apply avgOver_congr
          intro x
          exact (evaluatedSlicePhaseFiveStabilityDefect_expansion_at
            params strategy family G x).symm


/- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal
    to the paper's `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of
    `gCommStabilityTwo_scalar` (this is the scalar part of `hphase5paper` below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/
set_option maxHeartbeats 5000000 in
-- The final scalar-chain assembly unfolds many named phase endpoints and closes
-- the accumulated real-arithmetic budget; the larger cap keeps that calculation local.
private lemma evaluatedSlice_scalar_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab)) ≤
      commDataProcessedGError params gamma zeta := by
  -- Paper reference: commutativity-G.tex, proof of lem:comm-data-processed-g,
  -- equations (eq:gcom8) through the final displayed error estimate.
  -- Each step uses closenessOfIP, easyApproxFromApproxDelta, or the
  -- stability claims (clm:g-comm-stability, clm:g-comm-stability2).
  -- The algebraic qSDDOp expansions and stability families are defined
  -- in Commutativity/Defs.lean; the Cauchy-Schwarz bridges are in
  -- Preliminaries/CauchySchwarz.lean.
  have h𝒟 :
      ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
        (uniformDistribution (EvaluatedSliceQuestion params)).weight q ≤ 1 := by
    simpa using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hpostSSC_fst :=
    evaluatedPointSelfConsistency_fst params strategy family zeta _hpostSSC
  have hpostSSC_snd :=
    evaluatedPointSelfConsistency_snd params strategy family zeta _hpostSSC
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let avgABAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABABTerm params strategy family q ab
  let avgABA : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABATerm params strategy family q ab
  let avgBABA : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABATerm params strategy family q ab
  let avgBAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABTerm params strategy family q ab
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    fun u => by
      simpa [Parameters.next] using (strategy.pointMeasurement u).toMeasurement
  have hcons_swapped :=
    evaluatedPointFamily_pointConsistency_swapped params strategy family zeta _hcons
  have hconsSub :=
    MIPStarRE.LDT.Preliminaries.consSubMeas
      strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      pointMeas
      zeta
      hcons_swapped
  have hcombined_snd :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.2)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.2))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, evaluatedPointFamilyLeft] using
      (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  have hcombined_fst :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.1)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.1))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, evaluatedPointFamilyLeft] using
      (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  let phase1Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b))
  let phase3Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  let phase2Removed : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b))
  -- Paper line 86: insert the first-coordinate point measurement after `gcom9`.
  -- Unfolding `totalSandwichFamily`, this is the average of
  -- `G^{u,x}_a G^{v,y}_b G^x ⊗ A^{v,y}_b A^{u,x}_a`.
  let phase3PaperInserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  -- Paper line 87: swap the two right-register point measurements.
  let phase4PaperSwapped : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
  -- Paper line 87 after removing the trailing first-slice total `G^x`.
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  -- Paper lines 101--119 endpoints for the reverse insertions and tail.
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseEightTailRight params strategy family
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 :
      |avgOver 𝒟 avgABAB - avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgABAB, phase1Inserted] using
      evaluatedSlice_phaseOne_insert_bound
        params strategy zeta _hnorm family hcombined_snd
  -- Phase 2: remove the trailing `G^y` from the phase-1 inserted term via the
  -- direct boundedness estimate `gCommStability_scalar`.
  -- The analytic part is closed by `evaluatedSlice_phaseTwo_stability_defect_bound`,
  -- the sign/algebra expansion is proved by
  -- `evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect`, and the finite
  -- marginalization below identifies the question-level defect with
  -- `evaluatedSlicePhaseTwoStabilityDefect`: decompose the sampled second point as
  -- `(v,y)`, collapse the postprocessing fibers `∑_b ∑_{g : g(v)=b}` to `∑_g`,
  -- then average the first sampled point into `gCommStabilityR`.
  have hphase2 :
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    have hdefect :=
      evaluatedSlice_phaseTwo_stability_defect_bound
        params strategy zeta _hnorm family G _hG _hbound
    have hsign :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
      simpa [𝒟, phase1Inserted, phase2Removed] using
        evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
          params strategy family G _hG
    have hbridge :
        evaluatedSlicePhaseTwoReindexingResidual params strategy family G := by
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
              simp [evaluatedSlicePhaseTwoStabilityDefect, gCommStabilityR,
                IdxPolyFamily.averagedSlicePointEvaluationOperator, averageIdxSubMeas,
                averageOperatorOverDistribution, evaluatedPointFamily,
                IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
                postprocess_sandwichByOuter_prod_snd_outcome, Ffun, Pfun, R,
                Parameters.next]
      unfold evaluatedSlicePhaseTwoReindexingResidual
      rw [hprod, hdecomposeSecond]
      apply avgOver_congr
      intro y
      exact hbody y
    have hrewrite :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver (uniformDistribution (Fq params))
            (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      calc
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed
            = -avgOver 𝒟
                (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := hsign
        _ = -avgOver (uniformDistribution (Fq params))
                (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
              rw [hbridge]
    calc
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed|
          = |-(avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G))| := by
              rw [hrewrite]
      _ = |avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| := by
              rw [abs_neg]
      _ ≤ Real.sqrt zeta := hdefect
  -- Paper line 86, first approximation: insert the first-coordinate
  -- `G^x \otimes A^{u,x}_a` endpoint into the post-`gcom9` expression.
  have hphase3paper :
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted| ≤
        2 * Real.sqrt zeta := by
    let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
    let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a =>
        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1).outcome a)
    let C : EvaluatedSliceQuestion params → Fq params → Fq params →
        MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a b =>
        leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)
    have hAB :
        avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
      simpa [𝒟, A, B, qSDD, evaluatedSliceFirstFactor, evaluatedPointFamily,
        evaluatedSlicePointMeas, pointMeas, Parameters.next, IdxSubMeas.liftLeft,
        SubMeas.liftLeft] using hcombined_fst.squaredDistanceBound
    have hC :
        ∀ q, ∑ a : Fq params, (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
      intro q
      simpa [C, evaluatedSlicePointMeas, Parameters.next] using
        (leftRightTensor_prefix_pointMeasurement_normalization
          (A := evaluatedSliceFirstFactor params family q)
          (B := evaluatedSliceSecondFactor params family q)
          (R := strategy.pointMeasurement q.2))
    have hremoved :
        avgOver 𝒟 phase2Removed =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) := by
      apply avgOver_congr
      intro q
      dsimp [phase2Removed, A, C]
      rw [Finset.sum_comm]
      simp [opTensor_mul, mul_assoc]
    have hinserted :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a)) := by
      rfl
    have hclose :=
      MIPStarRE.LDT.Preliminaries.closenessOfIP
        strategy.state _hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
    calc
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted|
          = |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * A q a)) -
            avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * B q a))| := by
              rw [hremoved, hinserted]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
            norm_num
  -- Paper line 87: commute the two right-register point measurements.
  have hphase4paper :
      |avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase4PaperSwapped| ≤
        6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
        MIPStarRE.Quantum.Op (ι × ι) := fun q ab =>
      leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
          ((evaluatedSliceSecondFactor params family q).outcome ab.2) *
          (evaluatedSliceFirstFactor params family q).total)
    have hC :
        ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
      intro q
      simpa [C] using
        (leftTensor_prefix_total_normalization
          (A := evaluatedSliceFirstFactor params family q)
          (B := evaluatedSliceSecondFactor params family q)
          (T := (evaluatedSliceFirstFactor params family q).total)
          (hT_nonneg := (evaluatedSliceFirstFactor params family q).total_nonneg)
          (hT_le_one := (evaluatedSliceFirstFactor params family q).total_le_one))
    have hphase3_norm :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
      apply avgOver_congr
      intro q
      calc
        phase3PaperInserted q =
            ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                (C q (a, b) *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
              dsimp [phase3PaperInserted, C]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              congr 1
              simp [MIPStarRE.LDT.Preliminaries.totalSandwichFamily,
                evaluatedSliceFirstFactor, opTensor_mul, mul_assoc]
        _ = ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))) := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                  ev strategy.state
                    (C q (a, b) *
                      rightTensor (ι₁ := ι)
                        (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
    have hphase4_norm :
        avgOver 𝒟 phase4PaperSwapped =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
      apply avgOver_congr
      intro q
      dsimp [phase4PaperSwapped, C]
      simpa using
        (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  (evaluatedSliceFirstFactor params family q).total) *
              rightTensor (ι₁ := ι)
                (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                  ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
    have hswap :=
      evaluatedSlice_phaseFour_pointSwap_right_bound
        params strategy eps delta gamma _hnorm _hgood C hC
    calc
      |avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase4PaperSwapped|
          = |avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) -
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                      ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2))))| := by
              rw [hphase3_norm, hphase4_norm]
      _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
              simpa [𝒟, C] using hswap
  -- Paper phase five: remove the trailing `G^x` total from the line-87 endpoint.
  -- The ordered defect is first swapped on the right register, then reindexed to
  -- `gCommStabilityTwoRawScalarDefect`, whose average is controlled by the new
  -- raw scalar stability theorem.
  have hphase5paper :
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved| ≤
        Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let orderedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G
    let swappedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
    have hsign :
        avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved =
          -avgOver 𝒟 orderedDefect := by
      simpa [𝒟, phase4PaperSwapped, phase5PaperRemoved, orderedDefect] using
        evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
          params strategy family G _hG
    have hraw : |avgOver 𝒟 swappedDefect| ≤ Real.sqrt zeta := by
      have hraw0 :=
        gCommStabilityTwo_raw_scalar
          params strategy zeta _hnorm family G _hG _hbound
      have hreindex :
          avgOver 𝒟 swappedDefect =
            avgOver (uniformDistribution (Fq params))
              (gCommStabilityTwoRawScalarDefect params strategy family G) := by
        simpa [𝒟, swappedDefect] using
          evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
            params strategy family G _hG
      calc
        |avgOver 𝒟 swappedDefect|
            = |avgOver (uniformDistribution (Fq params))
                (gCommStabilityTwoRawScalarDefect params strategy family G)| := by
              rw [hreindex]
        _ ≤ Real.sqrt zeta := hraw0
    have hswap_defect :
        |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q ab =>
        leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
            ((evaluatedSliceSecondFactor params family q).outcome ab.2) *
            (1 - (G (pointHeight params q.1)).total))
      have hC :
          ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
        intro q
        have hT_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) -
            (G (pointHeight params q.1)).total := by
          exact sub_nonneg.mpr (G (pointHeight params q.1)).total_le_one
        have hT_le_one : (1 : MIPStarRE.Quantum.Op ι) -
            (G (pointHeight params q.1)).total ≤ 1 := by
          simpa using
            (sub_le_self (1 : MIPStarRE.Quantum.Op ι)
              (G (pointHeight params q.1)).total_nonneg)
        simpa [C] using
          (leftTensor_prefix_total_normalization
            (A := evaluatedSliceFirstFactor params family q)
            (B := evaluatedSliceSecondFactor params family q)
            (T := (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total)
            (hT_nonneg := hT_nonneg)
            (hT_le_one := hT_le_one))
      have hord_norm :
          avgOver 𝒟 orderedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                      ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
        apply avgOver_congr
        intro q
        dsimp [orderedDefect, evaluatedSlicePhaseFivePaperOrderedDefect, C]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
      have hswap_norm :
          avgOver 𝒟 swappedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
        apply avgOver_congr
        intro q
        dsimp [swappedDefect, evaluatedSlicePhaseFivePaperSwappedDefect, C]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
      have hswap :=
        evaluatedSlice_phaseFour_pointSwap_right_bound
          params strategy eps delta gamma _hnorm _hgood C hC
      calc
        |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect|
            = |avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
                ev strategy.state
                  (C q ab *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                        ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) -
              avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
                ev strategy.state
                  (C q ab *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                        ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))))| := by
                rw [hord_norm, hswap_norm]
        _ = |avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
                ev strategy.state
                  (C q ab *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                        ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) -
              avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
                ev strategy.state
                  (C q ab *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                        ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2))))| := by
                rw [abs_sub_comm]
        _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
                simpa [𝒟, C] using hswap
    have hordered_abs :
        |avgOver 𝒟 orderedDefect| ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      calc
        |avgOver 𝒟 orderedDefect|
            = |avgOver 𝒟 orderedDefect - 0| := by simp
        _ ≤ |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| +
              |avgOver 𝒟 swappedDefect - 0| :=
                abs_sub_le (avgOver 𝒟 orderedDefect) (avgOver 𝒟 swappedDefect) 0
        _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) + Real.sqrt zeta := by
                exact add_le_add hswap_defect (by simpa using hraw)
        _ = Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
                ring
    calc
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved|
          = |-(avgOver 𝒟 orderedDefect)| := by
              rw [hsign]
      _ = |avgOver 𝒟 orderedDefect| := by rw [abs_neg]
      _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) :=
              hordered_abs
  -- Paper lines 99--104: reverse the two `eq:add-an-a` insertions.
  have hphase67paper :
      |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤
        4 * Real.sqrt zeta := by
    simpa [𝒟, phase5PaperRemoved, phase7GonnaCite] using
      evaluatedSlice_phaseSixSeven_reverse_bound
        params strategy zeta _hnorm family hcombined_fst hcombined_snd
  -- Paper line 117--118: first postprocessed self-consistency tail move.
  have htail8 :
      |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase7GonnaCite, phase8TailRight] using
      evaluatedSlice_phaseEight_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- Paper line 118--119: move that same second-coordinate factor back to the left.
  have htail9 :
      |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase8TailRight, avgBAB] using
      evaluatedSlice_phaseNine_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- Follow the paper chain from the `ABAB` term to the `BAB` term, then use the
  -- exact evaluated-slice swap identity `avgABA = avgBAB`.
  have hassemble :
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
        commDataProcessedGError params gamma zeta := by
    have hswap := evaluatedSliceCommutation_avg_swap_terms params strategy family
    have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA := hswap.1
    have hγζ_chain :
        avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB ≤
          12 * Real.sqrt zeta +
            12 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have h01 : avgOver 𝒟 phase1Inserted - avgOver 𝒟 avgABAB ≤
          2 * Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase1Inserted) (avgOver 𝒟 avgABAB)).symm ▸ hphase1)
      have h12 : avgOver 𝒟 phase2Removed - avgOver 𝒟 phase1Inserted ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase2Removed) (avgOver 𝒟 phase1Inserted)).symm ▸ hphase2)
      have h23 : avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase2Removed ≤
          2 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase3PaperInserted)
            (avgOver 𝒟 phase2Removed)).symm ▸ hphase3paper
        exact le_trans (le_abs_self _) h
      have h34 : avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase3PaperInserted ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase4PaperSwapped)
            (avgOver 𝒟 phase3PaperInserted)).symm ▸ hphase4paper
        exact le_trans (le_abs_self _) h
      have h45 : avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase4PaperSwapped ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase5PaperRemoved)
            (avgOver 𝒟 phase4PaperSwapped)).symm ▸ hphase5paper
        exact le_trans (le_abs_self _) h
      have h57 : avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase5PaperRemoved ≤
          4 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase7GonnaCite)
            (avgOver 𝒟 phase5PaperRemoved)).symm ▸ hphase67paper
        exact le_trans (le_abs_self _) h
      have h78 : avgOver 𝒟 phase8TailRight - avgOver 𝒟 phase7GonnaCite ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase8TailRight) (avgOver 𝒟 phase7GonnaCite)).symm ▸ htail8)
      have h89 : avgOver 𝒟 avgBAB - avgOver 𝒟 phase8TailRight ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 avgBAB) (avgOver 𝒟 phase8TailRight)).symm ▸ htail9)
      linarith
    have hmain_one :
        2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
          24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have hrw : avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB =
          avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB := by
        linarith
      rw [hrw]
      nlinarith
    have hgamma_nonneg : 0 ≤ gamma := by
      have hdfp : 0 ≤ strategy.diagonalFailureProbability := by
        unfold SymStrat.diagonalFailureProbability
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun j _ =>
            bipartiteConsError_nonneg strategy.state _ _ _)
      exact le_trans hdfp _hgood.diagonalLineTest
    have hzeta_nonneg : 0 ≤ zeta :=
      le_trans (sddError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)) _hpostSSC.squaredDistanceBound
    have hm : 1 ≤ (params.m : Error) := by exact_mod_cast params.hm
    have hsqrtn_le :
        Real.sqrt ((((params.m + 1 : ℕ)) : Error)) ≤ 2 * (params.m : Error) := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith
      · norm_num
        nlinarith
    have hgamma_tail :
        Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          2 * (params.m : Error) * Real.sqrt gamma := by
      rw [Real.sqrt_mul hgamma_nonneg]
      calc
        Real.sqrt gamma * Real.sqrt ((((params.m + 1 : ℕ)) : Error))
            ≤ Real.sqrt gamma * (2 * (params.m : Error)) := by
              exact mul_le_mul_of_nonneg_left hsqrtn_le (Real.sqrt_nonneg gamma)
        _ = 2 * (params.m : Error) * Real.sqrt gamma := by ring
    have htarget_sqrt :
        24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := by
      have hzpart : 24 * Real.sqrt zeta ≤
          48 * (params.m : Error) * Real.sqrt zeta := by
        have hzsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
        nlinarith
      have hgpart : 24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * Real.sqrt gamma := by
        nlinarith
      nlinarith
    calc
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB)
          ≤ 24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hmain_one
      _ ≤ 48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := htarget_sqrt
      _ = commDataProcessedGError params gamma zeta := by
        unfold commDataProcessedGError
        rw [Real.sqrt_eq_rpow gamma, Real.sqrt_eq_rpow zeta]
        rfl
  simpa [𝒟, avgABA, avgABAB] using hassemble

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family G gamma zeta := by
  have hpostSSC :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)
        zeta :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  refine
    { familyG := hG
      postprocessedPointConsistency := ?_
      postprocessedSelfConsistency := hpostSSC
      evaluatedSliceCommutation := by
        refine ⟨?_⟩
        rw [evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family]
        exact evaluatedSlice_scalar_chain_bound
          params strategy eps delta gamma zeta
          hnorm hgood family G hG hcons hself hbound hpostSSC }
  simpa [evaluatedPointFamily] using hcons.pointConsistency

end MIPStarRE.LDT.Commutativity
