import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Phase67Residual
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Commutativity.GCommStability

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma avgOver_uniform_pointNext_decompose
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params.next)) f =
      avgOver (uniformDistribution (Fq params))
        (fun x => avgOver (uniformDistribution (Point params))
          (fun u => f (appendPoint params u x))) := by
  have hprod :
      avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => f (appendPoint params u x))) =
        avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) := by
    simpa using
      (avgOver_uniform_prod (α := Fq params) (β := Point params)
        (f := fun x u => f (appendPoint params u x))).symm
  have hswap :
      avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) =
        avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := Equiv.prodComm (Fq params) (Point params))
        (f := fun xu : Fq params × Point params => f (appendPoint params xu.2 xu.1)))
  have hequiv :
      avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) =
        avgOver (uniformDistribution (Point params.next)) f := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := CommutativityPoints.pointNextEquiv params)
        (f := f)).symm
  calc
    avgOver (uniformDistribution (Point params.next)) f
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := CommutativityPoints.pointNextEquiv params)
                (f := f))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) := by
            simpa using hswap.symm
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => f (appendPoint params u x))) := by
            simpa using hprod.symm

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
loss; the local `hphase5` step below keeps that contribution split off and
uses only the `√ζ` boundedness estimate.
Error: `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`.

**Phase 3** (eq:gcom10 → eq:gonna-cite-this-in-just-a-bit): reverse the
`eq:add-an-a` insertions using projectivity.
Error: `2√ζ + 2√ζ`.

**Phase 4** (eq:gonna-cite-this-in-just-a-bit → BAB = ABA): apply postprocessed
self-consistency twice.
Error: `√ζ + √ζ`.

Total: `12√ζ + 12√(γ(m+1))`. Then `2 * total ≤ 48m(√γ + √ζ)`. -/

/-- Unfold the phase-2 stability relation into the scalar defect term used in
`eq:gcom9`.  This is copied locally from the overlap proof so that the scalar
chain can cite the averaged inequality directly. -/
private lemma evaluatedSlice_phaseTwo_stability_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta)) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ ah : StabilityOneOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.2)).total) *
                  (((evaluatedSliceSandwichRaw params strategy family q).outcome
                    (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                    (evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2))) *
                  (1 - (G (pointHeight params q.2)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) ≤
      Real.sqrt zeta := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.2)).total) *
                    (((evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                      (evaluatedSliceSandwichRaw params strategy family q).outcome
                        (ah.1, ah.2 (truncatePoint params q.2))) *
                    (1 - (G (pointHeight params q.2)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityOneLeft params strategy family G q)
              (commDataProcessedGStabilityOneRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityOne_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityOneLeft params strategy family G)
          (commDataProcessedGStabilityOneRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta := hstab

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

/-- The evaluated point family has the same total as the underlying slice
measurement `G` at the sampled height.

This unfolds `evaluatedPointFamily` as postprocessing of `family.meas y`; the
postprocessing total is unchanged, and `hG` identifies the slice with `G y`. -/
private lemma evaluatedPointFamily_total_eq_G_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (u : Point params.next) :
    ((evaluatedPointFamily params family u).total) =
      (G (pointHeight params u)).total := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess_total, hG]

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

private lemma leftTensor_mul_rightTensor_smul_left
    (c : Error) (A B : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) ((c : ℂ) • A) * rightTensor (ι₁ := ι) B =
      (c : ℂ) • (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.smul_kronecker (c : ℂ) A B

private lemma leftTensor_mul_rightTensor_smul_right
    (c : Error) (A B : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) ((c : ℂ) • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.kronecker_smul (c : ℂ) A B

private lemma leftTensor_mul_rightTensor_real_smul_left
    (c : Error) (A B : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (c • A) * rightTensor (ι₁ := ι) B =
      (c : ℂ) • (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_left c A B

private lemma leftTensor_mul_rightTensor_real_smul_right
    (c : Error) (A B : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (c • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_right c A B

private lemma ev_real_smul
    (ψ : QuantumState (ι × ι)) (c : Error) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (c • X) = c * ev ψ X := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simpa using ev_scale ψ c X

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

private lemma ev_leftTensor_mul_middle_finset_sum
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (A C R D : MIPStarRE.Quantum.Op ι)
    (B : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D) =
      ∑ x ∈ s,
        ev ψ
          (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
            rightTensor (ι₁ := ι) D) := by
  classical
  have hinner :
      ((A * (∑ x ∈ s, B x) * C) * R) =
        ∑ x ∈ s, ((A * B x * C) * R) := by
    simp [Matrix.mul_sum, Finset.sum_mul, mul_assoc]
  calc
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D)
        = ev ψ
            (leftTensor (ι₂ := ι) (∑ x ∈ s, ((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by rw [hinner]
    _ = ev ψ
          ((∑ x ∈ s, leftTensor (ι₂ := ι) (((A * B x * C) * R))) *
            rightTensor (ι₁ := ι) D) := by
          rw [leftTensor_finset_sum (ι₂ := ι)]
    _ = ev ψ
          (∑ x ∈ s,
            leftTensor (ι₂ := ι) (((A * B x * C) * R) ) *
              rightTensor (ι₁ := ι) D) := by
          rw [Finset.sum_mul]
    _ = ∑ x ∈ s,
          ev ψ
            (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by
          rw [ev_finset_sum]

set_option maxHeartbeats 2000000 in
-- The pointwise phase-2 fiber collapse expands a postprocessed slice outcome inside
-- a sandwiched tensor expectation; the explicit finite-sum linearity proof is
-- heartbeat-heavy but keeps the #714 marginalization residual transparent.
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
`avgOver_uniform_pointNext_decompose` as the intended first marginalization step. -/
private def evaluatedSlicePhaseTwoReindexingResidual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) : Prop :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
    avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)

/-- Unfold the phase-5 stability relation into the scalar defect term used in
`eq:gcom10`. -/
private lemma evaluatedSlice_phaseFive_stability_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (gamma zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)))) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ gb : StabilityTwoOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.1)).total) *
                  (((orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                    (orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2)) *
                  (1 - (G (pointHeight params q.1)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) ≤
      Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.1)).total) *
                    (((orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                      (orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2)) *
                    (1 - (G (pointHeight params q.1)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityTwoLeft params strategy family G q)
              (commDataProcessedGStabilityTwoRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityTwo_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityTwoLeft params strategy family G)
          (commDataProcessedGStabilityTwoRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hstab

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
    `gCommStabilityTwo_scalar` (this is the local `hphase5` step below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/
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
  let phase5Removed : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFiveRemoved params strategy family
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
  -- Phase 3: insert Alice's measurement on the first coordinate (the BABA-side
  -- insertion used before the point-commutation step).
  have hphase3 :
      |avgOver 𝒟 avgBABA - avgOver 𝒟 phase3Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgBABA, phase3Inserted] using
      evaluatedSlice_phaseThree_insert_bound
        params strategy zeta _hnorm family hcombined_fst
  -- Phase 5: remove the trailing `G^x` from the BABA-side inserted term via
  -- the direct boundedness estimate `gCommStabilityTwo_scalar`.
  -- The analytic part is now closed by `evaluatedSlice_phaseFive_stability_defect_bound`;
  -- the remaining #715 work is the exact finite reindexing/sign equality from
  -- `avgOver 𝒟 (phase3Inserted - phase5Removed)` to the negative of
  -- `evaluatedSlicePhaseFiveStabilityDefect`.  Concretely, this residual expands
  -- `totalSandwichFamily`, decomposes each `Point params.next` as `(u,x)`, uses the
  -- postprocessing-fiber identity `∑_a ∑_{g : g(u)=a} = ∑_g`, and accounts for
  -- `B A B * (G^x - 1) = - B A B * (1 - G^x)`.  This keeps the phase-4
  -- `6√(γ(m+1))` contribution split off rather than folding it into this `√ζ`
  -- boundedness step.
  have hphase5 :
      |avgOver 𝒟 phase3Inserted - avgOver 𝒟 phase5Removed| ≤ Real.sqrt zeta := by
    have _hdefect :=
      evaluatedSlice_phaseFive_stability_defect_bound
        params strategy zeta _hnorm family G _hG _hbound
    -- TODO(#715): prove the finite reindexing/sign equality described above and
    -- finish by applying `_hdefect`.
    sorry
  -- Phases 8/9: postprocessed self-consistency transports `BAB` to `ABA`.
  have htail :
      |avgOver 𝒟 avgBAB - avgOver 𝒟 avgABA| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgBAB, avgABA] using
      evaluatedSlice_phaseEightNine_tail_bound
        params strategy zeta _hnorm family _hpostSSC
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- Strategy: use the exact swap symmetry to reduce to the BABA-side chain.
  --
  --   2*(avgABA − avgABAB)
  --     = 2*(avgBAB − avgBABA)     [exact: avgABA = avgBAB, avgABAB = avgBABA]
  --     ≤ 2*(|avgBAB − phase5Removed|          ≤ 2√ζ, hphase67_fst
  --         + |phase5Removed − phase3Inserted|  ≤ √ζ,  hphase5
  --         + |phase3Inserted − avgBABA|         ≤ 2√ζ, hphase3)
  --     = 2 * 5√ζ = 10√ζ
  --     ≤ 48·m·(√γ + √ζ) = commDataProcessedGError
  --
  have hassemble :
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
        commDataProcessedGError params gamma zeta := by
    -- Exact swap symmetry (from evaluatedSliceCommutation_avg_swap_terms)
    have hswap := evaluatedSliceCommutation_avg_swap_terms params strategy family
    -- avgABA = avgBAB (exact)
    have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA := hswap.1
    -- avgABAB = avgBABA (exact)
    have hBABAeqABAB : avgOver 𝒟 avgBABA = avgOver 𝒟 avgABAB := hswap.2
    -- Rewrite goal to BABA-side
    have hrw : 2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) =
        2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA) := by
      linarith
    rw [hrw]
    -- Phase 6/7 (missing): reverse-insertion at the first coordinate.
    -- The tempting postprocessed-self-consistency route via `hpostSSC_fst`
    -- proves a different BABA-side tensor comparison and does **not** reduce the
    -- live target below: routing through that term reintroduces the global
    -- `|avgBAB - avgBABA|` quantity that this chain is trying to bound.
    --
    -- A naive `hcombined_fst` / `closenessOfIP` attempt here is not the missing
    -- BAB-side bridge: it reproduces the already formalized BABA-side phase-3
    -- insertion `avgBABA -> phase3Inserted`.  Encoding exact endpoint
    -- identifications with `avgBAB` and `phase5Removed` would assert false
    -- equalities.  The honest residual is therefore the live BAB-side endpoint
    -- comparison named below.
    -- Reference: the single reverse `eq:add-an-a` on the first coordinate,
    -- the BAB-side analogue of `eq:apply-add-an-a-once` (paper line 76).
    -- The BABA-side counterpart is the first reverse move in lines 99--101 and
    -- is already represented here by `hphase3` / `evaluatedSlice_phaseThree_insert_bound`.
    have hphase67_fst :
        |avgOver 𝒟 avgBAB - avgOver 𝒟 phase5Removed| ≤ 2 * Real.sqrt zeta := by
      have hphase67_endpoint :
          evaluatedSlicePhase67FirstReverseEndpointResidual params strategy family zeta := by
        -- TODO(#732): prove the live BAB-side first-coordinate reverse
        -- `eq:add-an-a` endpoint comparison, or adjust the scalar-chain
        -- orientation so this residual has paper-faithful endpoints.
        sorry
      simpa [evaluatedSlicePhase67FirstReverseEndpointResidual, 𝒟, avgBAB,
        phase5Removed] using hphase67_endpoint
    -- Triangle-inequality chain: |avgBAB − avgBABA| ≤ 5√ζ
    have hchain :
        |avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA| ≤ 5 * Real.sqrt zeta := by
      -- Use calc to avoid whnf unification issues with rwa [abs_sub_comm]
      have h35_comm : |avgOver 𝒟 phase5Removed - avgOver 𝒟 phase3Inserted| ≤
          Real.sqrt zeta :=
        (abs_sub_comm (avgOver 𝒟 phase5Removed) (avgOver 𝒟 phase3Inserted)).symm ▸ hphase5
      have h3_comm : |avgOver 𝒟 phase3Inserted - avgOver 𝒟 avgBABA| ≤
          2 * Real.sqrt zeta :=
        (abs_sub_comm (avgOver 𝒟 phase3Inserted) (avgOver 𝒟 avgBABA)).symm ▸ hphase3
      have hstep2 : |avgOver 𝒟 phase5Removed - avgOver 𝒟 avgBABA| ≤
          Real.sqrt zeta + 2 * Real.sqrt zeta :=
        le_trans (abs_sub_le _ (avgOver 𝒟 phase3Inserted) _)
          (add_le_add h35_comm h3_comm)
      calc |avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA|
          ≤ |avgOver 𝒟 avgBAB - avgOver 𝒟 phase5Removed| +
              |avgOver 𝒟 phase5Removed - avgOver 𝒟 avgBABA| :=
                abs_sub_le _ _ _
        _ ≤ 2 * Real.sqrt zeta + (Real.sqrt zeta + 2 * Real.sqrt zeta) :=
                add_le_add hphase67_fst hstep2
        _ = 5 * Real.sqrt zeta := by ring
    -- Convert absolute value to one-sided bound
    have h10 : 2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA) ≤
        10 * Real.sqrt zeta := by
      have hle : avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA ≤ 5 * Real.sqrt zeta :=
        le_trans (le_abs_self _) hchain
      linarith
    -- Arithmetic: 10√ζ ≤ 48·m·(√γ + √ζ) = commDataProcessedGError
    calc 2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA)
        ≤ 10 * Real.sqrt zeta := h10
      _ ≤ commDataProcessedGError params gamma zeta := by
            -- Extract nonnegativity of gamma and zeta from the hypotheses
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
            unfold commDataProcessedGError
            rw [Real.sqrt_eq_rpow]
            -- After rw, goal has zeta ^ (1/2) on LHS, Real.rpow on RHS.
            -- Use `change` to normalize everything to Real.rpow form.
            change 10 * Real.rpow zeta (1 / (2 : ℝ)) ≤
              48 * (params.m : ℝ) *
                (Real.rpow gamma (1 / (2 : ℝ)) + Real.rpow zeta (1 / (2 : ℝ)))
            have hm : 1 ≤ (params.m : ℝ) := by exact_mod_cast params.hm
            have hm_nonneg : (0 : ℝ) ≤ (params.m : ℝ) := Nat.cast_nonneg _
            have hg : (0 : ℝ) ≤ Real.rpow gamma (1 / (2 : ℝ)) :=
              Real.rpow_nonneg hgamma_nonneg _
            have hz : (0 : ℝ) ≤ Real.rpow zeta (1 / (2 : ℝ)) :=
              Real.rpow_nonneg hzeta_nonneg _
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (params.m : ℝ) - 1) hz,
                       mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) hm_nonneg) hg]
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
