import MIPStarRE.LDT.Commutativity.Scaffold.Products
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 11 commutativity: evaluated-slice bounds for phases 1 and 3

Closeness-of-inner-product side conditions for inserting Bob's measurement
into the evaluated-slice step (phases 1 and 3 in the paper proof).

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Phase-1 `closenessOfIP` side condition for inserting Bob's measurement.

This packages the `lem:normalization-condition` bound for
`C_{b,a} = G^x_a G^y_b G^x_a`, lifted to the left tensor factor. -/
private lemma evaluatedSlice_phaseOne_hC
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ q : EvaluatedSliceQuestion params,
      ∑ b : Fq params,
          (∑ a : Fq params,
              leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  ((evaluatedSliceFirstFactor params family q).outcome a))) *
            (∑ a : Fq params,
              leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  ((evaluatedSliceFirstFactor params family q).outcome a)))ᴴ ≤ 1 := by
  intro q
  let P : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  let Q : ProjSubMeas (Fq params) ι := evaluatedSliceFirstProj params family q
  let T : Fq params → MIPStarRE.Quantum.Op ι := fun b =>
    ∑ a : Fq params,
      ((evaluatedSliceFirstFactor params family q).outcome a) *
        ((evaluatedSliceSecondFactor params family q).outcome b) *
        ((evaluatedSliceFirstFactor params family q).outcome a)
  calc
    ∑ b : Fq params,
        (∑ a : Fq params,
            leftTensor (ι₂ := ι)
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a))) *
          (∑ a : Fq params,
            leftTensor (ι₂ := ι)
               (((evaluatedSliceFirstFactor params family q).outcome a) *
                 ((evaluatedSliceSecondFactor params family q).outcome b) *
                 ((evaluatedSliceFirstFactor params family q).outcome a)))ᴴ
      = ∑ b : Fq params, leftTensor (ι₂ := ι) (T b * (T b)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hsum :
              (∑ a : Fq params,
                  leftTensor (ι₂ := ι)
                    (((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a))) =
                leftTensor (ι₂ := ι) (T b) := by
            simp [T, leftTensor_finset_sum]
          rw [hsum]
          have hleft_adj :
              (leftTensor (ι₂ := ι) (T b))ᴴ = leftTensor (ι₂ := ι) ((T b)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (T b) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ b : Fq params, T b * (T b)ᴴ) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun b => T b * (T b)ᴴ)]
    _ = leftTensor (ι₂ := ι) (normalizationConditionSquareOperator P Q) := by
          simp [T, P, Q, normalizationConditionSquareOperator,
            normalizationConditionSquareFamily,
            normalizationConditionSandwichedTotalOperator,
            normalizationConditionSandwichedTotalFamily,
            normalizationConditionSandwichedFamily,
            normalizationConditionSandwichedOperator,
            evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
            evaluatedSliceFirstProj, postprocess]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) <| by
            simpa [normalizationConditionSquareOperator] using
              (normalizationConditionSquareFamily P Q).total_le_one

/-- View the `params.next` point measurement with the outcome type rewritten as
`Fq params`. -/
noncomputable def evaluatedSlicePointMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas (Point params.next) (Fq params) ι :=
  fun u => by
    simpa [Parameters.next] using
      (strategy.pointMeasurement u).toMeasurement

/-- Phase-1 insertion step for `evaluatedSlice_scalar_chain_bound`.

This is the `eq:gcom8 -> eq:apply-add-an-a-once` comparison: transport the
pointwise `consSubMeas` control to the second coordinate of an evaluated-slice
question, then apply `closenessOfIP` with the left-sandwich family
`G_a^{u,x} G_b^{v,y} G_a^{u,x}`.  The inserted term is kept in the explicit
`G^y \otimes A_b^{v,y}` form coming from `totalSandwichFamily`. -/
lemma evaluatedSlice_phaseOne_insert_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_snd : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
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
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) -
      avgOver 𝒟 inserted| ≤ 2 * Real.sqrt zeta := by
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    evaluatedSlicePointMeas params strategy
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b =>
      ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (evaluatedPointFamily params family)
        pointMeas q.2).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b a =>
      leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceFirstFactor params family q).outcome a))
  have h𝒟 :
      ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB :
      avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
    simpa [𝒟, A, B, pointMeas, Parameters.next, qSDD, evaluatedSliceSecondFactor,
      evaluatedPointFamily, IdxSubMeas.liftLeft, SubMeas.liftLeft] using
      hcombined_snd.squaredDistanceBound
  have hC :
      ∀ q, ∑ b : Fq params, (∑ a : Fq params, C q b a) * (∑ a : Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C] using evaluatedSlice_phaseOne_hC params family q
  have hzeta_nonneg : 0 ≤ zeta := by
    have hsdd_nonneg :
        0 ≤ sddError strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => (IdxSubMeas.liftLeft (evaluatedPointFamily params family)) q.2)
          (fun q =>
            (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas q.2)) := by
      exact sddError_nonneg strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => (IdxSubMeas.liftLeft (evaluatedPointFamily params family)) q.2)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.2))
    have hfour : 0 ≤ 4 * zeta := le_trans hsdd_nonneg hcombined_snd.squaredDistanceBound
    nlinarith
  have hABAB :
      avgOver 𝒟
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) =
        avgOver 𝒟
          (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (C q b a * A q b)) := by
    apply avgOver_congr
    intro q
    calc
      ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABABTerm params strategy family q ab
        = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  ((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b))) := by
              simpa [evaluatedSliceABABTerm, leftTensor_mul_leftTensor, mul_assoc] using
                (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b)))))
      _ = ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * A q b) := by
              rw [Finset.sum_comm]
              simp [A, C, leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
  calc
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) -
      avgOver 𝒟
        (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * B q b))| =
        |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * A q b)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * B q b))| := by
          rw [hABAB]
    _ ≤ Real.sqrt (4 * zeta) := hclose
    _ = 2 * Real.sqrt zeta := by
          rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
          norm_num

/-- Phase-3 `eq:add-an-a` insertion on the first coordinate.

This mirrors `evaluatedSlice_phaseOne_insert_bound` with the roles of the two
evaluated points swapped: transport the `consSubMeas` control to the first
coordinate of an evaluated-slice question, then apply `closenessOfIP` to the
explicit `B A B * (G^x \otimes A_a^{u,x})` summand that feeds the later
`commutativityPoints` step. -/
lemma evaluatedSlice_phaseThree_insert_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_fst : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta)) :
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
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABATerm params strategy family q ab) -
      avgOver 𝒟 inserted| ≤ 2 * Real.sqrt zeta := by
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    evaluatedSlicePointMeas params strategy
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a =>
      ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (evaluatedPointFamily params family)
        pointMeas q.1).outcome a)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a b =>
      leftTensor (ι₂ := ι)
        (((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b))
  have h𝒟 :
      ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB :
      avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
    simpa [𝒟, A, B, pointMeas, Parameters.next, qSDD, evaluatedSliceFirstFactor,
      evaluatedPointFamily, IdxSubMeas.liftLeft, SubMeas.liftLeft] using
      hcombined_fst.squaredDistanceBound
  have hC :
      ∀ q, ∑ a : Fq params, (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
    intro q
    let P : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
    let Q : ProjSubMeas (Fq params) ι := evaluatedSliceSecondProj params family q
    let T : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
      ∑ b : Fq params,
        ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b)
    calc
      ∑ a : Fq params,
          (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ
        = ∑ a : Fq params, leftTensor (ι₂ := ι) (T a * (T a)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            have hsum :
                (∑ b : Fq params, C q a b) = leftTensor (ι₂ := ι) (T a) := by
              simp [C, T, leftTensor_finset_sum]
            rw [hsum]
            have hleft_adj :
                (leftTensor (ι₂ := ι) (T a))ᴴ = leftTensor (ι₂ := ι) ((T a)ᴴ) := by
              simpa [leftTensor, opTensor] using
                (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (T a) (1 : MIPStarRE.Quantum.Op ι))
            rw [hleft_adj, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι) (∑ a : Fq params, T a * (T a)ᴴ) := by
            rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => T a * (T a)ᴴ)]
      _ = leftTensor (ι₂ := ι) (normalizationConditionSquareOperator P Q) := by
            simp [T, P, Q, normalizationConditionSquareOperator,
              normalizationConditionSquareFamily,
              normalizationConditionSandwichedTotalOperator,
              normalizationConditionSandwichedTotalFamily,
              normalizationConditionSandwichedFamily,
              normalizationConditionSandwichedOperator,
              evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
              evaluatedSliceSecondProj, postprocess]
      _ ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) <| by
              simpa [normalizationConditionSquareOperator] using
                (normalizationConditionSquareFamily P Q).total_le_one
  have hzeta_nonneg : 0 ≤ zeta := by
    have hsdd_nonneg :
        0 ≤ sddError strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => (IdxSubMeas.liftLeft (evaluatedPointFamily params family)) q.1)
          (fun q =>
            (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas q.1)) := by
      exact sddError_nonneg strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => (IdxSubMeas.liftLeft (evaluatedPointFamily params family)) q.1)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.1))
    have hfour : 0 ≤ 4 * zeta := le_trans hsdd_nonneg hcombined_fst.squaredDistanceBound
    nlinarith
  have hBABA :
      avgOver 𝒟
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABATerm params strategy family q ab) =
        avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (C q a b * A q a)) := by
    apply avgOver_congr
    intro q
    calc
      ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABATerm params strategy family q ab
        = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (((evaluatedSliceSecondFactor params family q).outcome b) *
                  ((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  ((evaluatedSliceFirstFactor params family q).outcome a))) := by
              simpa [evaluatedSliceBABATerm, leftTensor_mul_leftTensor, mul_assoc] using
                (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                      (((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a)))))
      _ = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a) := by
              simp [A, C, leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
  calc
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABATerm params strategy family q ab) -
      avgOver 𝒟
        (fun q => ∑ a : Fq params, ∑ b : Fq params,
          ev strategy.state (C q a b * B q a))| =
        |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a))| := by
          rw [hBABA]
    _ ≤ Real.sqrt (4 * zeta) := hclose
    _ = 2 * Real.sqrt zeta := by
          rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
          norm_num


end MIPStarRE.LDT.Commutativity
