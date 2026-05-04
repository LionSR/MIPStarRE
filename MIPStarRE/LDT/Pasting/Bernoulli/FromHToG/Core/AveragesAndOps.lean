import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Bernoulli.Weights

/-!
# Section 12 pasting: operator averages and projective submeasurement lemmas

Averages over uniform distributions, tensor placement identities, and
projective submeasurement algebraic lemmas for the `fromHToG` bridge.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Operator-valued constant averages factor through the scalar distribution mass. -/
lemma averageOperatorOverDistribution_const {α : Type*}
    (𝒟 : Distribution α) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ x ∈ 𝒟.support, 𝒟.weight x) • A := by
  unfold averageOperatorOverDistribution
  rw [Finset.sum_smul]

lemma fromHToG_averageOperator_uniform_const_one
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α)
      (fun _ : α => (1 : MIPStarRE.Quantum.Op ι)) = 1 := by
  rw [averageOperatorOverDistribution_const]
  rw [uniformDistribution_weight_sum_eq_one, one_smul]

/-- The completed branch of `\widehat G` averages to the operator `G` used in the
Bernoulli recurrence, matching `references/ldt-paper/ld-pasting.tex:1408--1415`
for the `τ_ℓ = 1` case. -/
lemma fromHToG_completePart_average_total_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total := by
  unfold averageOperatorOverDistribution IdxPolyFamily.averagedSubMeas
  simp [completePartSubMeas_total]

/-- The incomplete branch of `\widehat G` averages to `I - G`, matching
`references/ldt-paper/ld-pasting.tex:1408--1415` for the `τ_ℓ = 0` case. -/
lemma fromHToG_incompletePart_average_total_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total := by
  classical
  calc
    averageOperatorOverDistribution (uniformDistribution (Fq params))
        (fun x => (incompletePartSubMeas params family x).total)
      = ∑ x ∈ (uniformDistribution (Fq params)).support,
          ((uniformDistribution (Fq params)).weight x • (1 : MIPStarRE.Quantum.Op ι) -
            (uniformDistribution (Fq params)).weight x •
              (completePartSubMeas params family x).total) := by
          unfold averageOperatorOverDistribution incompletePartSubMeas
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp [smul_sub]
    _ = averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun _ : Fq params => (1 : MIPStarRE.Quantum.Op ι)) -
        averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun x => (completePartSubMeas params family x).total) := by
          unfold averageOperatorOverDistribution
          rw [Finset.sum_sub_distrib]
    _ = 1 - family.averagedSubMeas.total := by
          rw [fromHToG_averageOperator_uniform_const_one]
          rw [fromHToG_completePart_average_total_eq]

/-- A zero-length type restriction of the sandwiched family has total identity.
This isolates the `tailLen = 0` collapse of `outcomesByType`, `restrictSubMeas`,
and the empty half-sandwich product. -/
lemma fromHToG_emptyRestrictedSandwichTotal_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (xs : PointTuple params 0) (τ : GHatType 0) :
    (postprocess
      (@restrictSubMeas ι _ _ (GHatTupleOutcome params 0) _
        (gHatSandwichFamily params family 0 xs)
        (fun gs => gs ∈ outcomesByType τ)
        (Classical.decPred (fun gs => gs ∈ outcomesByType τ)))
      (fun _ => ())).total = 1 := by
  simp only [restrictSubMeas, outcomesByType, IsEmpty.forall_iff, Set.setOf_true,
    Set.mem_univ, ↓reduceIte, gHatSandwichFamily, gHatHalfProductOutcomeOperator,
    Matrix.conjTranspose_one, mul_one, gHatHalfProductTotalOperator, Finset.univ_unique,
    Finset.filter_true, Finset.sum_const, Finset.card_singleton, one_smul, postprocess_total]

/-- The empty suffix sandwich has total identity. -/
lemma fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (τ : GHatType 0) :
    (averagedSandwichByTypeSubMeas params family 0 τ).total = 1 := by
  simp only [averagedSandwichByTypeSubMeas, averageIdxSubMeas]
  rw [show (fun xs : PointTuple params 0 =>
      (postprocess
        (@restrictSubMeas ι _ _ (GHatTupleOutcome params 0) _
          (gHatSandwichFamily params family 0 xs)
          (fun gs => gs ∈ outcomesByType τ)
          (Classical.decPred (fun gs => gs ∈ outcomesByType τ)))
        (fun _ => ())).total) =
      (fun _ : PointTuple params 0 => (1 : MIPStarRE.Quantum.Op ι)) by
    funext xs
    exact fromHToG_emptyRestrictedSandwichTotal_eq_one params family xs τ]
  exact fromHToG_averageOperator_uniform_const_one (PointTuple params 0)

/-- Tensor placement collapses to the left factor when the right recurrence weight
is the stage-`0` eligibility indicator. -/
lemma fromHToG_leftTensor_mul_rightTensor_indicator
    (A : MIPStarRE.Quantum.Op ι) (p : Prop) [Decidable p] :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι)
        (if p then 1 else 0 : MIPStarRE.Quantum.Op ι) =
      leftTensor (ι₂ := ι) (if p then A else 0) := by
  by_cases hp : p <;> simp [hp, leftTensor, rightTensor]

/-- Right tensor placement distributes over addition. -/
lemma fromHToG_rightTensor_add (A B : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) (A + B) = rightTensor (ι₁ := ι) A + rightTensor (ι₁ := ι) B := by
  simpa [Fintype.sum_bool] using
    (rightTensor_finset_sum (ι₁ := ι) (Finset.univ : Finset Bool)
      (fun b : Bool => if b then A else B)).symm

/-- Conjugate transpose commutes with left tensor placement. -/
lemma fromHToG_leftTensor_conjTranspose (A : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) A)ᴴ = leftTensor (ι₂ := ι) Aᴴ := by
  simp [leftTensor, Matrix.conjTranspose_kronecker]

/-- An outcome of a projective submeasurement is unchanged by multiplying by the
total mass on the right. -/
lemma fromHToG_projSubMeas_outcome_mul_total_eq_outcome {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) (a : α) :
    A.outcome a * A.total = A.outcome a := by
  simpa using ProjSubMeas.outcome_mul_total_eq_outcome A a

/-- The total of a projective submeasurement is idempotent. -/
lemma fromHToG_projSubMeas_total_proj {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) :
    A.total * A.total = A.total := by
  simpa using ProjSubMeas.total_proj A

/-- Each completed `\widehat G` outcome is projective. -/
lemma fromHToG_gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using fromHToG_projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

/-- Summing completed outcomes with `isSome = true` gives the complete branch. -/
lemma fromHToG_gHatIdxMeas_sum_isSome_true
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        (gHatIdxMeas params family x).outcome g) =
      (completePartSubMeas params family x).total := by
  classical
  have hfilter :
      ((Finset.univ : Finset (GHatOutcome params)).filter fun g => g.isSome = true) =
        (Finset.univ.image (fun p : Polynomial params => (some p : GHatOutcome params))) := by
    ext g
    cases g <;> simp
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        (gHatIdxMeas params family x).outcome g)
        = ∑ g ∈ ((Finset.univ : Finset (GHatOutcome params)).filter fun g =>
            g.isSome = true), (gHatIdxMeas params family x).outcome g := by
            rfl
    _ = ∑ g ∈ (Finset.univ.image fun p : Polynomial params =>
            (some p : GHatOutcome params)), (gHatIdxMeas params family x).outcome g := by
          rw [hfilter]
    _ = ∑ p : Polynomial params, (gHatIdxMeas params family x).outcome (some p) := by
          rw [Finset.sum_image]
          intro a _ha b _hb h
          cases h
          rfl
    _ = ∑ p : Polynomial params, (family.meas x).outcome p := by
          simp [gHatIdxMeas, completeSubMeas]
    _ = (completePartSubMeas params family x).total := by
          simp [completePartSubMeas, postprocess_total, (family.meas x).sum_eq_total]

/-- Summing completed outcomes with `isSome = false` gives the incomplete branch. -/
lemma fromHToG_gHatIdxMeas_sum_isSome_false
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        (gHatIdxMeas params family x).outcome g) =
      (incompletePartSubMeas params family x).total := by
  classical
  have hfilter :
      ((Finset.univ : Finset (GHatOutcome params)).filter fun g => g.isSome = false) =
        ({none} : Finset (GHatOutcome params)) := by
    ext g
    cases g <;> simp
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        (gHatIdxMeas params family x).outcome g)
        = ∑ g ∈ ((Finset.univ : Finset (GHatOutcome params)).filter fun g =>
            g.isSome = false), (gHatIdxMeas params family x).outcome g := by
            rfl
    _ = (gHatIdxMeas params family x).outcome none := by
          rw [hfilter]
          simp
    _ = (incompletePartSubMeas params family x).total := by
          simp [gHatIdxMeas, completeSubMeas, incompletePartSubMeas, completePartSubMeas,
            postprocess_total]

/-- Weighted complete-branch sum after using completed-outcome projectivity. -/
lemma fromHToG_gHatIdxMeas_sum_isSome_true_weight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (completePartSubMeas params family x).total := by
  classical
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g)
      = ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
          S * (gHatIdxMeas params family x).outcome g := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [mul_assoc, fromHToG_gHatIdxMeas_proj params family x g]
    _ = S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
          (gHatIdxMeas params family x).outcome g) := by
          rw [Finset.mul_sum]
    _ = S * (completePartSubMeas params family x).total := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_true]

/-- Weighted incomplete-branch sum after using completed-outcome projectivity. -/
lemma fromHToG_gHatIdxMeas_sum_isSome_false_weight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (incompletePartSubMeas params family x).total := by
  classical
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g)
      = ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
          S * (gHatIdxMeas params family x).outcome g := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [mul_assoc, fromHToG_gHatIdxMeas_proj params family x g]
    _ = S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
          (gHatIdxMeas params family x).outcome g) := by
          rw [Finset.mul_sum]
    _ = S * (incompletePartSubMeas params family x).total := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_false]

/-- Expectation-level weighted complete-branch sum. -/
lemma fromHToG_ev_sum_isSome_true_weight
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (x : Fq params)
    (A S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι) (S * (completePartSubMeas params family x).total)) := by
  classical
  rw [← ev_finset_sum]
  congr 1
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))
      = leftTensor (ι₂ := ι) A *
          (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g)) := by
          rw [Finset.mul_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
              S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g) := by
          rw [rightTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι) (S * (completePartSubMeas params family x).total) := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_true_weight]

/-- Expectation-level weighted incomplete-branch sum. -/
lemma fromHToG_ev_sum_isSome_false_weight
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (x : Fq params)
    (A S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι) (S * (incompletePartSubMeas params family x).total)) := by
  classical
  rw [← ev_finset_sum]
  congr 1
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))
      = leftTensor (ι₂ := ι) A *
          (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g)) := by
          rw [Finset.mul_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
              S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g) := by
          rw [rightTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι) (S * (incompletePartSubMeas params family x).total) := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_false_weight]

end MIPStarRE.LDT.Pasting
