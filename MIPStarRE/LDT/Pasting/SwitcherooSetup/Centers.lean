import MIPStarRE.LDT.Pasting.SwitcherooSetup.Infrastructure

/-!
# Section 12 pasting: switcheroo centers

Switcheroo center terms and their sandwich rewrites.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The common comparison scalar `⟨ψ, G ⊗ M ψ⟩` from the switcheroo proof. -/
noncomputable def switcherooAggregateTarget
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
          rightTensor (ι₁ := ι) ((M q.2).outcome o))

/-- The first positive term in the switcheroo expansion. -/
noncomputable def switcherooAggregateFirstTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o))

/-- Rewrite the first positive switcheroo term as a left-sandwich average. -/
lemma switcherooAggregateFirstTerm_eq_leftSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateFirstTerm params ψbi family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  unfold switcherooAggregateFirstTerm
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun y =>
                ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M y).outcome o * (completePartSubMeas params family x).total *
                        (M y).outcome o)))) := by
            simpa [SlicePairQuestion, SliceQuestion] using
              (avgOver_uniform_prod
                (α := SliceQuestion params)
                (β := SliceQuestion params)
                (f := fun x y =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor (ι₂ := ι)
                        ((M y).outcome o * (completePartSubMeas params family x).total *
                          (M y).outcome o))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
              (uniformDistribution (SliceQuestion params))
              M
              ((completePartSubMeas params family x).total)) := by
            apply avgOver_congr
            intro x
            simp [MIPStarRE.LDT.Preliminaries.leftSandwichExpectation,
              avgOver, leftTensor_mul_leftTensor, mul_assoc]

/-- Rewrite the `G ⊗ M` switcheroo center as a middle-sandwich average. -/
lemma switcherooAggregateTarget_eq_middleSandwich
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateTarget params ψbi family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  unfold switcherooAggregateTarget
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                rightTensor (ι₁ := ι) ((M q.2).outcome o)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun y =>
                ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι) ((completePartSubMeas params family x).total) *
                      rightTensor (ι₁ := ι) ((M y).outcome o)))) := by
            simpa [SlicePairQuestion, SliceQuestion] using
              (avgOver_uniform_prod
                (α := SliceQuestion params)
                (β := SliceQuestion params)
                (f := fun x y =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor (ι₂ := ι) ((completePartSubMeas params family x).total) *
                        rightTensor (ι₁ := ι) ((M y).outcome o))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            MIPStarRE.LDT.Preliminaries.middleSandwichExpectation ψbi
              (uniformDistribution (SliceQuestion params))
              M
              ((completePartSubMeas params family x).total)) := by
            apply avgOver_congr
            intro x
            simp [MIPStarRE.LDT.Preliminaries.middleSandwichExpectation, avgOver]

/-- The first positive switcheroo term is close to the `G ⊗ M` center via the
self-consistency of `M`. -/
lemma switcheroo_first_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (omega : Error)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega) :
    let firstTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.leftSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x => Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          M ((completePartSubMeas params family x).total))
    |firstTerm - commonTerm| ≤ 2 * Real.sqrt omega := by
  dsimp
  let L : Fq params → Error := fun x =>
    Preliminaries.leftSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  let C : Fq params → Error := fun x =>
    Preliminaries.middleSandwichExpectation ψbi
      (uniformDistribution (SliceQuestion params))
      M ((completePartSubMeas params family x).total)
  have hselfM_bip := switcherooSelfConsistency_bip params ψbi M omega hselfM
  have hpoint : ∀ x, |L x - C x| ≤ 2 * Real.sqrt omega := by
    intro x
    have hB : Preliminaries.OpBounded01 ((completePartSubMeas params family x).total) := by
      refine ⟨?_, ?_⟩
      · exact SubMeas.total_nonneg (completePartSubMeas params family x)
      · exact sub_nonneg.mpr (completePartSubMeas params family x).total_le_one
    simpa [L, C] using
      (Preliminaries.switchSandwich ψbi
        (uniformDistribution (SliceQuestion params))
        hnorm
        (uniformDistribution_weight_sum_le_one (SliceQuestion params))
        M
        ((completePartSubMeas params family x).total)
        hB
        omega
        hselfM_bip).leftSandwichTransfer
  calc
    |avgOver (uniformDistribution (SliceQuestion params)) L -
        avgOver (uniformDistribution (SliceQuestion params)) C|
      = |avgOver (uniformDistribution (SliceQuestion params)) (fun x => L x - C x)| := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun x => |L x - C x|) := by
          exact avgOver_abs_le_avgOver_abs _ _
    _ ≤ avgOver (uniformDistribution (SliceQuestion params)) (fun _ => 2 * Real.sqrt omega) := by
          exact avgOver_mono _ _ _ hpoint
    _ = 2 * Real.sqrt omega :=
          avgOver_uniform_const (α := SliceQuestion params) (2 * Real.sqrt omega)

end MIPStarRE.LDT.Pasting
