import MIPStarRE.LDT.Pasting.Core

/-!
# Section 12 pasting: switcheroo setup

Initial switcheroo infrastructure and aggregate expansions.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/

/-- Convert the one-question switcheroo self-consistency input into the
bipartite form used by `switchSandwich`. -/
lemma switcherooSelfConsistency_bip
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (omega : Error)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega) :
    Preliminaries.BipartiteSDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxProjSubMeas.toIdxSubMeas M)
      (IdxProjSubMeas.toIdxSubMeas M)
      omega := by
  constructor
  simpa [switcherooSelfConsistencyLeft, switcherooSelfConsistencyRight,
    IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    hselfM.squaredDistanceBound

/-- Lift slicewise complete-part self-consistency to the slice-pair distribution.

This packages the `G^x` self-consistency input in the form used by the
switcheroo tensor-bound steps. -/
lemma switcherooCompletePartSelfConsistency_pairBound
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDCore ψbi
          (fun g => leftTensor (ι₂ := ι) ((family.meas q.1).outcome g))
          (fun g => rightTensor (ι₁ := ι) ((family.meas q.1).outcome g))) ≤
      zeta := by
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDCore ψbi
          (fun g => leftTensor (ι₂ := ι) ((family.meas q.1).outcome g))
          (fun g => rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun _y => qSDDCore ψbi
                (fun g => leftTensor (ι₂ := ι) ((family.meas x).outcome g))
                (fun g => rightTensor (ι₁ := ι) ((family.meas x).outcome g)))) := by
            simpa [SlicePairQuestion, SliceQuestion] using
              (avgOver_uniform_prod
                (α := SliceQuestion params)
                (β := SliceQuestion params)
                (f := fun x _y => qSDDCore ψbi
                  (fun g => leftTensor (ι₂ := ι) ((family.meas x).outcome g))
                  (fun g => rightTensor (ι₁ := ι) ((family.meas x).outcome g))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x => qSDDCore ψbi
            (fun g => leftTensor (ι₂ := ι) ((family.meas x).outcome g))
            (fun g => rightTensor (ι₁ := ι) ((family.meas x).outcome g))) := by
          apply avgOver_congr
          intro x
          have hq0 : (params.q : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hq
          simp [avgOver, uniformDistribution]
          field_simp [hq0]
    _ = sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
          (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
            simp [sddError, qSDD, qSDDCore, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
              IdxProjSubMeas.toIdxSubMeas, SubMeas.liftLeft, SubMeas.liftRight]
    _ ≤ zeta := hselfG.completePartSelfConsistency.squaredDistanceBound

/-- Read the switcheroo point-product commutation hypothesis as an average
`qSDDCore` bound. -/
lemma switcherooPointProductCommutation_coreBound
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDCore ψbi
          (fun go => (switcherooPointProductLeft params family M q).outcome go)
          (fun go => (switcherooPointProductRight params family M q).outcome go)) ≤
      chi := by
  simpa [sddErrorOp, qSDDOp] using hcomm.squaredDistanceBound

/-- If `|f q| ≤ c` pointwise and the distribution has total weight at most `1`, then
its weighted average is bounded by `c`. -/
private lemma avgOver_abs_le_of_bound
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f : Question → Error)
    (c : Error)
    (hc : 0 ≤ c)
    (hf : ∀ q, |f q| ≤ c) :
    |avgOver 𝒟 f| ≤ c := by
  calc
    |avgOver 𝒟 f|
      = |∑ q ∈ 𝒟.support, 𝒟.weight q * f q| := rfl
    _ ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * f q| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |f q| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support, 𝒟.weight q * c := by
          refine Finset.sum_le_sum ?_
          intro q _
          exact mul_le_mul_of_nonneg_left (hf q) (𝒟.nonnegative q)
    _ = c * ∑ q ∈ 𝒟.support, 𝒟.weight q := by
          calc
            ∑ q ∈ 𝒟.support, 𝒟.weight q * c
              = ∑ q ∈ 𝒟.support, c * 𝒟.weight q := by
                  refine Finset.sum_congr rfl ?_
                  intro q _
                  ring
            _ = c * ∑ q ∈ 𝒟.support, 𝒟.weight q := by
                  rw [Finset.mul_sum]
    _ ≤ c * 1 := by
          exact mul_le_mul_of_nonneg_left h𝒟 hc
    _ = c := by ring

lemma avgOver_abs_le_avgOver_abs
    {α : Type*} [DecidableEq α]
    (𝒟 : Distribution α) (f : α → Error) :
    |avgOver 𝒟 f| ≤ avgOver 𝒟 (fun a => |f a|) := by
  unfold avgOver
  calc
    |∑ a ∈ 𝒟.support, 𝒟.weight a * f a|
      ≤ ∑ a ∈ 𝒟.support, |𝒟.weight a * f a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a * |f a| := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative a)]
    _ = avgOver 𝒟 (fun a => |f a|) := by
          rfl

/-- The total of a submeasurement is bounded between `0` and `1`. -/
private lemma subMeas_total_opBounded01
    {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    Preliminaries.OpBounded01 A.total := by
  constructor
  · exact A.total_nonneg
  · exact sub_nonneg.mpr A.total_le_one

/-- A projective sandwich family with middle operator bounded by `1` sums to at
most `1`. -/
lemma projSubMeas_sandwich_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι)
    (hB : B ≤ 1) :
    ∑ a : Outcome, A.outcome a * B * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, A.outcome a * B * A.outcome a
      ≤ ∑ a : Outcome, A.outcome a * 1 * A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) hB
    _ = ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [A.proj a]
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- The total operator of a projective submeasurement is idempotent. -/
lemma projSubMeas_total_sq
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome ι) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total := by
  simpa using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P

/-- Expand a single-question switcheroo `qSDDOp` term into its four scalar
components. -/
lemma switcherooAggregate_qSDDOp_expand
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    qSDDOp ψbi
      (switcherooAggregateLeft params family M q)
      (switcherooAggregateRight params family M q)
      =
        ∑ o : Outcome,
          (ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)) +
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total)) -
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  have hGsq : G * G = G := by
    simpa [G, completePartSubMeas, postprocess_total] using
      projSubMeas_total_sq (family.meas q.1)
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro o _
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hMosq : Mo * Mo = Mo := by
    simpa [Mo] using (M q.2).proj o
  have hGherm : (leftTensor (ι₂ := ι) G)ᴴ = leftTensor (ι₂ := ι) G := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι)
          (SubMeas.total_nonneg (completePartSubMeas params family q.1)))).isHermitian.eq
  have hMoherm : (leftTensor (ι₂ := ι) Mo)ᴴ = leftTensor (ι₂ := ι) Mo := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((M q.2).outcome_pos o))).isHermitian.eq
  calc
    ev ψbi
        ((((switcherooAggregateLeft params family M q).outcome o -
              (switcherooAggregateRight params family M q).outcome o)ᴴ) *
          ((switcherooAggregateLeft params family M q).outcome o -
            (switcherooAggregateRight params family M q).outcome o))
      = ev ψbi
          ((((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
                (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))ᴴ) *
            ((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
              (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))) := by
            simp [switcherooAggregateLeft, switcherooAggregateRight,
              multiplyByTotalOnLeft, multiplyByTotalOnRight,
              OpFamily.leftPlacedOpFamily, completePartSubMeas, G, Mo,
              leftTensor_mul_leftTensor, postprocess_total]
    _ = ev ψbi
          (((leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
                (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo)) *
            ((leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) -
              (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G))) := by
            simp [hGherm, hMoherm]
    _ = ev ψbi
          ((leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G *
                leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo) +
            (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo *
                leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
            (leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G *
                leftTensor (ι₂ := ι) Mo * leftTensor (ι₂ := ι) G) -
            (leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo *
                leftTensor (ι₂ := ι) G * leftTensor (ι₂ := ι) Mo)) := by
            congr 1
            noncomm_ring
    _ = ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo) +
            leftTensor (ι₂ := ι) (G * Mo * G) -
            leftTensor (ι₂ := ι) (Mo * G * Mo * G) -
            leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            simp [leftTensor_mul_leftTensor, hGsq, hMosq, mul_assoc]
    _ =
        ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo)) +
        ev ψbi
          (leftTensor (ι₂ := ι) (G * Mo * G)) -
        ev ψbi
          (leftTensor (ι₂ := ι) (Mo * G * Mo * G)) -
        ev ψbi
          (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
            rw [ev_sub, ev_sub, ev_add]
    _ =
        ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                (M q.2).outcome o)) +
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (completePartSubMeas params family q.1).total)) -
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                (M q.2).outcome o * (completePartSubMeas params family q.1).total)) -
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                (completePartSubMeas params family q.1).total * (M q.2).outcome o)) := by
            simp [G, Mo]

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
private lemma switcherooAggregateFirstTerm_eq_leftSandwich
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

/-- The one-outcome projective family whose sole effect is the complete slice part `G^x`. -/
noncomputable def completePartProjFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (SliceQuestion params) Unit ι :=
  fun x =>
    { toSubMeas := completePartSubMeas params family x
      proj := by
        intro u
        cases u
        have hsingle :
            (completePartSubMeas params family x).outcome () =
              (completePartSubMeas params family x).total := by
          simpa [completePartSubMeas] using
            postprocess_unit_outcome_eq_total ((family.meas x).toSubMeas)
        rw [hsingle]
        simpa [completePartSubMeas, postprocess_total] using
          MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x) }

/-- The second positive term in the switcheroo expansion. -/
noncomputable def switcherooAggregateSecondTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The third (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateThirdTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The fourth (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateFourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))

lemma switcherooAggregateThirdTerm_eq_fourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateThirdTerm params ψbi family M =
      switcherooAggregateFourthTerm params ψbi family M := by
  unfold switcherooAggregateThirdTerm switcherooAggregateFourthTerm
  apply avgOver_congr
  intro q
  refine Finset.sum_congr rfl ?_
  intro o _
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hGherm : Gᴴ = G :=
    (Matrix.nonneg_iff_posSemidef.mp
      (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq
  have hMoherm : Moᴴ = Mo :=
    (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq
  calc
    ev ψbi (leftTensor (ι₂ := ι) (Mo * G * Mo * G))
      = ev ψbi ((leftTensor (ι₂ := ι) (Mo * G * Mo * G))ᴴ) := by
          symm
          exact ev_conjTranspose ψbi _
    _ = ev ψbi (leftTensor (ι₂ := ι) ((Mo * G * Mo * G)ᴴ)) := by
          congr 1
          simpa [leftTensor, opTensor] using
            (conjTranspose_opTensor (Mo * G * Mo * G)
              (1 : MIPStarRE.Quantum.Op ι))
    _ = ev ψbi (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
          congr 1
          simp [mul_assoc, Matrix.conjTranspose_mul, hGherm, hMoherm]

/-- Split the fourth switcheroo term by inserting the complete-part projector
resolution `G = ∑_g G_g`. -/
lemma switcherooAggregateFourthTerm_eq_split
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateFourthTerm params ψbi family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2))) := by
  unfold switcherooAggregateFourthTerm
  apply avgOver_congr
  intro q
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  calc
    ∑ o : Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            (G * (M q.2).outcome o * G * (M q.2).outcome o))
      = ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              (G * (M q.2).outcome o * (∑ g : Polynomial params, Gq g) *
                (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [(family.meas q.1).sum_eq_total]
            simp [G, completePartSubMeas, postprocess_total]
    _ = ∑ o : Outcome,
          ∑ g : Polynomial params,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [← ev_sum ψbi (fun g : Polynomial params =>
              leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o))]
            congr 1
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ,
              Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ o : Outcome,
          ∑ g : Polynomial params,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            refine Finset.sum_congr rfl ?_
            intro g _
            simp [Gq, mul_assoc, (family.meas q.1).proj g]
    _ = ∑ g : Polynomial params,
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            rw [Finset.sum_comm]
    _ = ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              (G * (M q.2).outcome go.2 * Gq go.1 * Gq go.1 * (M q.2).outcome go.2)) := by
            symm
            simpa using
              (Fintype.sum_prod_type' (f := fun g o =>
                ev ψbi
                  (leftTensor (ι₂ := ι)
                    (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o))))


end MIPStarRE.LDT.Pasting
