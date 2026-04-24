import MIPStarRE.LDT.Pasting.Core

set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
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

end MIPStarRE.LDT.Pasting
