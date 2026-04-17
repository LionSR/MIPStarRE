import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Core

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `lem:good-strategy-characterization`.

The axis-parallel branch is already definitionally a consistency bound. The
self-consistency branch is the same consistency bound specialized to the point
measurement, since that family is complete. The diagonal branch remains bundled
as `strategy.diagonalFailureProbability` because its sampled question type
depends on the restriction index `j`. -/
theorem goodStrategyCharacterization {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (eps delta gamma : Error) :
    strategy.IsGood eps delta gamma ↔
      ConsRel strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
        eps ∧
      ConsRel strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        delta ∧
      strategy.diagonalFailureProbability ≤ gamma := by
  have hself_eq_point (u : Point params) :
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas) =
        qBipartiteConsDefect strategy.state
          ((strategy.pointMeasurement u).toSubMeas)
          ((strategy.pointMeasurement u).toSubMeas) := by
    simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
      (strategy.pointMeasurement u).total_eq_one, leftTensor, opTensor]
  have hself_eq :
      bipartiteSSCError strategy.state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) =
        bipartiteConsError strategy.state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) := by
    unfold bipartiteSSCError bipartiteConsError
    apply avgOver_congr
    intro u
    simpa using hself_eq_point u
  constructor
  · intro h
    refine ⟨⟨h.axisParallelTest⟩, ?_, h.diagonalLineTest⟩
    constructor
    rw [← hself_eq]
    exact h.selfConsistencyTest
  · rintro ⟨haxis, hself, hdiag⟩
    refine ⟨haxis.offDiagonalBound, ?_, hdiag⟩
    simpa [SymStrat.selfConsistencyFailureProbability, hself_eq] using
      hself.offDiagonalBound

/-- `prop:two-notions-of-self-consistency-after-evaluation`.

Proof:
1. Postprocessing preserves the total mass and can only increase the diagonal
   overlap term `∑_b ⟨ψ|A_[f(a)=b] ⊗ A_[f(a)=b]|ψ⟩`.
2. Hence bipartite SSC transfers from `A` to the postprocessed family.
3. Apply `twoNotionsOfSelfConsistency` to the postprocessed family. -/
theorem twoNotionsOfSelfConsistencyAfterEvaluation
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α ι) (δ : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ) := by
  intro hssc
  have hpost :
      BipartiteSSCRel ψ 𝒟 (fun q => postprocess (A q) f) δ := by
    rcases hssc with ⟨hssc⟩
    constructor
    unfold bipartiteSSCError at *
    calc
      avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (postprocess (A q) f))
        ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
            apply avgOver_mono
            intro q
            let M := A q
            have hmatch :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) (postprocess M f))
                    (rightPlacedSubMeas (ιA := ι) (postprocess M f)) ≥
                  qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) M)
                    (rightPlacedSubMeas (ιA := ι) M) :=
              qMatchMass_leftRight_postprocess_ge ψ M M f
            have hsub :
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    qMatchMass ψ
                      (leftPlacedSubMeas (ιB := ι) (postprocess M f))
                      (rightPlacedSubMeas (ιA := ι) (postprocess M f))
                  ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    qMatchMass ψ
                      (leftPlacedSubMeas (ιB := ι) M)
                      (rightPlacedSubMeas (ιA := ι) M) := by
              linarith
            have hmass_post :
                ev ψ (leftTensor (ι₂ := ι) (postprocess M f).total) =
                  ev ψ (leftTensor (ι₂ := ι) M.total) := by
              simp [postprocess_total]
            have hmatch_post :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) (postprocess M f))
                    (rightPlacedSubMeas (ιA := ι) (postprocess M f)) =
                  ∑ b : β,
                    ev ψ
                      (opTensor
                        ((postprocess M f).outcome b)
                        ((postprocess M f).outcome b)) := by
              simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
                leftTensor_mul_rightTensor_eq_opTensor]
            have hmatch_orig :
                qMatchMass ψ
                    (leftPlacedSubMeas (ιB := ι) M)
                    (rightPlacedSubMeas (ιA := ι) M) =
                  ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
              simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
                leftTensor_mul_rightTensor_eq_opTensor]
            have hsub' :
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ b : β,
                      ev ψ
                        (opTensor
                          ((postprocess M f).outcome b)
                          ((postprocess M f).outcome b))
                  ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
              rw [← hmatch_post, ← hmatch_orig]
              exact hsub
            change
              max 0
                  (ev ψ (leftTensor (ι₂ := ι) (postprocess M f).total) -
                    ∑ b : β,
                      ev ψ
                        (opTensor
                          ((postprocess M f).outcome b)
                          ((postprocess M f).outcome b)))
                ≤
              max 0
                  (ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)))
            rw [hmass_post]
            exact max_le_max le_rfl hsub'
      _ ≤ δ := hssc
  exact twoNotionsOfSelfConsistency ψ 𝒟 (fun q => postprocess (A q) f) δ
    ⟨hperm, hpost⟩

/-- `prop:completeness-transfer-self-consistent-A`.

Proof:
1. Lower-bound `⟨ψ|B ⊗ I|ψ⟩` by the mixed overlap
   `∑ₐ ⟨ψ|B_a ⊗ A_a|ψ⟩` using `A_a ≤ I`.
2. Compare `∑ₐ ⟨ψ|B_a ⊗ A_a|ψ⟩` with
   `∑ₐ ⟨ψ|A_a ⊗ A_a|ψ⟩` by a Cauchy-Schwarz overlap estimate from
   the hypothesis `A ⊗ I ≈_ε B ⊗ I`.
3. Use bipartite SSC to replace the latter by
   `⟨ψ|A ⊗ I|ψ⟩ - δ`.
4. Relax the resulting bound to the requested `δ + 2√ε` form. -/
theorem completenessTransferSelfConsistentA
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι) (δ ε : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) ε →
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≥
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - δ - 2 * Real.sqrt ε := by
  intro hssc ⟨hε⟩
  have hlocalSSC :
      SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) δ :=
    bipartiteSSC_implies_localSSC_liftLeft ψ hperm 𝒟 A δ hssc
  rcases hlocalSSC with ⟨hδ⟩
  let diagA : Question → Error := fun q =>
    ∑ a : Outcome,
      ev ψ
        (((IdxSubMeas.liftLeft A) q).outcome a *
          ((IdxSubMeas.liftLeft A) q).outcome a)
  let defectA : Question → Error := fun q =>
    subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - diagA q
  have hdefectA_avg :
      avgOver 𝒟 defectA ≤ δ := by
    calc
      avgOver 𝒟 defectA
        ≤ avgOver 𝒟 (fun q => qSSCDefect ψ ((IdxSubMeas.liftLeft A) q)) := by
            apply avgOver_mono
            intro q
            exact le_max_right 0 (defectA q)
      _ = sscError ψ 𝒟 (IdxSubMeas.liftLeft A) := by
            simp [sscError, qSSCDefect]
      _ ≤ δ := hδ
  let sdd : Question → Error := fun q =>
    qSDD ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
  let gap : Question → Error := fun q =>
    diagA q - subMeasMass ψ ((IdxSubMeas.liftLeft B) q)
  have hgap_pointwise : ∀ q, gap q ≤ 2 * Real.sqrt (sdd q) := by
    intro q
    let diagB : Error :=
      ∑ a : Outcome,
        ev ψ
          (((IdxSubMeas.liftLeft B) q).outcome a *
            ((IdxSubMeas.liftLeft B) q).outcome a)
    let overlap : Error :=
      ∑ a : Outcome,
        ev ψ
          (((IdxSubMeas.liftLeft A) q).outcome a *
            ((IdxSubMeas.liftLeft B) q).outcome a)
    have hdiagB_le_massB :
        diagB ≤ subMeasMass ψ ((IdxSubMeas.liftLeft B) q) := by
      simpa [diagB, subMeasMass] using
        subMeas_diagMass_le_mass ψ ((IdxSubMeas.liftLeft B) q)
    have hgap_left_raw :
        |diagA q - overlap| ≤ Real.sqrt (sdd q) := by
      simpa [diagA, overlap, sdd] using
        question_overlap_gap_left ψ hψ
          ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
    have hgap_left :
        diagA q - overlap ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_left_raw]
    have hgap_right_raw :
        |overlap - diagB| ≤ Real.sqrt (sdd q) := by
      simpa [diagB, overlap, sdd] using
        question_overlap_gap_right ψ hψ
          ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
    have hgap_right :
        overlap - diagB ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_right_raw]
    have hdiag_gap :
        diagA q - diagB ≤ 2 * Real.sqrt (sdd q) := by
      linarith
    have hmass_gap :
        gap q ≤ diagA q - diagB := by
      dsimp [gap]
      exact sub_le_sub_left hdiagB_le_massB _
    exact le_trans hmass_gap hdiag_gap
  have hgap_avg :
      avgOver 𝒟 gap ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := by
    unfold avgOver
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left (hgap_pointwise q) (𝒟.nonnegative q)
  have hsqrt_avg_abs :
      |avgOver 𝒟 (fun q => Real.sqrt (sdd q))| ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => Real.sqrt (sdd q))
        sdd
        (by
          intro q
          rw [abs_of_nonneg (Real.sqrt_nonneg _)])
        (by
          intro q
          exact qSDD_nonneg ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q))
        h𝒟
  have hsqrt_avg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => Real.sqrt (sdd q)) :=
    avgOver_nonneg 𝒟 _ fun q => Real.sqrt_nonneg _
  have hsqrt_avg :
      avgOver 𝒟 (fun q => Real.sqrt (sdd q)) ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    simpa [abs_of_nonneg hsqrt_avg_nonneg] using hsqrt_avg_abs
  have hscale_avg :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) =
        2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    calc
      ∑ q ∈ 𝒟.support, 𝒟.weight q * (2 * Real.sqrt (sdd q))
        = ∑ q ∈ 𝒟.support, 2 * (𝒟.weight q * Real.sqrt (sdd q)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            ring
      _ = 2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * Real.sqrt (sdd q) := by
            rw [← Finset.mul_sum]
  have hsdd_sqrt :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) ≤
        2 * Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := by
    rw [hscale_avg]
    calc
      2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q))
        ≤ 2 * Real.sqrt (avgOver 𝒟 sdd) := by
            exact mul_le_mul_of_nonneg_left hsqrt_avg (by positivity)
      _ = 2 * Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := by
            simp [sddError, sdd]
  have hsqrt_ε :
      Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) ≤
        Real.sqrt ε := by
    exact Real.sqrt_le_sqrt hε
  have hgap_total :
      avgOver 𝒟 gap ≤ 2 * Real.sqrt ε := by
    calc
      avgOver 𝒟 gap
        ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := hgap_avg
      _ ≤ 2 * Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := hsdd_sqrt
      _ ≤ 2 * Real.sqrt ε := by
            exact mul_le_mul_of_nonneg_left hsqrt_ε (by positivity)
  have hsplit :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) =
        avgOver 𝒟 defectA + avgOver 𝒟 gap := by
    unfold idxSubMeasMass subMeasMass avgOver defectA gap diagA
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp [subMeasMass]
    ring
  have hfinal :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≤
        δ + 2 * Real.sqrt ε := by
    rw [hsplit]
    linarith
  linarith

end MIPStarRE.LDT.Preliminaries
