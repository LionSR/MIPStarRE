import MIPStarRE.LDT.Preliminaries.CauchySchwarz
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Self-Consistency Extensions

Additional proposition statements from
`references/ldt-paper/preliminaries.tex`.

All five propositions from the paper are now fully proved. 
This file records the exact signatures together with proof-sketch comments

-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Squared mass lower bound from bipartite SSC (`prop:cool-prop`).

If A is ζ-strongly self-consistent on a permutation-invariant state, then
∑_a ⟨ψ| A_a² ⊗ I |ψ⟩ ≥ ∑_a ⟨ψ| A_a ⊗ I |ψ⟩ − ζ.

Proof:
1. Apply Cauchy-Schwarz to the families `A_a ⊗ I` and `I ⊗ A_a`.
2. Use permutation invariance to identify the two square-mass factors.
3. Conclude `∑ₐ ⟨ψ|(A_a)^2 ⊗ I|ψ⟩ ≥ ∑ₐ ⟨ψ|A_a ⊗ A_a|ψ⟩`.
4. Combine with `BipartiteSSCRel` on the constant `Unit`-indexed family. -/
theorem bipartiteSSCSquaredMass {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * A.outcome a)) ≥
        ev ψ (leftTensor (ι₂ := ι) A.total) - ζ := by
  intro hssc
  have hlocal :
      SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.liftLeft) ζ :=
    bipartiteSSC_implies_localSSC_liftLeft ψ hperm
      (uniformDistribution Unit) (constSubMeasFamily A) ζ <|
      by simpa [constSubMeasFamily, IdxSubMeas.liftLeft]
        using hssc
  rcases hlocal with ⟨hlocal⟩
  have hq : qSSCDefect ψ A.liftLeft ≤ ζ := by
    simpa [sscError, avgOver, uniformDistribution, constSubMeasFamily] using hlocal
  have hinner :
      ev ψ A.liftLeft.total -
          ∑ a : Outcome, ev ψ (A.liftLeft.outcome a * A.liftLeft.outcome a) ≤
        ζ := by
    exact le_trans (le_max_right 0 _) hq
  calc
    ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * A.outcome a))
      = ∑ a : Outcome, ev ψ (A.liftLeft.outcome a * A.liftLeft.outcome a) := by
          simp [SubMeas.liftLeft, leftTensor_mul_leftTensor]
    _ ≥ ev ψ A.liftLeft.total - ζ := by
          linarith
    _ = ev ψ (leftTensor (ι₂ := ι) A.total) - ζ := by
          simp [SubMeas.liftLeft]

/-- `prop:other-two-notions-of-self-consistency`.

Proof:
1. Expand `qConsDefect` for the left/right lifts.
2. Bound the total-overlap term `⟨ψ|A ⊗ A|ψ⟩` by `⟨ψ|A ⊗ I|ψ⟩`
   using `A.total ≤ I`.
3. The remaining expression is exactly the bipartite SSC defect.
4. Average over questions and use the hypothesis. -/
theorem otherTwoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (_hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
      ConsRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight A) δ := by
  intro ⟨hssc⟩
  constructor
  unfold consError
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q))
      ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          let M := A q
          have htotal_le :
              ev ψ (M.liftLeft.total * M.liftRight.total) ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) := by
            have hopTensor_le :
                opTensor M.total M.total ≤ leftTensor (ι₂ := ι) M.total := by
              have hrewrite :
                  leftTensor (ι₂ := ι) M.total - opTensor M.total M.total =
                    opTensor M.total (1 - M.total) := by
                have hneg :
                    Matrix.kronecker M.total (-M.total) =
                      -Matrix.kronecker M.total M.total := by
                  simpa using
                    (Matrix.kronecker_smul (-1 : ℂ) M.total M.total)
                calc
                  leftTensor (ι₂ := ι) M.total - opTensor M.total M.total
                    = Matrix.kronecker M.total 1 +
                        Matrix.kronecker M.total (-M.total) := by
                          rw [hneg]
                          simp [leftTensor, opTensor, sub_eq_add_neg]
                  _ = Matrix.kronecker M.total (1 - M.total) := by
                        simpa [sub_eq_add_neg] using
                          (Matrix.kronecker_add M.total 1 (-M.total)).symm
                  _ = opTensor M.total (1 - M.total) := by
                        simp [opTensor]
              change
                (leftTensor (ι₂ := ι) M.total - opTensor M.total M.total).PosSemidef
              rw [hrewrite]
              change Matrix.PosSemidef (Matrix.kronecker M.total (1 - M.total))
              exact
                Matrix.PosSemidef.kronecker
                  (Matrix.nonneg_iff_posSemidef.mp M.total_nonneg)
                  (Matrix.nonneg_iff_posSemidef.mp
                    (sub_nonneg.mpr M.total_le_one))
            have hmono :
                ev ψ (opTensor M.total M.total) ≤
                  ev ψ (leftTensor (ι₂ := ι) M.total) :=
              ev_mono ψ _ _ hopTensor_le
            simpa [SubMeas.liftLeft, SubMeas.liftRight,
              leftTensor_mul_rightTensor_eq_opTensor] using hmono
          have hmatch :
              qMatchMass ψ M.liftLeft M.liftRight =
                ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            simp [qMatchMass, SubMeas.liftLeft, SubMeas.liftRight,
              leftTensor_mul_rightTensor_eq_opTensor]
          have hinner :
              ev ψ (M.liftLeft.total * M.liftRight.total) -
                  qMatchMass ψ M.liftLeft M.liftRight ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [hmatch]
            exact sub_le_sub_right htotal_le _
          change
            max 0
                (ev ψ (M.liftLeft.total * M.liftRight.total) -
                  qMatchMass ψ M.liftLeft M.liftRight)
              ≤
            max 0
                (ev ψ (leftTensor (ι₂ := ι) M.total) -
                  ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)))
          exact max_le_max le_rfl hinner
    _ ≤ δ := hssc

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
      0 ≤ avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (𝒟.nonnegative q) (Real.sqrt_nonneg _)
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

/-- `prop:self-consistency-implies-data-processing`.

Proof:
1. First prove the “wrong-side” estimate
   `P_[f] ⊗ I ≈_{2δ + 4√ε} I ⊗ A_[f]` by:
   - expanding the `qSDD` square,
   - bounding the mass of `P` via `completenessTransferProjectiveP`,
   - comparing the mixed overlap with the diagonal overlap of `A`,
   - and using SSC plus postprocessing monotonicity.
2. Apply `twoNotionsOfSelfConsistencyAfterEvaluation` to obtain
   `A_[f] ⊗ I ≈_{2δ} I ⊗ A_[f]`.
3. Use the `SDDRel` triangle inequality to conclude
   `P_[f] ⊗ I ≈_{8δ + 8√ε} A_[f] ⊗ I`. -/
private lemma wrongSideEstimate
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ + 4 * Real.sqrt ε) := by
  intro hssc ⟨hε⟩
  let PL : IdxProjSubMeas Question α (ι × ι) := fun q =>
    { toSubMeas := ((P q).toSubMeas).liftLeft
      proj := by
        intro a
        simp [SubMeas.liftLeft, leftTensor_mul_leftTensor, (P q).proj a] }
  let LPf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f)
  let RAf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftRight (fun q => postprocess (A q) f)
  let crossPost : Question → Error := fun q =>
    qMatchMass ψ (LPf q) (RAf q)
  let crossOrig : Question → Error := fun q =>
    qMatchMass ψ
      ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P)) q)
      ((IdxSubMeas.liftRight A) q)
  let overlapA : Question → Error := fun q =>
    qMatchMass ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q)
  have hcomp :
      CompTransferStmt ψ 𝒟 (IdxSubMeas.liftLeft A) PL ε := by
    apply completenessTransferProjectiveP ψ 𝒟 hψ h𝒟 (IdxSubMeas.liftLeft A) PL ε
    exact
      sddRel_symm ψ 𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A) ε
        ⟨hε⟩
  have hmassP :
      idxSubMeasMass ψ 𝒟 LPf ≤
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε := by
    have hpost :
        idxSubMeasMass ψ 𝒟 LPf =
          idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas PL) := by
      unfold idxSubMeasMass subMeasMass avgOver LPf PL
      refine Finset.sum_congr rfl ?_
      intro q hq
      change
        𝒟.weight q *
            ev ψ (((postprocess ((P q).toSubMeas) f).liftLeft).total) =
          𝒟.weight q * ev ψ ((((P q).toSubMeas).liftLeft).total)
      simp [SubMeas.liftLeft, postprocess_total]
    have hbase := hcomp.completenessTransfer
    rw [hpost]
    linarith
  have hmassA :
      idxSubMeasMass ψ 𝒟 RAf =
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) := by
    unfold idxSubMeasMass subMeasMass avgOver RAf
    refine Finset.sum_congr rfl ?_
    intro q hq
    change
      𝒟.weight q *
          ev ψ (rightTensor (ι₁ := ι) ((postprocess (A q) f).total)) =
        𝒟.weight q * ev ψ (leftTensor (ι₂ := ι) ((A q).total))
    rw [postprocess_total, ← hperm.swap_ev ((A q).total)]
  have hcross_post_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 crossOrig := by
    unfold avgOver crossPost crossOrig
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (qMatchMass_leftRight_postprocess_ge ψ ((P q).toSubMeas) (A q) f)
      (𝒟.nonnegative q)
  have hcross_close :
      |avgOver 𝒟 crossOrig - avgOver 𝒟 overlapA| ≤ Real.sqrt ε := by
    simpa [crossOrig, overlapA, qMatchMass, IdxProjSubMeas.toIdxSubMeas,
      IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
      easyApproxFromApproxDelta ψ hψ 𝒟 h𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A)
        ε
        ⟨hε⟩
  have hcross_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 overlapA - Real.sqrt ε := by
    linarith [hcross_post_ge, (abs_le.mp hcross_close).1]
  have hssc_gap :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA ≤ δ := by
    rcases hssc with ⟨hssc⟩
    calc
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA
        = avgOver 𝒟
            (fun q =>
              subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              unfold idxSubMeasMass subMeasMass avgOver overlapA
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro q hq
              ring
      _ ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
            apply avgOver_mono
            intro q
            have hdef :
                qBipartiteSSCDefect ψ (A q) =
                  max 0 (subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              simp [qBipartiteSSCDefect, overlapA, qMatchMass, subMeasMass,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                SubMeas.liftLeft, SubMeas.liftRight,
                leftTensor_mul_rightTensor_eq_opTensor]
            rw [hdef]
            exact le_max_right 0 _
      _ ≤ δ := by
            simpa [bipartiteSSCError, overlapA, qMatchMass, IdxSubMeas.liftLeft,
              IdxSubMeas.liftRight] using hssc
  have hpointwise :
      ∀ q, qSDD ψ (LPf q) (RAf q) ≤
        subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q := by
    intro q
    let diagP : Error := ∑ b : β, ev ψ ((LPf q).outcome b * (LPf q).outcome b)
    let diagA : Error := ∑ b : β, ev ψ ((RAf q).outcome b * (RAf q).outcome b)
    have hdiagP_le :
        diagP ≤ subMeasMass ψ (LPf q) := by
      simpa [diagP, subMeasMass] using subMeas_diagMass_le_mass ψ (LPf q)
    have hdiagA_le :
        diagA ≤ subMeasMass ψ (RAf q) := by
      simpa [diagA, subMeasMass] using subMeas_diagMass_le_mass ψ (RAf q)
    have h_expand : qSDD ψ (LPf q) (RAf q) = diagP + diagA - 2 * crossPost q := by
      have hterm :
          ∀ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
                ((LPf q).outcome b - (RAf q).outcome b)) =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
        intro b
        have hcomm :
            ev ψ ((RAf q).outcome b * (LPf q).outcome b) =
              ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
          exact
            ev_mul_comm_of_psd ψ _ _
              ((RAf q).outcome_pos b)
              ((LPf q).outcome_pos b)
        calc
          ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
            =
              ev ψ
                ((((LPf q).outcome b * (LPf q).outcome b) -
                    (LPf q).outcome b * (RAf q).outcome b) -
                  ((RAf q).outcome b * (LPf q).outcome b -
                    (RAf q).outcome b * (RAf q).outcome b)) := by
                  congr 1
                  simp [sub_mul, mul_sub, SubMeas.outcome_hermitian]
                  abel
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) -
                ev ψ ((LPf q).outcome b * (RAf q).outcome b) -
                (ev ψ ((RAf q).outcome b * (LPf q).outcome b) -
                  ev ψ ((RAf q).outcome b * (RAf q).outcome b)) := by
                    rw [ev_sub, ev_sub, ev_sub]
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
                  rw [hcomm]
                  ring
      unfold qSDD qSDDCore crossPost
      calc
        ∑ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
          =
            ∑ b : β,
              (ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b)) := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  exact hterm b
        _ = diagP + diagA - 2 * qMatchMass ψ (LPf q) (RAf q) := by
              unfold diagP diagA qMatchMass
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand]
    linarith
  constructor
  calc
    sddError ψ 𝒟 LPf RAf
      ≤ avgOver 𝒟
          (fun q =>
            subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q) := by
              unfold sddError
              apply avgOver_mono
              intro q
              exact hpointwise q
    _ = idxSubMeasMass ψ 𝒟 LPf +
          idxSubMeasMass ψ 𝒟 RAf -
            2 * avgOver 𝒟 crossPost := by
              unfold idxSubMeasMass subMeasMass avgOver
              calc
                ∑ q ∈ 𝒟.support,
                    𝒟.weight q * (ev ψ (LPf q).total + ev ψ (RAf q).total - 2 * crossPost q)
                  =
                    ∑ q ∈ 𝒟.support,
                      (𝒟.weight q * ev ψ (LPf q).total +
                        (𝒟.weight q * ev ψ (RAf q).total - 2 * (𝒟.weight q * crossPost q))) := by
                          refine Finset.sum_congr rfl ?_
                          intro q hq
                          ring
                _ =
                    (∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (LPf q).total) +
                      ((∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (RAf q).total) -
                        2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * crossPost q) := by
                          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
                _ = idxSubMeasMass ψ 𝒟 LPf +
                    idxSubMeasMass ψ 𝒟 RAf -
                      2 * avgOver 𝒟 crossPost := by
                          simp [idxSubMeasMass, avgOver, subMeasMass]
                          ring
    _ ≤
        (idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε) +
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
            2 * (avgOver 𝒟 overlapA - Real.sqrt ε) := by
              rw [hmassA]
              linarith
    _ ≤ 2 * δ + 4 * Real.sqrt ε := by
          linarith

theorem selfConsistencyImpliesDataProcessing
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (8 * δ + 8 * Real.sqrt ε) := by
  intro hssc hsdd
  have hwrong :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ + 4 * Real.sqrt ε) :=
    wrongSideEstimate ψ hperm hψ 𝒟 h𝒟 A P δ ε f hssc hsdd
  have hself :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ) :=
    twoNotionsOfSelfConsistencyAfterEvaluation ψ hperm 𝒟 A δ f hssc
  have hself_symm :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (2 * δ) := by
    exact
      sddRel_symm ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ)
        hself
  have htri :
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (2 * ((2 * δ + 4 * Real.sqrt ε) + (2 * δ))) := by
    exact
      stateDependentDistanceRel_triangle ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (2 * δ + 4 * Real.sqrt ε) (2 * δ)
        hwrong hself_symm
  exact
    stateDependentDistanceRel_mono ψ 𝒟
      (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
      (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
      (2 * ((2 * δ + 4 * Real.sqrt ε) + (2 * δ)))
      (8 * δ + 8 * Real.sqrt ε)
      (by linarith)
      htri

end MIPStarRE.LDT.Preliminaries
