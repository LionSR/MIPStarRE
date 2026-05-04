import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta

/-!
# Self-consistency: core squared-mass bounds

Squared-mass lower bound lemma derived from bipartite self-consistency on
permutation-invariant states (`prop:cool-prop`).

## References

- arXiv:2009.12982, Section 7 (self-consistency preliminaries).
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

/-- `lem:completion-missing-mass-bound`.

This is the source-style missing-mass estimate used immediately before
`prop:completing-to-measurement` in the paper. The current formalization keeps
the left-register placement explicit via `leftTensor`. -/
theorem completionMissingMassBound {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (δ ζ : Error)
    (hssc : BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ)
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily B.liftLeft) δ) :
    ev ψ (leftTensor (ι₂ := ι)
      (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
        ((1 : MIPStarRE.Quantum.Op ι) - B.total))) ≤
      2 * Real.sqrt δ + ζ := by
  have hδ : qSDD ψ A.toSubMeas.liftLeft B.liftLeft ≤ δ := by
    simpa [constFamily_sdd_unit] using hclose.squaredDistanceBound
  let diagA : Error :=
    ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * B.outcome a))
  have hdiagA_lb : 1 - ζ ≤ diagA := by
    have hsq := bipartiteSSCSquaredMass ψ hperm A.toSubMeas ζ hssc
    have hmassA : ev ψ (leftTensor (ι₂ := ι) A.total) = 1 := by
      rw [A.total_eq_one, leftTensor_one]
      exact ev_one_of_isNormalized ψ hψ
    linarith
  have hgapA_raw :
      |diagA - overlap| ≤ Real.sqrt (qSDD ψ A.toSubMeas.liftLeft B.liftLeft) := by
    simpa [diagA, overlap, SubMeas.liftLeft, leftTensor_mul_leftTensor] using
      question_overlap_gap_left ψ hψ A.toSubMeas.liftLeft B.liftLeft
  have hgapA : diagA - overlap ≤ Real.sqrt δ := by
    exact le_trans (abs_le.mp hgapA_raw).2 (Real.sqrt_le_sqrt hδ)
  have hgapB_raw :
      |overlap - diagB| ≤ Real.sqrt (qSDD ψ A.toSubMeas.liftLeft B.liftLeft) := by
    simpa [diagB, overlap, SubMeas.liftLeft, leftTensor_mul_leftTensor] using
      question_overlap_gap_right ψ hψ A.toSubMeas.liftLeft B.liftLeft
  have hgapB : overlap - diagB ≤ Real.sqrt δ := by
    exact le_trans (abs_le.mp hgapB_raw).2 (Real.sqrt_le_sqrt hδ)
  have hdiagB_lb : 1 - ζ - 2 * Real.sqrt δ ≤ diagB := by
    linarith
  let R : MIPStarRE.Quantum.Op ι := (1 : MIPStarRE.Quantum.Op ι) - B.total
  let RL : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) R
  have hdiagB_le_mass : diagB ≤ ev ψ (leftTensor (ι₂ := ι) B.total) := by
    simpa [diagB, subMeasMass, SubMeas.liftLeft, leftTensor_mul_leftTensor] using
      subMeas_diagMass_le_mass ψ B.liftLeft
  have hRL_nonneg : 0 ≤ RL := by
    dsimp [RL, R]
    exact leftTensor_nonneg (ι₂ := ι) (sub_nonneg.mpr B.total_le_one)
  have hRL_le_one : RL ≤ 1 := by
    dsimp [RL, R]
    exact leftTensor_le_one (ι₂ := ι)
      (sub_le_self (1 : MIPStarRE.Quantum.Op ι) B.total_nonneg)
  have hRL_sq_le : RL * RL ≤ RL := by
    exact MIPStarRE.Quantum.sq_le_self hRL_nonneg hRL_le_one
  have hRL_rewrite : RL = 1 - leftTensor (ι₂ := ι) B.total := by
    dsimp [RL, R]
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [leftTensor, h₁, h₂, sub_eq_add_neg, add_comm]
  have hRL_ev : ev ψ RL ≤ 2 * Real.sqrt δ + ζ := by
    have hRL_eq : ev ψ RL = 1 - ev ψ (leftTensor (ι₂ := ι) B.total) := by
      rw [hRL_rewrite, ev_sub]
      simp [ev_one_of_isNormalized ψ hψ]
    linarith
  calc
    ev ψ (leftTensor (ι₂ := ι)
        (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
          ((1 : MIPStarRE.Quantum.Op ι) - B.total)))
      = ev ψ (RL * RL) := by
          simp [RL, R, leftTensor_mul_leftTensor]
    _ ≤ ev ψ RL := ev_mono ψ _ _ hRL_sq_le
    _ ≤ 2 * Real.sqrt δ + ζ := hRL_ev

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
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
      @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟 A A δ := by
  intro ⟨hssc⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed]
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

/-- Diagonal consistency for a full measurement is exactly bipartite strong
self-consistency.

This is the converse of `otherTwoNotionsOfSelfConsistency` in the special case
where the indexed family is measurement-valued.  Completeness identifies both
total-mass terms with the identity operator, so the self-`ConsRel` defect
`G ⊗ I ≃ I ⊗ G` and the diagonal SSC defect have the same questionwise
quantity. -/
theorem bipartiteSSCRel_of_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ →
      BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ := by
  intro ⟨hcons⟩
  constructor
  have hdefect :
      bipartiteSSCError ψ 𝒟 (IdxMeas.toIdxSubMeas A) =
        bipartiteConsError ψ 𝒟
          (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) := by
    unfold bipartiteSSCError bipartiteConsError
    apply avgOver_congr
    intro q
    simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
      IdxMeas.toIdxSubMeas, (A q).total_eq_one, leftTensor, opTensor]
  simpa [hdefect] using hcons

/-- For full measurements, bipartite SSC and diagonal self-consistency are
equivalent. -/
theorem bipartiteSSCRel_iff_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ ↔
      @ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas A) δ := by
  constructor
  · exact otherTwoNotionsOfSelfConsistency ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ
  · exact bipartiteSSCRel_of_consRel_self_measurement ψ 𝒟 A δ

end MIPStarRE.LDT.Preliminaries
