import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta

/-!
# Preliminary comparison theorems: completion and chain rules

Completion lemmas and final chain inequalities from the preliminaries chapter.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Local (single-register) version of the completion bound.
This is the original proof, preserved verbatim so it can be called
by the bipartite wrapper below. -/
private lemma closenessAfterCompletion_core_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (a0 : Outcome) (δ ζ : Error) :
    SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
    SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily (completeAtOutcome B a0).toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  intro ⟨hζ⟩ hdist
  rcases hdist with ⟨hδ⟩
  have hζ' :
      qSSCDefect ψ A.toSubMeas ≤ ζ := by
    simpa [constFamily_ssc_unit] using hζ
  have hδ' :
      qSDD ψ A.toSubMeas B ≤ δ := by
    simpa [constFamily_sdd_unit] using hδ
  have hBC :
      qSDD ψ B (completeAtOutcome B a0).toSubMeas =
        ev ψ (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
          ((1 : MIPStarRE.Quantum.Op ι) - B.total)) :=
    completion_self_distance ψ B a0
  let diagA : Error :=
    ∑ a : Outcome, ev ψ (A.toSubMeas.outcome a * A.toSubMeas.outcome a)
  let diagB : Error :=
    ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (A.toSubMeas.outcome a * B.outcome a)
  have hgap :
      |diagA - overlap| ≤ Real.sqrt δ ∧
        |overlap - diagB| ≤ Real.sqrt δ := by
    simpa [diagA, diagB, overlap, constSubMeasFamily, avgOver,
        uniformDistribution, uniformProbabilityDistribution] using
      easyApproxFromApproxDelta_twoFamily_of_probabilityDistribution ψ
        (uniformProbabilityDistribution Unit) hψ
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ (by exact ⟨hδ⟩)
  have hgapA_raw :
      |diagA - overlap| ≤ Real.sqrt δ := hgap.1
  have hgapA :
      diagA - overlap ≤ Real.sqrt δ := by
    exact (abs_le.mp hgapA_raw).2
  have hgapB_raw :
      |overlap - diagB| ≤ Real.sqrt δ := hgap.2
  have hgapB :
      overlap - diagB ≤ Real.sqrt δ := by
    exact (abs_le.mp hgapB_raw).2
  have hdiagA_lb : 1 - ζ ≤ diagA := by
    have hssc :
        max 0
            (ev ψ A.toSubMeas.total -
              ∑ a : Outcome, ev ψ (A.toSubMeas.outcome a * A.toSubMeas.outcome a))
          ≤ ζ := by
      simpa [qSSCDefect, diagA] using hζ'
    have hinner :
        ev ψ A.toSubMeas.total - diagA ≤ ζ := by
      exact le_trans (le_max_right 0 (ev ψ A.toSubMeas.total - diagA)) hssc
    have hmassA : ev ψ A.toSubMeas.total = 1 := by
      simpa [A.total_eq_one] using ev_one_of_isNormalized ψ hψ
    linarith
  have hdiagB_lb : 1 - ζ - 2 * Real.sqrt δ ≤ diagB := by
    linarith
  have hresidual_le :
      ev ψ (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
        ((1 : MIPStarRE.Quantum.Op ι) - B.total)) ≤
        2 * Real.sqrt δ + ζ := by
    let R : MIPStarRE.Quantum.Op ι := (1 : MIPStarRE.Quantum.Op ι) - B.total
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr B.total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op ι) B.total_nonneg
    have hR_sq_le : R * R ≤ R := by
      exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_ev :
        ev ψ (R * R) ≤ ev ψ R := by
      exact ev_mono ψ _ _ hR_sq_le
    have hmassB_sq :
        diagB ≤ ev ψ B.total := by
      calc
        diagB = ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a) := by rfl
        _ ≤ ∑ a : Outcome, ev ψ (B.outcome a) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (B.outcome_pos a) (B.outcome_le_one a)
        _ = ev ψ B.total := by
              rw [← ev_sum ψ B.outcome, B.sum_eq_total]
    have hmassB :
        ev ψ B.total ≥ diagB := by
      exact hmassB_sq
    have hR_ev' : ev ψ R ≤ 2 * Real.sqrt δ + ζ := by
      have hR_eq :
          ev ψ R = 1 - ev ψ B.total := by
        dsimp [R]
        rw [ev_sub]
        simp [ev_one_of_isNormalized ψ hψ]
      linarith
    have hRR :
        ev ψ (R * R) ≤ 2 * Real.sqrt δ + ζ := by
      exact le_trans hR_ev hR_ev'
    simpa [R] using hRR
  constructor
  rw [constFamily_sdd_unit]
  calc
    qSDD ψ A.toSubMeas (completeAtOutcome B a0).toSubMeas
      ≤ 2 * (qSDD ψ A.toSubMeas B +
          qSDD ψ B (completeAtOutcome B a0).toSubMeas) := by
            exact questionSDD_triangle ψ A.toSubMeas B
              (completeAtOutcome B a0).toSubMeas
    _ = 2 * (qSDD ψ A.toSubMeas B +
          ev ψ (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
            ((1 : MIPStarRE.Quantum.Op ι) - B.total))) := by
              rw [hBC]
    _ ≤ 2 * (δ +
          ev ψ (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
            ((1 : MIPStarRE.Quantum.Op ι) - B.total))) := by
              gcongr
    _ ≤ 2 * (δ + (2 * Real.sqrt δ + ζ)) := by
              gcongr
    _ = 2 * δ + 4 * Real.sqrt δ + 2 * ζ := by
          ring

/-- Bipartite wrapper for the completion bound.

The proof strategy: convert `BipartiteSSCRel` to local `SSCRel` on
left-lifted families via `bipartiteSSC_implies_localSSC_liftLeft`, then
invoke `closenessAfterCompletion_core_local` instantiated at `ι × ι`.
The wrapper builds the lifted measurement directly and rewrites the
completed lifted submeasurement back to the statement's
`(completeAtOutcome B a0).toSubMeas.liftLeft` form outcomewise. -/
private lemma closenessAfterCompletion_core {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (a0 : Outcome) (δ ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
    SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily B.liftLeft) δ →
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily (completeAtOutcome B a0).toSubMeas.liftLeft)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  intro hbipartite hsdd
  -- Bridge: convert BipartiteSSCRel to local SSCRel on left-lifted families
  have hlocal_ssc : SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft) ζ :=
    bipartiteSSC_implies_localSSC_liftLeft ψ hperm (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ
      (by simpa [constSubMeasFamily, IdxSubMeas.liftLeft] using hbipartite)
  -- Lift A to a full Measurement on ι × ι: total_eq_one follows from
  -- leftTensor 1 = 1 (Kronecker I ⊗ I = I on the product space).
  let A_lifted : Measurement Outcome (ι × ι) :=
    { toSubMeas := A.toSubMeas.liftLeft
      total_eq_one := by
        simpa [SubMeas.liftLeft, A.total_eq_one] using
          (leftTensor_one (ι₁ := ι) (ι₂ := ι)) }
  have hlocal :=
    closenessAfterCompletion_core_local ψ hψ A_lifted B.liftLeft a0 δ ζ
      hlocal_ssc hsdd
  rcases hlocal with ⟨hlocal_bound⟩
  have hlocal' :
      qSDD ψ A.toSubMeas.liftLeft (completeAtOutcome B.liftLeft a0).toSubMeas ≤
        2 * δ + 4 * Real.sqrt δ + 2 * ζ := by
    simpa [A_lifted, constFamily_sdd_unit] using hlocal_bound
  have hcomplete_outcome :
      ∀ a : Outcome,
        (completeAtOutcome B.liftLeft a0).toSubMeas.outcome a =
          ((completeAtOutcome B a0).toSubMeas.liftLeft).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [completeAtOutcome, SubMeas.liftLeft, leftTensor, sub_eq_add_neg,
          h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [completeAtOutcome, SubMeas.liftLeft, leftTensor, h, h₁, h₂]
  have hcomplete_q :
      qSDD ψ A.toSubMeas.liftLeft (completeAtOutcome B.liftLeft a0).toSubMeas =
        qSDD ψ A.toSubMeas.liftLeft (completeAtOutcome B a0).toSubMeas.liftLeft := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hcomplete_outcome a]
  constructor
  rw [constFamily_sdd_unit]
  rw [← hcomplete_q]
  exact hlocal'

/-- `prop:completing-to-measurement`.

The paper's hypothesis involves permutation-invariance; the bipartite
completion proof needs `PermInvState` to bridge `BipartiteSSCRel` to the
local `SSCRel` used in the algebraic completion bound. -/
theorem completingToMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (a0 : Outcome) (δ ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily B.liftLeft) δ →
      ∃ C : Measurement Outcome ι,
        CompletingToMeasStmt ψ A B C a0 δ ζ := by
  intro hsc hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion :=
      closenessAfterCompletion_core ψ hperm hψ A B a0 δ ζ hsc hdist
  }⟩

/-- Triangle inequality for state-dependent operator distance. -/
lemma sddOpRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceOpRel_triangle ψ 𝒟 A B C δ₁ δ₂

/-- Monotonicity for `SDDOpRel`. -/
lemma sddOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error) :
    SDDOpRel ψ 𝒟 A B δ → δ ≤ δ' → SDDOpRel ψ 𝒟 A B δ' := by
  intro h hle
  exact stateDependentDistanceOpRel_mono ψ 𝒟 A B δ δ' hle h

/-- Questionwise n-step chain bound: the squared distance between the
first and last operator family telescopes and is bounded by
`n * ∑ individual squared distances` via `ev_sum_conjTranspose_mul_sum_le`. -/
private lemma questionSDDOp_chain
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (n : ℕ)
    (families : Fin (n + 1) → OpFamily Outcome ι) :
    qSDDOp ψ (families 0) (families (Fin.last n)) ≤
      (n : ℝ) * ∑ i : Fin n,
        qSDDOp ψ (families i.castSucc) (families i.succ) := by
  -- Define the per-step difference operators
  let D : Fin n → Outcome → MIPStarRE.Quantum.Op ι := fun i a =>
    (families i.castSucc).outcome a - (families i.succ).outcome a
  -- Telescoping: total difference = sum of step differences
  have htelescope : ∀ a,
      (families 0).outcome a - (families (Fin.last n)).outcome a =
        ∑ i : Fin n, D i a := by
    intro a
    change (families 0).outcome a -
        (families (Fin.last n)).outcome a =
      ∑ i : Fin n, ((families i.castSucc).outcome a -
        (families i.succ).outcome a)
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add]
    exact (Fin.sum_univ_succ
      (fun j => (families j).outcome a)).symm.trans
      (Fin.sum_univ_castSucc
        (fun j => (families j).outcome a))
  unfold qSDDOp qSDDCore
  calc ∑ a : Outcome,
        ev ψ (((families 0).outcome a -
            (families (Fin.last n)).outcome a)ᴴ *
          ((families 0).outcome a -
            (families (Fin.last n)).outcome a))
      = ∑ a, ev ψ ((∑ i : Fin n, D i a)ᴴ *
          (∑ i : Fin n, D i a)) := by
        exact Finset.sum_congr rfl fun a _ => by
          rw [htelescope a]
    _ ≤ ∑ a, ((n : ℝ) * ∑ i : Fin n,
          ev ψ ((D i a)ᴴ * D i a)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have := ev_sum_conjTranspose_mul_sum_le ψ
          (fun i => D i a)
        rwa [Fintype.card_fin] at this
    _ = (n : ℝ) * ∑ i : Fin n, ∑ a,
          ev ψ ((D i a)ᴴ * D i a) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

/-- n-step SDDOpRel chain lemma via vector Cauchy-Schwarz.

Given `n` consecutive SDDOpRel bounds, the endpoints satisfy an SDDOpRel
bound with error `n * (∑ individual errors)`.  This improves on naive
triangle-inequality chaining, which would give exponential blowup.

Paper reference: `prop:triangle-inequality-for-approx_delta` in
`references/ldt-paper/preliminaries.tex`.

Proof sketch: telescoping + `‖∑ dᵢ|ψ⟩‖² ≤ n · ∑ ‖dᵢ|ψ⟩‖²`
(vector Cauchy-Schwarz / norm triangle inequality). -/
lemma sddOpRel_chain
    {Question Outcome : Type*} {ι' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype Outcome]
    (ψ : QuantumState ι') (𝒟 : Distribution Question)
    (n : ℕ)
    (families : Fin (n + 1) → IdxOpFamily Question Outcome ι')
    (errors : Fin n → Error)
    (hsteps : ∀ i : Fin n,
      SDDOpRel ψ 𝒟 (families i.castSucc) (families i.succ)
        (errors i)) :
    SDDOpRel ψ 𝒟 (families 0) (families (Fin.last n))
      ((n : Error) * ∑ i : Fin n, errors i) := by
  constructor
  unfold sddErrorOp at *
  -- Lift the questionwise chain bound through avgOver
  calc avgOver 𝒟 (fun q =>
        qSDDOp ψ (families 0 q) (families (Fin.last n) q))
      ≤ avgOver 𝒟 (fun q => (n : ℝ) * ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        exact avgOver_mono 𝒟 _ _ fun q =>
          questionSDDOp_chain ψ n (fun j => families j q)
    _ = (n : ℝ) * avgOver 𝒟 (fun q => ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        rw [avgOver_const_mul]
    _ = (n : ℝ) * ∑ i : Fin n, avgOver 𝒟 (fun q =>
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        congr 1
        simp only [avgOver, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ (n : ℝ) * ∑ i : Fin n, errors i := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ =>
            (hsteps i).squaredDistanceBound)
          (Nat.cast_nonneg n)


end MIPStarRE.LDT.Preliminaries
