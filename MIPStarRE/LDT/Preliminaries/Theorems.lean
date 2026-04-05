import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
All operator fields use `Op ι` directly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) :
    ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ ↔
      ConsAgreement ψ 𝒟 A B δ := by
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

/-- Atomic mathematical fact: for a full measurement, the squared-distance defect
is at most `2 * qConsDefect`. -/
private lemma questionSDD_le_two_questionConsistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) :
    qSDD ψ A.toSubMeas B.toSubMeas ≤
      2 * qConsDefect ψ A.toSubMeas B.toSubMeas := by
  have hA_sq_sum_le : ∑ a, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (A.outcome a * A.outcome a)
        ≤ ∑ a, ev ψ (A.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a)
                  (Measurement.outcome_le_one A a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ A.outcome, A.sum_eq]
  have hB_sq_sum_le : ∑ a, ev ψ (B.outcome a * B.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (B.outcome a * B.outcome a)
        ≤ ∑ a, ev ψ (B.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (B.outcome_pos a)
                  (Measurement.outcome_le_one B a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ B.outcome, B.sum_eq]
  have h_expand : ∀ a,
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
        ev ψ (A.outcome a * A.outcome a) +
          ev ψ (B.outcome a * B.outcome a) -
          2 * ev ψ (A.outcome a * B.outcome a) := by
    intro a
    have hcomm :
        ev ψ (B.outcome a * A.outcome a) =
          ev ψ (A.outcome a * B.outcome a) :=
      ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
    calc
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ev ψ ((A.outcome a * A.outcome a - A.outcome a * B.outcome a) -
            (B.outcome a * A.outcome a - B.outcome a * B.outcome a)) := by
              congr 1
              simp [sub_mul, mul_sub, Measurement.outcome_hermitian]
              abel
      _ = ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a) -
            (ev ψ (B.outcome a * A.outcome a) -
              ev ψ (B.outcome a * B.outcome a)) := by
              rw [ev_sub, ev_sub, ev_sub]
      _ = ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a) := by
              rw [hcomm]
              ring
  have hbound :
      qSDD ψ A.toSubMeas B.toSubMeas ≤
        2 * (ev ψ (A.total * B.total) -
          qMatchMass ψ A.toSubMeas B.toSubMeas) := by
    unfold qSDD qSDDCore qMatchMass
    calc
      ∑ a, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact h_expand a
      _ = (∑ a, ev ψ (A.outcome a * A.outcome a)) +
            (∑ a, ev ψ (B.outcome a * B.outcome a)) -
            2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ev ψ 1 + ev ψ 1 - 2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              linarith
      _ = 2 * (ev ψ (A.total * B.total) -
            ∑ a, ev ψ (A.outcome a * B.outcome a)) := by
              simp [A.total_eq_one, B.total_eq_one]
              ring
  have hinner_nonneg :
      0 ≤ ev ψ (A.total * B.total) -
        qMatchMass ψ A.toSubMeas B.toSubMeas := by
    have hnonneg := qSDD_nonneg ψ A.toSubMeas B.toSubMeas
    linarith
  unfold qConsDefect
  rw [max_eq_right hinner_nonneg]
  exact hbound

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) :
    ConsRel ψ 𝒟
        (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) δ →
      BipartiteSDDRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDD ψ
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
      ≤ avgOver 𝒟
          (fun q =>
            2 * qConsDefect ψ
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let A' : Measurement Outcome (ι × ι) :=
            { toSubMeas := ((A q).toSubMeas).liftLeft
              total_eq_one := by
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                simp [SubMeas.liftLeft, leftTensor, (A q).total_eq_one] }
          let B' : Measurement Outcome (ι × ι) :=
            { toSubMeas := ((B q).toSubMeas).liftRight
              total_eq_one := by
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                simp [SubMeas.liftRight, rightTensor, (B q).total_eq_one] }
          simpa [A', B', IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas] using
            questionSDD_le_two_questionConsistency ψ A' B'
    _ = 2 * avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
          exact mul_le_mul_of_nonneg_left hcons (by norm_num)

private lemma ev_leftTensor_mul_rightTensor_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    {X Y : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ ev ψ (leftTensor (ι₂ := ι) X * rightTensor (ι₁ := ι) Y) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact
    ev_nonneg_of_psd ψ _ <|
      (Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp hX)
        (Matrix.nonneg_iff_posSemidef.mp hY)).nonneg

private lemma qMatchMass_leftRight_postprocess_ge {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ι) (postprocess A f))
        (rightPlacedSubMeas (ιA := ι) (postprocess B f)) ≥
      qMatchMass ψ
        (leftPlacedSubMeas (ιB := ι) A)
        (rightPlacedSubMeas (ιA := ι) B) := by
  classical
  let fiber : β → Finset α := fun b => Finset.univ.filter fun a => f a = b
  let diagTerm : α → Error := fun a =>
    ev ψ
      (leftTensor (ι₂ := ι) (A.outcome a) *
        rightTensor (ι₁ := ι) (B.outcome a))
  let pairTerm : α → α → Error := fun a a' =>
    ev ψ
      (leftTensor (ι₂ := ι) (A.outcome a) *
        rightTensor (ι₁ := ι) (B.outcome a'))
  let fiberDiag : β → Error := fun b => (fiber b).sum diagTerm
  let fiberPair : β → Error := fun b => (fiber b).sum fun a => (fiber b).sum fun a' => pairTerm a a'
  have hdiag_le (b : β) : fiberDiag b ≤ fiberPair b := by
    dsimp [fiberDiag, fiberPair]
    refine Finset.sum_le_sum ?_
    intro a ha
    exact Finset.single_le_sum
      (fun a' ha' =>
        ev_leftTensor_mul_rightTensor_nonneg ψ (A.outcome_pos a) (B.outcome_pos a'))
      ha
  have hfiber_expand (b : β) :
      ev ψ
        (((fiber b).sum fun a => leftTensor (ι₂ := ι) (A.outcome a)) *
          ((fiber b).sum fun a => rightTensor (ι₁ := ι) (B.outcome a))) =
      fiberPair b := by
    dsimp [fiberPair]
    rw [Matrix.sum_mul, ev_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Matrix.mul_sum, ev_finset_sum]
  calc
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ι) A)
        (rightPlacedSubMeas (ιA := ι) B)
      = ∑ b : β, fiberDiag b := by
          dsimp [fiberDiag, diagTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas
          symm
          exact Finset.sum_fiberwise Finset.univ f
            (fun a =>
              ev ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  rightTensor (ι₁ := ι) (B.outcome a)))
    _ ≤ ∑ b : β, fiberPair b := by
          refine Finset.sum_le_sum ?_
          intro b _
          exact hdiag_le b
    _ = qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) (postprocess A f))
          (rightPlacedSubMeas (ιA := ι) (postprocess B f)) := by
          dsimp [fiberPair, pairTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas postprocess
          refine Finset.sum_congr rfl ?_
          intro b _
          symm
          calc
            ev ψ
                (leftTensor (ι₂ := ι) (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) *
                  rightTensor (ι₁ := ι) (∑ a ∈ Finset.univ.filter (fun a => f a = b), B.outcome a))
              =
                ev ψ
                  (((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      leftTensor (ι₂ := ι) (A.outcome a)) *
                    ((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      rightTensor (ι₁ := ι) (B.outcome a))) := by
                    rw [← leftTensor_finset_sum (ι₂ := ι)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => A.outcome a)]
                    rw [← rightTensor_finset_sum (ι₁ := ι)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => B.outcome a)]
            _ = fiberPair b := hfiber_expand b

private lemma qConsDefect_leftRight_postprocess_le {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ι) (postprocess A f))
        (rightPlacedSubMeas (ιA := ι) (postprocess B f))
      ≤
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ι) A)
        (rightPlacedSubMeas (ιA := ι) B) := by
  have hmatch :=
    qMatchMass_leftRight_postprocess_ge ψ A B f
  have hsub :
      ev ψ
          ((leftPlacedSubMeas (ιB := ι) A).total *
            (rightPlacedSubMeas (ιA := ι) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) (postprocess A f))
          (rightPlacedSubMeas (ιA := ι) (postprocess B f))
      ≤
      ev ψ
          ((leftPlacedSubMeas (ιB := ι) A).total *
            (rightPlacedSubMeas (ιA := ι) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) A)
          (rightPlacedSubMeas (ιA := ι) B) := by
    linarith
  unfold qConsDefect
  have htotal :
      ev ψ
          ((leftPlacedSubMeas (ιB := ι) (postprocess A f)).total *
            (rightPlacedSubMeas (ιA := ι) (postprocess B f)).total) =
        ev ψ
          ((leftPlacedSubMeas (ιB := ι) A).total *
            (rightPlacedSubMeas (ιA := ι) B).total) := by
    simp [leftPlacedSubMeas, rightPlacedSubMeas, postprocess_total]
  rw [htotal]
  exact max_le_max le_rfl hsub

/-- `prop:simeq-data-processing`.

This is the paper-faithful opposite-side statement: the two families are first
placed on opposite tensor factors of a bipartite state, and only then
postprocessed. The generic same-side `qConsDefect` monotonicity statement is
false for arbitrary noncommuting submeasurements. -/
theorem simeqDataProcessing {Question α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question α ι) (δ : Error) (f : α → β) :
    ConsRel ψ 𝒟
      (fun q => leftPlacedSubMeas (ιB := ι) ((A q).toSubMeas))
      (fun q => rightPlacedSubMeas (ιA := ι) ((B q).toSubMeas)) δ →
      ConsRel ψ 𝒟
        (fun q => leftPlacedSubMeas (ιB := ι) (postprocess ((A q).toSubMeas) f))
        (fun q => rightPlacedSubMeas (ιA := ι) (postprocess ((B q).toSubMeas) f)) δ := by
  intro ⟨hcons⟩
  constructor
  unfold consError at *
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ
            (leftPlacedSubMeas (ιB := ι) (postprocess ((A q).toSubMeas) f))
            (rightPlacedSubMeas (ιA := ι) (postprocess ((B q).toSubMeas) f)))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              (leftPlacedSubMeas (ιB := ι) ((A q).toSubMeas))
              (rightPlacedSubMeas (ιA := ι) ((B q).toSubMeas))) := by
          apply avgOver_mono
          intro q
          exact qConsDefect_leftRight_postprocess_le ψ (A q).toSubMeas (B q).toSubMeas f
    _ ≤ δ := hcons

/-! ### Infrastructure: triangle inequality for `SDDRel` -/

/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDD`. -/
lemma questionSDD_triangle {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B C : SubMeas Outcome ι) :
    qSDD ψ A C ≤
      2 * (qSDD ψ A B +
           qSDD ψ B C) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have pointwise_outcome : ∀ a, ev' (A.outcome a) (C.outcome a) ≤
      2 * (ev' (A.outcome a) (B.outcome a) +
           ev' (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  unfold qSDD qSDDCore
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                 ev' (B.outcome a) (C.outcome a))) :=
    Finset.sum_le_sum (fun a _ => pointwise_outcome a)
  have h2 : ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                        ev' (B.outcome a) (C.outcome a))) =
      2 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
           ∑ a : Outcome, ev' (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Triangle inequality for state-dependent distance. -/
lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold sddError at *
  calc avgOver 𝒟
        (fun q => qSDD ψ (A q) (C q))
      ≤ avgOver 𝒟
          (fun q => 2 * (qSDD ψ (A q) (B q) +
                         qSDD ψ (B q) (C q))) := by
        apply avgOver_mono
        intro q
        exact questionSDD_triangle ψ (A q) (B q) (C q)
    _ = 2 * avgOver 𝒟
          (fun q => qSDD ψ (A q) (B q) +
                     qSDD ψ (B q) (C q)) := by
        rw [avgOver_const_mul]
    _ = 2 * (avgOver 𝒟
              (fun q => qSDD ψ (A q) (B q)) +
             avgOver 𝒟
              (fun q => qSDD ψ (B q) (C q))) := by
        rw [avgOver_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h₁ h₂

/-- Monotonicity: if `SDDRel` holds for `δ`, it holds for any `δ' ≥ δ`. -/
lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDRel ψ 𝒟 A B δ →
    SDDRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩

/-! ### Bridge lemmas for `prop:cons-sub-meas` -/

private lemma consSubMeas_controlHelper
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (P Q M N : SubMeas Outcome (ι × ι))
    (X : Outcome → MIPStarRE.Quantum.Op (ι × ι))
    (hSq :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) =
          ev ψ (X a * X a))
    (hX_nonneg : ∀ a : Outcome, 0 ≤ X a)
    (hX_le_one : ∀ a : Outcome, X a ≤ 1)
    (hSum :
      ∑ a : Outcome, ev ψ (X a) =
        ev ψ (P.total * Q.total) - qMatchMass ψ P Q) :
    qSDD ψ M N ≤ qConsDefect ψ P Q := by
  have hsummand :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) ≤
          ev ψ (X a) := by
    intro a
    calc
      ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
        = ev ψ (X a * X a) := hSq a
      _ ≤ ev ψ (X a) := by
          exact ev_mono ψ _ _ (MIPStarRE.Quantum.sq_le_self (hX_nonneg a) (hX_le_one a))
  have hnonneg :
      0 ≤ ev ψ (P.total * Q.total) - qMatchMass ψ P Q := by
    calc
      0 ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_nonneg fun a _ =>
            ev_nonneg_of_psd ψ _ (hX_nonneg a)
      _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum
  unfold qSDD qSDDCore qConsDefect
  rw [max_eq_right hnonneg]
  calc
    ∑ a : Outcome,
        ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
      ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_le_sum fun a _ => hsummand a
    _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum

private lemma consSubMeas_diagonalControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft A)
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) γ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
      (diagonalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((IdxSubMeas.liftLeft A) q) ((diagonalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((IdxSubMeas.liftLeft A) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [IdxSubMeas.liftLeft, SubMeas.liftLeft, diagonalSandwichFamily,
              LDT.leftTensor_mul_rightTensor_eq_opTensor, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_le_leftTensor
              ((A q).outcome_pos a)
              (Measurement.outcome_le_one (B q) a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_left :
                X a ≤ ((IdxSubMeas.liftLeft A) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            exact le_trans hX_le_left <|
              leftTensor_le_one (ι₂ := ι) ((A q).outcome_le_one a)
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((IdxSubMeas.liftLeft A) q))
            (((diagonalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            simp [X, hXh]
          · have hleft :
                ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
              simp [leftTensor_finset_sum, (A q).sum_eq_total]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                    ∑ a : Outcome,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                          simp [X, IdxSubMeas.liftLeft, SubMeas.liftLeft,
                            diagonalSandwichFamily, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                          unfold qMatchMass
                          simp [hleft, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                            SubMeas.liftLeft, SubMeas.liftRight, IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        have htotalOverlap :
                            ev ψ
                                ((((IdxSubMeas.liftLeft A) q).total) *
                                  (((IdxSubMeas.liftRight
                                      (IdxMeas.toIdxSubMeas B)) q).total)) =
                              ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                          rw [show (((IdxSubMeas.liftLeft A) q).total) *
                              (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total) =
                                leftTensor (ι₂ := ι) ((A q).total) *
                                  rightTensor (ι₁ := ι) ((B q).total) by rfl]
                          rw [(B q).total_eq_one]
                          simp [leftTensor, rightTensor]
                        rw [htotalOverlap]
    _ ≤ γ := hcons

private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft A)
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((diagonalSandwichFamily A B) q) ((totalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((totalSandwichFamily A B) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [totalSandwichFamily, LDT.leftTensor_mul_rightTensor_eq_opTensor,
              diagonalSandwichFamily, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_mono_left
              ((A q).outcome_le_total a)
              ((B q).outcome_pos a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_total :
                X a ≤ ((totalSandwichFamily A B) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            have htotal_le :
                ((totalSandwichFamily A B) q).outcome a ≤ 1 := by
              dsimp [totalSandwichFamily]
              have hop :
                  opTensor ((A q).total) ((B q).outcome a) ≤
                    leftTensor (ι₂ := ι) ((A q).total) := by
                exact MIPStarRE.LDT.opTensor_le_leftTensor
                  ((A q).total_nonneg)
                  (Measurement.outcome_le_one (B q) a)
              simpa [MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor] using
                le_trans hop (leftTensor_le_one (ι₂ := ι) (A q).total_le_one)
            exact le_trans hX_le_total htotal_le
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((diagonalSandwichFamily A B) q))
            (((totalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            have hneg :
                ((diagonalSandwichFamily A B) q).outcome a -
                    ((totalSandwichFamily A B) q).outcome a =
                  -(X a) := by
              simp [X]
            simp [hneg, hXh]
          · have htotal :
                ∑ a : Outcome,
                    ev ψ
                      (((totalSandwichFamily A B) q).outcome a) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => ((totalSandwichFamily A B) q).outcome a)]
              calc
                ev ψ (∑ a : Outcome, ((totalSandwichFamily A B) q).outcome a)
                  =
                    ev ψ
                      (∑ a : Outcome,
                        leftTensor (ι₂ := ι) ((A q).total) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            simp [totalSandwichFamily]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        ∑ a : Outcome, rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            rw [← Finset.mul_sum]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) (∑ a : Outcome, (B q).outcome a)) := by
                            rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ
                              (fun a : Outcome => (B q).outcome a)]
                _ =
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) 1) := by
                            rw [(B q).sum_eq]
                _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                            simp [leftTensor, rightTensor]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (((totalSandwichFamily A B) q).outcome a) -
                    ∑ a : Outcome, ev ψ (((diagonalSandwichFamily A B) q).outcome a) := by
                        simp [X, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        unfold qMatchMass
                        simp [htotal, diagonalSandwichFamily, IdxSubMeas.liftLeft,
                          IdxSubMeas.liftRight, SubMeas.liftLeft, SubMeas.liftRight,
                          IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        rw [show ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total =
                            rightTensor (ι₁ := ι) ((B q).total) by rfl]
                        rw [(B q).total_eq_one]
                        simp [IdxSubMeas.liftLeft, SubMeas.liftLeft, rightTensor, leftTensor]
    _ ≤ γ := hcons

private lemma consSubMeas_combinedControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
      (diagonalSandwichFamily A B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
      (totalSandwichFamily A B) (4 * γ) := by
  intro hAD hDT
  have h := stateDependentDistanceRel_triangle ψ 𝒟 (IdxSubMeas.liftLeft A)
    (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ γ
    hAD hDT
  exact stateDependentDistanceRel_mono ψ 𝒟 (IdxSubMeas.liftLeft A) (totalSandwichFamily A B)
    (2 * (γ + γ)) (4 * γ) (by linarith) h

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft A)
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) γ →
    ConsSubMeasStmt ψ 𝒟 A B γ := by
  intro hcons
  have hdc := consSubMeas_diagonalControl ψ 𝒟 A B γ hcons
  have hsc := consSubMeas_sandwichControl ψ 𝒟 A B γ hcons
  exact {
    diagonalControl := hdc
    sandwichControl := hsc
    combinedControl :=
      consSubMeas_combinedControl ψ 𝒟 A B γ hdc hsc
  }

/-! ### Bridge lemmas for `prop:switch-sandwich` -/

lemma weightedFinsetCauchySchwarz
    {Question Outcome : Type*}
    [Fintype Outcome]
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    (ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, 0 ≤ x q a)
    (hy : ∀ q a, 0 ≤ y q a) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
        Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
  unfold avgOver
  calc
    |∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, t q a|
      ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * ∑ a : Outcome, t q a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |∑ a : Outcome, t q a| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support,
          𝒟.weight q *
            (Real.sqrt (∑ a : Outcome, x q a) *
              Real.sqrt (∑ a : Outcome, y q a)) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have hq :
              |∑ a : Outcome, t q a| ≤
                Real.sqrt (∑ a : Outcome, x q a) *
                  Real.sqrt (∑ a : Outcome, y q a) := by
            calc
              |∑ a : Outcome, t q a|
                ≤ ∑ a : Outcome, |t q a| := by
                    exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : Outcome, Real.sqrt (x q a) * Real.sqrt (y q a) := by
                    refine Finset.sum_le_sum ?_
                    intro a _
                    exact ht q a
              _ ≤ Real.sqrt (∑ a : Outcome, x q a) *
                    Real.sqrt (∑ a : Outcome, y q a) := by
                    exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                      (f := fun a => x q a) (g := fun a => y q a)
                      (fun a => hx q a) (fun a => hy q a)
          exact mul_le_mul_of_nonneg_left hq (𝒟.nonnegative q)
    _ = ∑ q ∈ 𝒟.support,
          Real.sqrt (𝒟.weight q * ∑ a : Outcome, x q a) *
            Real.sqrt (𝒟.weight q * ∑ a : Outcome, y q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          have hsx : 0 ≤ ∑ a : Outcome, x q a := by
            exact Finset.sum_nonneg fun a _ => hx q a
          have hsy : 0 ≤ ∑ a : Outcome, y q a := by
            exact Finset.sum_nonneg fun a _ => hy q a
          rw [Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, x q a)
                (𝒟.nonnegative q),
              Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, y q a)
                (𝒟.nonnegative q)]
          ring_nf
          rw [Real.sq_sqrt (𝒟.nonnegative q)]
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, y q a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := 𝒟.support)
              (f := fun q => 𝒟.weight q * ∑ a : Outcome, x q a)
              (g := fun q => 𝒟.weight q * ∑ a : Outcome, y q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hx q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hy q a)
    _ = Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
            rfl

/-- The diagonal mass of a sub-measurement is bounded by its total mass. -/
lemma subMeas_diagMass_le_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a) (A.outcome_le_one a)
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- The diagonal mass of a sub-measurement is at most `1` on a normalized state. -/
lemma subMeas_diagMass_le_one
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ 1 := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ev ψ A.total := subMeas_diagMass_le_mass ψ A
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
          exact ev_mono ψ _ _ A.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

/-- Projective outcomes satisfy `P_a^2 = P_a`, so diagonal mass equals total mass. -/
lemma projSubMeas_diagMass_eq_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : ProjSubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) = ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      = ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [A.proj a]
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- Each projective outcome is absorbed by the total projector. -/
lemma projSubMeas_outcome_mul_total_eq_outcome
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) (a : Outcome) :
    A.outcome a * A.total = A.outcome a := by
  let P := A.outcome a
  let R : MIPStarRE.Quantum.Op ι := 1 - A.total
  have hP_herm : Pᴴ = P := by
    simpa [P] using A.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr A.total_le_one
  have hR_le_self : R ≤ 1 - P := by
    simpa [R, P] using
      sub_le_sub_left (A.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPRP_nonneg : 0 ≤ P * R * P := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hP_herm
  have hP_one_sub_P : P * (1 - P) * P = 0 := by
    calc
      P * (1 - P) * P = (P * 1 - P * P) * P := by rw [mul_sub]
      _ = 0 := by simp [P, A.proj a]
  have hPRP_eq_zero : P * R * P = 0 := by
    apply le_antisymm
    · calc
        P * R * P ≤ P * (1 - P) * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_le_self
        _ = 0 := hP_one_sub_P
    · simpa using hPRP_nonneg
  have hA_total_herm : A.totalᴴ = A.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hA_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) A.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRP_conj_mul : (R * P)ᴴ * (R * P) = P * (R * R) * P := by
    calc
      (R * P)ᴴ * (R * P) = (Pᴴ * Rᴴ) * (R * P) := by
        simp [Matrix.conjTranspose_mul]
      _ = P * (R * R) * P := by simp [hP_herm, hR_herm, mul_assoc]
  have hRP_eq_zero : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRP_conj_mul]
    apply le_antisymm
    · calc
        P * (R * R) * P ≤ P * R * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_sq_le
        _ = 0 := hPRP_eq_zero
    · have hnonneg : 0 ≤ P * (R * R) * P := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hP_herm
      simpa using hnonneg
  calc
    A.outcome a * A.total = P * (1 - R) := by
      simp [P, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = P - P * R := by rw [mul_sub, mul_one]
    _ = P := by
          have : P * R = 0 := by
            simpa [hP_herm, hR_herm] using congrArg Matrix.conjTranspose hRP_eq_zero
          simp [this]
    _ = A.outcome a := by rfl

/-- The total operator of a projective sub-measurement is itself a projector. -/
lemma projSubMeas_total_proj
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) :
    A.total * A.total = A.total := by
  calc
    A.total * A.total = (∑ a : Outcome, A.outcome a) * A.total := by
      rw [A.sum_eq_total]
    _ = ∑ a : Outcome, A.outcome a * A.total := by
      rw [Matrix.sum_mul]
    _ = ∑ a : Outcome, A.outcome a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact projSubMeas_outcome_mul_total_eq_outcome A a
    _ = A.total := A.sum_eq_total

/-- Any `OpBounded01` operator is bounded above by the identity. -/
private lemma opBounded01_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B ≤ 1 :=
  sub_nonneg.mp hB.boundedByIdentity

/-- Any `OpBounded01` operator is Hermitian. -/
private lemma opBounded01_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    Bᴴ = B :=
  (Matrix.nonneg_iff_posSemidef.mp hB.nonnegative).isHermitian.eq

/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
private lemma opBounded01_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B * B ≤ 1 := by
  exact le_trans
    (MIPStarRE.Quantum.sq_le_self hB.nonnegative (opBounded01_le_one hB))
    (opBounded01_le_one hB)

/-- Left tensoring preserves the `0 ≤ B ≤ 1` bounds. -/
private lemma leftTensor_opBounded01
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B : MIPStarRE.Quantum.Op ι₁} (hB : OpBounded01 B) :
    OpBounded01 (leftTensor (ι₂ := ι₂) B) := by
  constructor
  · exact leftTensor_nonneg (ι₂ := ι₂) hB.nonnegative
  · exact sub_nonneg.mpr (leftTensor_le_one (ι₂ := ι₂) (opBounded01_le_one hB))

lemma avgOver_abs_le_sqrt_of_pointwise
    {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g) := by
  have hcs :=
    weightedFinsetCauchySchwarz
      (Question := Question) (Outcome := Unit) 𝒟
      (t := fun q _ => f q)
      (x := fun q _ => g q)
      (y := fun _ _ => 1)
      (ht := by
        intro q _
        simpa using hf q)
      (hx := by
        intro q _
        exact hg q)
      (hy := by
        intro _ _
        positivity)
  have hmass : avgOver 𝒟 (fun _ => (1 : Error)) ≤ 1 := by
    simpa [avgOver] using h𝒟
  have hsqrt_mass : Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hmass
  calc
    |avgOver 𝒟 f|
      ≤ Real.sqrt (avgOver 𝒟 g) *
          Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) := by
            simpa using hcs
    _ ≤ Real.sqrt (avgOver 𝒟 g) * 1 := by
          exact mul_le_mul_of_nonneg_left hsqrt_mass (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 g) := by ring

private lemma question_overlap_gap_left
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (A.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagA := by
            simpa [diagA] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (A.outcome a * A.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (A.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
            simp [qSDD, qSDDCore, diagA]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * A.outcome a) -
            ev ψ (A.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (B.outcome a * A.outcome a) = ev ψ (A.outcome a * B.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
          calc
            ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a)
              = ev ψ (A.outcome a * A.outcome a) - ev ψ (B.outcome a * A.outcome a) := by
                  rw [hcomm]
            _ 
              = ev ψ (A.outcome a * A.outcome a - B.outcome a * A.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * A.outcome a) (B.outcome a * A.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
                  simp [sub_mul]

private lemma question_overlap_gap_right
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagB : Error := ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  have hdiagB_le_one : diagB ≤ 1 := by
    simpa [diagB] using subMeas_diagMass_le_one ψ hψ B
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (B.outcome a * B.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (B.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagB := by
            simpa [diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (B.outcome a * B.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (B.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
            simp [qSDD, qSDDCore, diagB]
  have hsqrtB : Real.sqrt diagB ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagB_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (B.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (A.outcome a * B.outcome a) = ev ψ (B.outcome a * A.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)
          calc
            ev ψ (A.outcome a * B.outcome a) - ev ψ (B.outcome a * B.outcome a)
              = ev ψ (A.outcome a * B.outcome a - B.outcome a * B.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * B.outcome a) (B.outcome a * B.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
                  simp [sub_mul]

private lemma sum_ev_mul_leftBounded_le_of_leftHermitian
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι)
    (LB : MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))|
      ≤ ∑ a : Outcome, |ev ψ (X a * (LB * Y a))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (ev ψ (X a * X a)) *
            Real.sqrt (ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          refine Finset.sum_le_sum ?_
          intro a _
          simpa [hXherm a] using
            ev_abs_mul_le_sqrt ψ (X a) (LB * Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => ev ψ (X a * X a))
              (g := fun a => ev ψ (((LB * Y a)ᴴ) * (LB * Y a)))
              (fun a => by
                simpa [hXherm a] using ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => by
                exact ev_adjoint_self_nonneg ψ (LB * Y a))
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
          apply mul_le_mul
          · exact le_rfl
          · exact Real.sqrt_le_sqrt <| Finset.sum_le_sum fun a _ => by
              have hsand :
                  Y a * (LB * LB) * Y a ≤ Y a * 1 * Y a := by
                exact MIPStarRE.Quantum.sandwich_mono (hYherm a) hLB_sq_le_one
              have hev := ev_mono ψ _ _ hsand
              simpa [hLB_herm, hYherm a, Matrix.conjTranspose_mul, mul_assoc] using hev
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _

-- NOTE: `question_switchSandwich_left_gap` and `question_switchSandwich_middle_gap`
-- are each ~330 lines. The shared OpBounded01 setup has been extracted into
-- `leftTensor_opBounded01_*` helpers above. The shared
-- `sum_ev_mul_leftBounded_le_of_leftHermitian` lemma now packages the
-- Cauchy-Schwarz application plus the `LB * LB ≤ 1` sandwich contraction,
-- while the two long proofs keep their distinct rewrite skeletons.
private lemma question_switchSandwich_left_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B) :
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hLB : OpBounded01 LB := by
    dsimp [LB]
    exact leftTensor_opBounded01 (ι₂ := ι) hB
  have hLB_nonneg : 0 ≤ LB := by
    exact hLB.nonnegative
  have hLB_herm : LBᴴ = LB := by
    exact opBounded01_hermitian hLB
  have hLB_sq_le_one : LB * LB ≤ 1 := by
    exact opBounded01_sq_le_one hLB
  have hLAherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a))).isHermitian.eq
  have hRAherm :
      ∀ a : Outcome,
        (rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι) (A.outcome_pos a))).isHermitian.eq
  have hDherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a) -
          rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    simp [hLAherm a, hRAherm a]
  have haux :
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := by
    simpa using
      sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a => leftTensor (ι₂ := ι) (A.outcome a))
        (fun a =>
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hLAherm hDherm
  have hdiag_le_one :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) (A.outcome a)) ≤ 1 := by
    simpa [SubMeas.liftLeft] using
      subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftLeft
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) (A.outcome a))) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := haux
      _ ≤ 1 *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_diag (Real.sqrt_nonneg _)
      _ = Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (((leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            (LB *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) B *
              leftTensor (ι₂ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                leftTensor (ι₂ := ι) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                (LB *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  leftTensor (ι₂ := ι) (A.outcome a))
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))).symm]
            simp [LB, mul_assoc, mul_sub]
  calc
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [qSDD, qSDDCore, SubMeas.liftLeft, SubMeas.liftRight]

private lemma question_switchSandwich_middle_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B) :
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hLB : OpBounded01 LB := by
    dsimp [LB]
    exact leftTensor_opBounded01 (ι₂ := ι) hB
  have hLB_nonneg : 0 ≤ LB := by
    exact hLB.nonnegative
  have hLB_herm : LBᴴ = LB := by
    exact opBounded01_hermitian hLB
  have hLB_sq_le_one : LB * LB ≤ 1 := by
    exact opBounded01_sq_le_one hLB
  have hLAherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a))).isHermitian.eq
  have hRAherm :
      ∀ a : Outcome,
        (rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι) (A.outcome_pos a))).isHermitian.eq
  have hDherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a) -
          rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    simp [hLAherm a, hRAherm a]
  have haux :
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (rightTensor (ι₁ := ι) (A.outcome a) *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
    simpa [hRAherm] using
      sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a =>
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a))
        (fun a => rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hDherm hRAherm
  have hdiag_le_one :
      ∑ a : Outcome,
        ev ψ
          (rightTensor (ι₁ := ι) (A.outcome a) *
            rightTensor (ι₁ := ι) (A.outcome a)) ≤ 1 := by
    simpa [SubMeas.liftRight] using
      subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftRight
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (rightTensor (ι₁ := ι) (A.outcome a) *
              rightTensor (ι₁ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (rightTensor (ι₁ := ι) (A.outcome a) *
                    rightTensor (ι₁ := ι) (A.outcome a))) := haux
      _ ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrt_diag (Real.sqrt_nonneg _)
      _ =
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        ev ψ
          ((leftTensor (ι₂ := ι) (A.outcome a) -
              rightTensor (ι₁ := ι) (A.outcome a)) *
            (LB * rightTensor (ι₁ := ι) (A.outcome a))) := by
    calc
      (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            ev ψ
              ((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)) *
                (LB * rightTensor (ι₁ := ι) (A.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))
                (leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))).symm]
            have hRcomm :
                rightTensor (ι₁ := ι) (A.outcome a) *
                    leftTensor (ι₂ := ι) B =
                  leftTensor (ι₂ := ι) B *
                    rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                rightTensor (ι₁ := ι) (A.outcome a) *
                    leftTensor (ι₂ := ι) B
                  = opTensor B (A.outcome a) := by
                      simpa [rightTensor, leftTensor, opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : MIPStarRE.Quantum.Op ι) B
                          (A.outcome a) (1 : MIPStarRE.Quantum.Op ι)).symm
                _ = leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
            refine congrArg (ev ψ) ?_
            have hRA_mul :
                rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) =
                  LB * rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a))
                  = (rightTensor (ι₁ := ι) (A.outcome a) * LB) *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                        simp [mul_assoc]
                _ = (LB * rightTensor (ι₁ := ι) (A.outcome a)) *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                        rw [hRcomm]
                _ = LB *
                      (rightTensor (ι₁ := ι) (A.outcome a) *
                        rightTensor (ι₁ := ι) (A.outcome a)) := by
                        simp [mul_assoc]
                _ = LB * rightTensor (ι₁ := ι) (A.outcome a) := by
                      have hRAproj :
                          rightTensor (ι₁ := ι) (A.outcome a) *
                              rightTensor (ι₁ := ι) (A.outcome a) =
                            rightTensor (ι₁ := ι) (A.outcome a) := by
                        simpa [rightTensor, A.proj a] using
                          (Matrix.mul_kronecker_mul
                            (1 : MIPStarRE.Quantum.Op ι)
                            (1 : MIPStarRE.Quantum.Op ι)
                            (A.outcome a) (A.outcome a)).symm
                      simp [hRAproj]
            calc
              leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a) -
                leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a)
                =
                leftTensor (ι₂ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) -
                  rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [LB, mul_assoc, hRA_mul]
              _ =
                (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (LB * rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [sub_mul]
  calc
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            ev ψ
              ((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [qSDD, qSDDCore, SubMeas.liftLeft, SubMeas.liftRight, hDherm]


private lemma switchSandwich_leftTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B| ≤
      2 * Real.sqrt δ := by
  intro happrox
  let inter : Error :=
    avgOver 𝒟 fun q =>
      ∑ a, ev ψ
        (leftTensor (ι₂ := ι) ((A q).outcome a) *
          leftTensor (ι₂ := ι) B *
          rightTensor (ι₁ := ι) ((A q).outcome a))
  have hδ :
      avgOver 𝒟
        (fun q =>
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [BipartiteSDDRel, sddError, IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using happrox.leftRightSquaredDistanceBound
  have hleft_gap :
      |leftSandwichExpectation ψ 𝒟 A B - inter| ≤ Real.sqrt δ := by
    calc
      |leftSandwichExpectation ψ 𝒟 A B - inter|
        = |avgOver 𝒟 (fun q =>
            (∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                leftTensor (ι₂ := ι) ((A q).outcome a))) -
            ∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [leftSandwichExpectation, inter, avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (avgOver 𝒟
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      leftTensor (ι₂ := ι) ((A q).outcome a))) -
                  ∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    question_switchSandwich_left_gap ψ hψ (A q) B hB)
                (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  have hmiddle_gap :
      |inter - middleSandwichExpectation ψ 𝒟 A B| ≤ Real.sqrt δ := by
    calc
      |inter - middleSandwichExpectation ψ 𝒟 A B|
        = |avgOver 𝒟 (fun q =>
            (∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a))) -
            ∑ a, ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [middleSandwichExpectation, inter, avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (avgOver 𝒟
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) -
                  ∑ a, ev ψ
                    (leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    question_switchSandwich_middle_gap ψ hψ (A q) B hB)
                (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  calc
    |leftSandwichExpectation ψ 𝒟 A B - middleSandwichExpectation ψ 𝒟 A B|
      ≤
        |leftSandwichExpectation ψ 𝒟 A B - inter| +
          |inter - middleSandwichExpectation ψ 𝒟 A B| := by
            exact
              abs_sub_le
                (leftSandwichExpectation ψ 𝒟 A B)
                inter
                (middleSandwichExpectation ψ 𝒟 A B)
    _ ≤ Real.sqrt δ + Real.sqrt δ := add_le_add hleft_gap hmiddle_gap
    _ = 2 * Real.sqrt δ := by ring

private lemma switchSandwich_rightTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  intro happrox
  have hδ :
      avgOver 𝒟
        (fun q =>
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [BipartiteSDDRel, sddError, IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using happrox.leftRightSquaredDistanceBound
  have hpointwise :
      ∀ q,
        |(∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))| ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
    intro q
    classical
    let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
    let LT : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) ((A q).total)
    let RT : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) ((A q).total)
    have hLB : OpBounded01 LB := by
      dsimp [LB]
      exact leftTensor_opBounded01 (ι₂ := ι) hB
    have hLB_nonneg : 0 ≤ LB := by
      exact hLB.nonnegative
    have hLB_herm : LBᴴ = LB := by
      exact opBounded01_hermitian hLB
    have hLB_sq_le_one : LB * LB ≤ 1 := by
      exact opBounded01_sq_le_one hLB
    have hLT_nonneg : 0 ≤ LT := by
      dsimp [LT]
      exact leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hRT_nonneg : 0 ≤ RT := by
      dsimp [RT]
      exact rightTensor_nonneg (ι₁ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hLT_herm : LTᴴ = LT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hLT_nonneg).isHermitian.eq
    have hRT_herm : RTᴴ = RT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hRT_nonneg).isHermitian.eq
    have hLT_proj : LT * LT = LT := by
      calc
        LT * LT
          = leftTensor (ι₂ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [LT]
              simpa [leftTensor] using
                (Matrix.mul_kronecker_mul
                  ((A q).total) ((A q).total)
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
        _ = LT := by
              rw [projSubMeas_total_proj (A q)]
    have hRT_proj : RT * RT = RT := by
      calc
        RT * RT
          = rightTensor (ι₁ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [RT]
              simpa [rightTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                  ((A q).total) ((A q).total)).symm
        _ = RT := by
              rw [projSubMeas_total_proj (A q)]
    have hLTRT_comm : LT * RT = RT * LT := by
      calc
        LT * RT
          = opTensor ((A q).total) ((A q).total) := by
              dsimp [LT, RT]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = RT * LT := by
              dsimp [RT, LT]
              simpa [rightTensor, leftTensor, opTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) ((A q).total)
                  ((A q).total) (1 : MIPStarRE.Quantum.Op ι))
    have hLB_diag_le_one : ev ψ (LBᴴ * LB) ≤ 1 := by
      have hmono : ev ψ (LB * LB) ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
        exact ev_mono ψ _ _ hLB_sq_le_one
      simpa [hLB_herm, ev_one_of_isNormalized ψ hψ] using hmono
    have hsqrt_LB : Real.sqrt (ev ψ (LBᴴ * LB)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hLB_diag_le_one
    have hLT_ev :
        ev ψ LT =
          ∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) := by
      dsimp [LT]
      rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
      simp [leftTensor_finset_sum, (A q).sum_eq_total]
    have hRT_ev :
        ev ψ RT =
          ∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) := by
      dsimp [RT]
      rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ι) ((A q).outcome a))]
      simp [rightTensor_finset_sum, (A q).sum_eq_total]
    have hdiag_le_cross :
        ∑ a,
          ev ψ
            (leftTensor (ι₂ := ι) ((A q).outcome a) *
              rightTensor (ι₁ := ι) ((A q).outcome a)) ≤
          ev ψ (LT * RT) := by
      calc
        ∑ a,
            ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                rightTensor (ι₁ := ι) ((A q).outcome a))
          ≤
            ∑ a,
              ∑ b,
                ev ψ
                  (leftTensor (ι₂ := ι) ((A q).outcome a) *
                    rightTensor (ι₁ := ι) ((A q).outcome b)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact Finset.single_le_sum
                (fun b _ =>
                  ev_leftTensor_mul_rightTensor_nonneg ψ
                    ((A q).outcome_pos a) ((A q).outcome_pos b))
                (by simp)
        _ =
            ev ψ (LT * RT) := by
              calc
                ∑ a,
                    ∑ b,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((A q).outcome b))
                  =
                    ∑ a,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [← ev_sum ψ
                        (fun b : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            rightTensor (ι₁ := ι) ((A q).outcome b))]
                      rw [Matrix.mul_sum]
                _ =
                    ev ψ
                      (∑ a,
                        leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [← ev_sum ψ
                        (fun a : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            ∑ b,
                              rightTensor (ι₁ := ι) ((A q).outcome b))]
                _ =
                    ev ψ
                      ((∑ a,
                          leftTensor (ι₂ := ι) ((A q).outcome a)) *
                        ∑ b,
                          rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [Finset.sum_mul]
                _ = ev ψ (LT * RT) := by
                      simp [LT, RT, leftTensor_finset_sum, rightTensor_finset_sum,
                        (A q).sum_eq_total]
    have htotal_sq_le :
        ev ψ ((RT - LT)ᴴ * (RT - LT)) ≤
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
      have hDherm : (RT - LT)ᴴ = RT - LT := by
        simp [hRT_herm, hLT_herm]
      have hD_expand :
          (RT - LT)ᴴ * (RT - LT) = RT + LT - (2 : Error) • (LT * RT) := by
        have hmul :
            (RT - LT) * (RT - LT) = RT * RT - RT * LT - LT * RT + LT * LT := by
          noncomm_ring
        calc
          (RT - LT)ᴴ * (RT - LT)
            = (RT - LT) * (RT - LT) := by simp [hDherm]
          _ = RT * RT - RT * LT - LT * RT + LT * LT := hmul
          _ = RT + LT - (2 : Error) • (LT * RT) := by
                rw [hRT_proj, hLT_proj, hLTRT_comm]
                simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hq_expand :
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) =
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
        unfold qSDD qSDDCore
        calc
          ∑ a,
              ev ψ
                ((((leftTensor (ι₂ := ι) ((A q).outcome a) -
                        rightTensor (ι₁ := ι) ((A q).outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) ((A q).outcome a) -
                      rightTensor (ι₁ := ι) ((A q).outcome a))))
            =
              ∑ a,
                (ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) +
                  ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                  2 *
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                let LA : MIPStarRE.Quantum.Op (ι × ι) :=
                  leftTensor (ι₂ := ι) ((A q).outcome a)
                let RA : MIPStarRE.Quantum.Op (ι × ι) :=
                  rightTensor (ι₁ := ι) ((A q).outcome a)
                have hLA_nonneg : 0 ≤ LA := by
                  dsimp [LA]
                  exact leftTensor_nonneg (ι₂ := ι) ((A q).outcome_pos a)
                have hRA_nonneg : 0 ≤ RA := by
                  dsimp [RA]
                  exact rightTensor_nonneg (ι₁ := ι) ((A q).outcome_pos a)
                have hLA_herm : LAᴴ = LA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hLA_nonneg).isHermitian.eq
                have hRA_herm : RAᴴ = RA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hRA_nonneg).isHermitian.eq
                have hLA_proj : LA * LA = LA := by
                  calc
                    LA * LA
                      = leftTensor (ι₂ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [LA]
                          simpa [leftTensor] using
                            (Matrix.mul_kronecker_mul
                              ((A q).outcome a) ((A q).outcome a)
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
                    _ = LA := by
                          rw [(A q).proj a]
                have hRA_proj : RA * RA = RA := by
                  calc
                    RA * RA
                      = rightTensor (ι₁ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [RA]
                          simpa [rightTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                              ((A q).outcome a) ((A q).outcome a)).symm
                    _ = RA := by
                          rw [(A q).proj a]
                have hcomm : LA * RA = RA * LA := by
                  calc
                    LA * RA
                      = opTensor ((A q).outcome a) ((A q).outcome a) := by
                          dsimp [LA, RA]
                          rw [leftTensor_mul_rightTensor_eq_opTensor]
                    _ = RA * LA := by
                          dsimp [RA, LA]
                          simpa [rightTensor, leftTensor, opTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) ((A q).outcome a)
                              ((A q).outcome a) (1 : MIPStarRE.Quantum.Op ι))
                have hmul :
                    (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
                  noncomm_ring
                calc
                  ev ψ (((LA - RA)ᴴ) * (LA - RA))
                    = ev ψ (RA + LA - (2 : Error) • (LA * RA)) := by
                        rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                        rw [hmul, hLA_proj, hRA_proj, hcomm]
                        simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  _ = ev ψ RA + ev ψ LA - 2 * ev ψ (LA * RA) := by
                        rw [ev_sub]
                        rw [ev_add]
                        have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                          simpa using (ev_scale ψ (2 : Error) (LA * RA))
                        rw [hscale]
          _ =
              (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
                (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
                2 *
                  (∑ a,
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      calc
        ev ψ ((RT - LT)ᴴ * (RT - LT))
          = ev ψ (RT + LT - (2 : Error) • (LT * RT)) := by
              rw [hD_expand]
        _ = ev ψ RT + ev ψ LT - 2 * ev ψ (LT * RT) := by
              rw [ev_sub, ev_add]
              have hscale : ev ψ ((2 : Error) • (LT * RT)) = 2 * ev ψ (LT * RT) := by
                simpa using (ev_scale ψ (2 : Error) (LT * RT))
              rw [hscale]
        _ ≤
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
              rw [hRT_ev, hLT_ev]
              linarith
        _ = qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
              rw [hq_expand]
    have hrewrite :
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
          ev ψ (LB * (RT - LT)) := by
      have hmiddle :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)) =
            ev ψ (LB * RT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))]
        calc
          ev ψ (∑ a,
              leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a))
            = ev ψ
                (LB *
                  ∑ a, rightTensor (ι₁ := ι) ((A q).outcome a)) := by
                    refine congrArg (ev ψ) ?_
                    dsimp [LB]
                    symm
                    exact Finset.mul_sum Finset.univ
                      (fun a : Outcome =>
                        rightTensor (ι₁ := ι) ((A q).outcome a))
                      (leftTensor (ι₂ := ι) B)
          _ = ev ψ (LB * RT) := by
                simp [RT, rightTensor_finset_sum, (A q).sum_eq_total]
      have hright :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
            ev ψ (LB * LT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) (B * (A q).outcome a))]
        calc
          ev ψ (∑ a, leftTensor (ι₂ := ι) (B * (A q).outcome a))
            = ev ψ (∑ a, LB * leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                refine congrArg (ev ψ) ?_
                refine Finset.sum_congr rfl ?_
                intro a _
                dsimp [LB]
                simpa [leftTensor] using
                  (Matrix.mul_kronecker_mul
                    B ((A q).outcome a)
                    (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι))
          _ = ev ψ (LB * ∑ a, leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                rw [Finset.mul_sum]
          _ = ev ψ (LB * LT) := by
                simp [LT, leftTensor_finset_sum, (A q).sum_eq_total]
      calc
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))
          = ev ψ (LB * RT) - ev ψ (LB * LT) := by rw [hmiddle, hright]
        _ = ev ψ (LB * (RT - LT)) := by
              rw [(ev_sub ψ (LB * RT) (LB * LT)).symm]
              simp [mul_sub]
    have hsqrt_LB' : Real.sqrt (ev ψ (LB * LBᴴ)) ≤ 1 := by
      simpa [hLB_herm] using hsqrt_LB
    calc
      |(∑ a, ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) ((A q).outcome a))) -
        ∑ a, ev ψ
          (leftTensor (ι₂ := ι) (B * (A q).outcome a))|
        = |ev ψ (LB * (RT - LT))| := by rw [hrewrite]
      _ ≤
          Real.sqrt (ev ψ (LB * LBᴴ)) *
            Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
              simpa using ev_abs_mul_le_sqrt ψ LB (RT - LT)
      _ ≤ 1 * Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_LB' (Real.sqrt_nonneg _)
      _ = Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by ring
      _ ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
            exact Real.sqrt_le_sqrt htotal_sq_le
  calc
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      = |avgOver 𝒟 (fun q =>
          (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)))| := by
            simp [middleSandwichExpectation, rightSandwichExpectation, avgOver,
              Finset.sum_sub_distrib, mul_sub]
    _ ≤
        Real.sqrt
          (avgOver 𝒟
            (fun q =>
              qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
          exact
            avgOver_abs_le_sqrt_of_pointwise 𝒟
              (fun q =>
                (∑ a, ev ψ
                  (leftTensor (ι₂ := ι) B *
                    rightTensor (ι₁ := ι) ((A q).outcome a))) -
                ∑ a, ev ψ
                  (leftTensor (ι₂ := ι) (B * (A q).outcome a)))
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              hpointwise
              (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              h𝒟
    _ ≤ Real.sqrt δ := by
          exact Real.sqrt_le_sqrt hδ

/-- `prop:switch-sandwich`.

The paper proof assumes a normalized state and a probability distribution
(weights summing to ≤ 1). These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem switchSandwich {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
  }

private lemma completenessTransfer_core {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    sddError ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  intro hε
  let gap : Question → Error := fun q =>
    subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) - subMeasMass ψ (A q)
  let sdd : Question → Error := fun q =>
    qSDD ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q)
  have hgap_pointwise : ∀ q, gap q ≤ 2 * Real.sqrt (sdd q) := by
    intro q
    let diagA : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)
    let diagP : Error := ∑ a : Outcome, ev ψ ((P q).outcome a * (P q).outcome a)
    let overlap : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (P q).outcome a)
    have hmassP_eq_diagP :
        subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) = diagP := by
      simpa [subMeasMass, IdxProjSubMeas.toIdxSubMeas, diagP] using
        (projSubMeas_diagMass_eq_mass ψ (P q)).symm
    have hdiagA_le_massA :
        diagA ≤ subMeasMass ψ (A q) := by
      simpa [subMeasMass, diagA] using subMeas_diagMass_le_mass ψ (A q)
    have hgap_left_raw :
        |diagA - overlap| ≤ Real.sqrt (sdd q) := by
      simpa [diagA, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_left ψ hψ (A q) ((P q).toSubMeas)
    have hgap_left :
        overlap - diagA ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_left_raw]
    have hgap_right_raw :
        |overlap - diagP| ≤ Real.sqrt (sdd q) := by
      simpa [diagP, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_right ψ hψ (A q) ((P q).toSubMeas)
    have hgap_right :
        diagP - overlap ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_right_raw]
    have hmass_gap :
        gap q ≤ diagP - diagA := by
      have hmassP_eq_diagP' :
          ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) = diagP := by
        simpa [subMeasMass] using hmassP_eq_diagP
      dsimp [gap, subMeasMass]
      calc
        ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - ev ψ (A q).total
          ≤ ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - diagA := by
              exact sub_le_sub_left hdiagA_le_massA _
        _ = diagP - diagA := by rw [hmassP_eq_diagP']
    have hdiag_gap : diagP - diagA ≤ 2 * Real.sqrt (sdd q) := by
      linarith
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
          exact qSDD_nonneg ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q))
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
        2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    rw [hscale_avg]
    calc
      2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q))
        ≤ 2 * Real.sqrt (avgOver 𝒟 sdd) := by
            exact mul_le_mul_of_nonneg_left hsqrt_avg (by positivity)
      _ = 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
            simp [sddError, sdd]
  have hgap_total :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    calc
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        = avgOver 𝒟 gap := by
            unfold idxSubMeasMass subMeasMass avgOver gap
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [mul_sub, subMeasMass]
      _ ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := hgap_avg
      _ ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := hsdd_sqrt
  have hsqrt_ε :
      Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) ≤ Real.sqrt ε := by
    exact Real.sqrt_le_sqrt hε
  have hgap_total' :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt ε := by
    exact le_trans hgap_total <| by
      exact mul_le_mul_of_nonneg_left hsqrt_ε (by positivity)
  linarith

/-- `prop:completeness-transfer-projective-P`.

The paper proof uses a normalized state and a probability distribution.
These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    SDDRel ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact {
    completenessTransfer :=
      completenessTransfer_core ψ 𝒟 hψ h𝒟 A P ε hε
  }

/-- The self-distance defect `qSDD ψ M M` is zero. -/
private lemma qSDD_self
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (M : SubMeas Outcome ι) :
    qSDD ψ M M = 0 := by
  unfold qSDD qSDDCore
  apply Finset.sum_eq_zero
  intro a _
  simp [ev]

/-- The self-distance `sddError ψ 𝒟 A A` is zero. -/
lemma sddError_self {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    sddError ψ 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => qSDD ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => qSDD_self ψ (A q))
  rw [this]
  exact avgOver_zero 𝒟

/-- `sscError` is nonneg since it averages `max 0 (...)` terms. -/
lemma sscError_nonneg {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError
  exact avgOver_nonneg 𝒟 _ fun a => by unfold qSSCDefect; exact le_max_left 0 _


private lemma leftTensor_mono
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A B : MIPStarRE.Quantum.Op ι₁} (hAB : A ≤ B) :
    leftTensor (ι₂ := ι₂) A ≤ leftTensor (ι₂ := ι₂) B := by
  simpa [leftTensor, opTensor] using
    (opTensor_mono_left (ι₂ := ι₂) (B := (1 : MIPStarRE.Quantum.Op ι₂))
      hAB (show (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1 by exact zero_le_one))

private lemma qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : PermInvState ψ)
    (M : SubMeas Outcome ι) :
    qSDD ψ M.liftLeft M.liftRight ≤ 2 * qBipartiteSSCDefect ψ M := by
  have h_expand :
      ∀ a : Outcome,
        ev ψ
            (((leftTensor (ι₂ := ι) (M.outcome a) -
                  rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
              (leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a))) =
          ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
            ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
            2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    intro a
    have hLherm :
        (leftTensor (ι₂ := ι) (M.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (M.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (leftTensor_nonneg (ι₂ := ι) (M.outcome_pos a))).isHermitian.eq
    have hRherm :
        (rightTensor (ι₁ := ι) (M.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (M.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (rightTensor_nonneg (ι₁ := ι) (M.outcome_pos a))).isHermitian.eq
    calc
      ev ψ
          (((leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
            (leftTensor (ι₂ := ι) (M.outcome a) -
              rightTensor (ι₁ := ι) (M.outcome a)))
        =
          ev ψ
            (((leftTensor (ι₂ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a) -
                leftTensor (ι₂ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a)) -
              (rightTensor (ι₁ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a) -
                rightTensor (ι₁ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a)))) := by
            congr 1
            simp [hLherm, hRherm, sub_mul, mul_sub]
            abel
      _ =
          ev ψ
            (leftTensor (ι₂ := ι) (M.outcome a) *
              leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) *
                rightTensor (ι₁ := ι) (M.outcome a)) -
            (ev ψ
                (rightTensor (ι₁ := ι) (M.outcome a) *
                  leftTensor (ι₂ := ι) (M.outcome a)) -
              ev ψ
                (rightTensor (ι₁ := ι) (M.outcome a) *
                  rightTensor (ι₁ := ι) (M.outcome a))) := by
            rw [ev_sub, ev_sub, ev_sub]
      _ =
          ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
            ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
            2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [leftTensor_mul_leftTensor, leftTensor_mul_rightTensor_eq_opTensor,
              rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor]
            ring
  have h_gap_eq :
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a))) =
        ev ψ (leftTensor (ι₂ := ι) M.total) -
          ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a)))
        =
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sub]
      _ =
          ev ψ
            (∑ a : Outcome,
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a))) := by
            rw [← ev_sum ψ
              (fun a =>
                leftTensor (ι₂ := ι) (M.outcome a) -
                  opTensor (M.outcome a) (M.outcome a))]
      _ =
          ev ψ
            ((∑ a : Outcome, leftTensor (ι₂ := ι) (M.outcome a)) -
              ∑ a : Outcome, opTensor (M.outcome a) (M.outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ M.outcome, M.sum_eq_total]
            rw [ev_sub, ev_sum]
  have h_gap_nonneg :
      0 ≤ ev ψ (leftTensor (ι₂ := ι) M.total) -
        ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      0 ≤
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            exact Finset.sum_nonneg fun a _ =>
              ev_nonneg_of_psd ψ _ <|
                sub_nonneg.mpr <|
                  opTensor_le_leftTensor
                    (M.outcome_pos a)
                    (M.outcome_le_one a)
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            calc
              ∑ a : Outcome,
                  ev ψ
                    (leftTensor (ι₂ := ι) (M.outcome a) -
                      opTensor (M.outcome a) (M.outcome a))
                =
                  ∑ a : Outcome,
                    (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
                      ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    rw [ev_sub]
              _ =
                  ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
                    exact h_gap_eq
  have h_pointwise :
      qSDD ψ M.liftLeft M.liftRight ≤
        2 *
          (ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
    unfold qSDD qSDDCore
    calc
      ∑ a : Outcome,
          ev ψ
            (((M.liftLeft.outcome a - M.liftRight.outcome a)ᴴ) *
              (M.liftLeft.outcome a - M.liftRight.outcome a))
        =
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
              ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
              2 * ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            simpa [SubMeas.liftLeft, SubMeas.liftRight] using h_expand a
      _ =
          ∑ a : Outcome,
            (2 *
              (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                ev ψ (opTensor (M.outcome a) (M.outcome a)))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hψ.swap_ev (M.outcome a * M.outcome a)]
            ring
      _ = 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [← Finset.mul_sum]
      _ ≤ 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun a _ => by
                apply sub_le_sub
                · exact ev_mono ψ _ _ <|
                    leftTensor_mono (ι₂ := ι) <|
                      MIPStarRE.Quantum.sq_le_self
                        (M.outcome_pos a)
                        (M.outcome_le_one a)
                · exact le_rfl
            · norm_num
      _ =
          2 *
            (ev ψ (leftTensor (ι₂ := ι) M.total) -
              ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [h_gap_eq]
  unfold qBipartiteSSCDefect
  rw [max_eq_right h_gap_nonneg]
  exact h_pointwise

/-- `prop:two-notions-of-self-consistency`.

If the indexed sub-measurement `A` is bipartite-strongly-self-consistent
on the permutation-invariant state `ψ` (i.e., `BipartiteSSCRel ψ 𝒟 A δ`,
meaning `∑ₐ ev ψ (Aₐ ⊗ I) − ∑ₐ ev ψ (Aₐ ⊗ Aₐ) ≤ δ`), then the left
and right lifts are close: `SDDRel ψ 𝒟 (liftLeft A) (liftRight A) (2 * δ)`.

**Paper proof sketch:**
1. Expand `∑ₐ ev ψ ((Aₐ⊗I − I⊗Aₐ)² )`.
2. Using Kronecker mixed-product rule and PermInvState.swap_ev, this
   equals `2 · (∑ₐ ev ψ (Aₐ²⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ))`.
3. Since `Aₐ² ≤ Aₐ` (sub-measurement bound), we get
   `≤ 2 · (∑ₐ ev ψ (Aₐ⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ)) = 2 · bipartiteSSCDefect`.
4. Average over 𝒟 and apply the BipartiteSSCRel hypothesis. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    (PermInvState ψ ∧ BipartiteSSCRel ψ 𝒟 A δ) →
      SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A) (2 * δ) := by
  intro ⟨hψ, hssc⟩
  rcases hssc with ⟨hssc⟩
  constructor
  unfold sddError
  calc
    avgOver 𝒟
        (fun q =>
          qSDD ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q))
      ≤
        avgOver 𝒟 (fun q => 2 * qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
            qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect ψ hψ (A q)
    _ = 2 * avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
          have hssc' : avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) ≤ δ := by
            simpa [bipartiteSSCError] using hssc
          exact mul_le_mul_of_nonneg_left hssc' (by norm_num)

/-- For a constant `Unit`-indexed family, `consError` reduces to `qConsDefect`. -/
lemma constFamily_cons_unit
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    consError ψ (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) =
      qConsDefect ψ A B := by
  simp [consError, avgOver, uniformDistribution, constSubMeasFamily]

/-- For a constant `Unit`-indexed family, `sddError` reduces to `qSDD`. -/
lemma constFamily_sdd_unit
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    sddError ψ (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) =
      qSDD ψ A B := by
  simp [sddError, avgOver, uniformDistribution, constSubMeasFamily]

/-- For a constant `Unit`-indexed family, `sscError` reduces to `qSSCDefect`. -/
lemma constFamily_ssc_unit
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    sscError ψ (uniformDistribution Unit) (constSubMeasFamily A) =
      qSSCDefect ψ A := by
  simp [sscError, avgOver, uniformDistribution, constSubMeasFamily]

/-- Completing `B` at `a0` changes only the missing mass, so the self-distance is
exactly the squared residual mass. -/
lemma completion_self_distance
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (B : SubMeas Outcome ι) (a0 : Outcome) :
    qSDD ψ B (completeAtOutcome B a0).toSubMeas =
      ev ψ (((1 : MIPStarRE.Quantum.Op ι) - B.total) *
        ((1 : MIPStarRE.Quantum.Op ι) - B.total)) := by
  classical
  let R : MIPStarRE.Quantum.Op ι := 1 - B.total
  have hsum :
      ∑ a : Outcome,
          ev ψ
            ((B.outcome a -
                (completeAtOutcome B a0).toSubMeas.outcome a)ᴴ *
              (B.outcome a -
                (completeAtOutcome B a0).toSubMeas.outcome a)) =
        ev ψ (R * R) := by
    have hBtotal_herm : B.totalᴴ = B.total := by
      exact (Matrix.nonneg_iff_posSemidef.mp B.total_nonneg).isHermitian.eq
    have hsingle :
        ∑ a : Outcome,
          (if a = a0 then ev ψ (R * R) else 0) =
          ev ψ (R * R) := by
      simp
    calc
      ∑ a : Outcome,
          ev ψ
            ((B.outcome a -
                (completeAtOutcome B a0).toSubMeas.outcome a)ᴴ *
              (B.outcome a -
                (completeAtOutcome B a0).toSubMeas.outcome a))
        = ∑ a : Outcome, if a = a0 then ev ψ (R * R) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : a = a0
            · subst ha
              have hRflip :
                  (B.total - 1) * (B.total - 1) =
                    (1 - B.total) * (1 - B.total) := by
                noncomm_ring
              simp [completeAtOutcome, R, hBtotal_herm, hRflip]
            · simp [completeAtOutcome, ha, ev_zero]
      _ = ev ψ (R * R) := hsingle
  simpa [qSDD, qSDDCore, R] using hsum

/-- Bridge lemma: for a permutation-invariant bipartite state, bipartite SSC
on local families implies local SSC on the left-lifted families.

Requires `PermInvState ψ` because the bipartite defect
`∑ ev(A_a ⊗ A_a)` and local defect `∑ ev(A_a² ⊗ I)` are generally
incomparable without symmetry; the permutation-invariance bridge
`ev(M ⊗ I) = ev(I ⊗ M)` makes the two notions equivalent.

The proof expands `qSDD ψ A.liftLeft A.liftRight`, uses
`PermInvState.swap_ev` to identify the left and right square terms, and
then reads off `∑ ev(A_a² ⊗ I) ≥ ∑ ev(A_a ⊗ A_a)` from
`qSDD_nonneg`. -/
private lemma bipartiteSSC_implies_localSSC_liftLeft {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) δ := by
  intro ⟨hssc⟩
  constructor
  unfold sscError bipartiteSSCError at *
  calc
    avgOver 𝒟 (fun q => qSSCDefect ψ ((IdxSubMeas.liftLeft A) q))
      ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          let M := A q
          let diagSq : Error :=
            ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a))
          let overlap : Error :=
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))
          have h_expand :
              ∀ a : Outcome,
                ev ψ
                    (((leftTensor (ι₂ := ι) (M.outcome a) -
                          rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
                      (leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a))) =
                  ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                    2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            intro a
            have hLherm :
                (leftTensor (ι₂ := ι) (M.outcome a))ᴴ =
                  leftTensor (ι₂ := ι) (M.outcome a) := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (leftTensor_nonneg (ι₂ := ι) (M.outcome_pos a))).isHermitian.eq
            have hRherm :
                (rightTensor (ι₁ := ι) (M.outcome a))ᴴ =
                  rightTensor (ι₁ := ι) (M.outcome a) := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (rightTensor_nonneg (ι₁ := ι) (M.outcome_pos a))).isHermitian.eq
            calc
              ev ψ
                  (((leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (M.outcome a) -
                      rightTensor (ι₁ := ι) (M.outcome a)))
                =
                  ev ψ
                    (((leftTensor (ι₂ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a) -
                        leftTensor (ι₂ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a)) -
                      (rightTensor (ι₁ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a)))) := by
                    congr 1
                    simp [hLherm, hRherm, sub_mul, mul_sub]
                    abel
              _ =
                  ev ψ
                    (leftTensor (ι₂ := ι) (M.outcome a) *
                      leftTensor (ι₂ := ι) (M.outcome a)) -
                    ev ψ
                      (leftTensor (ι₂ := ι) (M.outcome a) *
                        rightTensor (ι₁ := ι) (M.outcome a)) -
                    (ev ψ
                        (rightTensor (ι₁ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a)) -
                      ev ψ
                        (rightTensor (ι₁ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a))) := by
                    rw [ev_sub, ev_sub, ev_sub]
              _ =
                  ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                    2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
                    rw [leftTensor_mul_leftTensor,
                      leftTensor_mul_rightTensor_eq_opTensor,
                      rightTensor_mul_leftTensor_eq_opTensor,
                      rightTensor_mul_rightTensor]
                    ring
          have hdiag_ge_overlap : overlap ≤ diagSq := by
            have hnonneg := qSDD_nonneg ψ M.liftLeft M.liftRight
            have hq :
                qSDD ψ M.liftLeft M.liftRight = 2 * (diagSq - overlap) := by
              unfold qSDD qSDDCore diagSq overlap
              calc
                ∑ a : Outcome,
                    ev ψ
                      (((M.liftLeft.outcome a - M.liftRight.outcome a)ᴴ) *
                        (M.liftLeft.outcome a - M.liftRight.outcome a))
                  =
                    ∑ a : Outcome,
                      (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                        ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                        2 * ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      simpa [SubMeas.liftLeft, SubMeas.liftRight] using h_expand a
                _ =
                    ∑ a : Outcome,
                      (2 *
                        (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                          ev ψ (opTensor (M.outcome a) (M.outcome a)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [hperm.swap_ev (M.outcome a * M.outcome a)]
                      ring
                _ = 2 *
                    ∑ a : Outcome,
                      (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                        ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                      rw [← Finset.mul_sum]
                _ = 2 * (diagSq - overlap) := by
                      rw [show
                        (∑ a : Outcome,
                            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                              ev ψ (opTensor (M.outcome a) (M.outcome a)))) =
                          diagSq - overlap by
                            simp [diagSq, overlap, Finset.sum_sub_distrib]]
            rw [hq] at hnonneg
            nlinarith
          unfold qSSCDefect qBipartiteSSCDefect
          apply max_le_max le_rfl
          have :
              ev ψ (leftTensor (ι₂ := ι) M.total) - diagSq ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) - overlap := by
            linarith
          simpa [M, IdxSubMeas.liftLeft, SubMeas.liftLeft, diagSq,
            leftTensor_mul_leftTensor] using this
    _ ≤ δ := hssc

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
  have hgapA_raw :
      |diagA - overlap| ≤ Real.sqrt (qSDD ψ A.toSubMeas B) := by
    simpa [diagA, overlap] using
      question_overlap_gap_left ψ hψ A.toSubMeas B
  have hgapA :
      diagA - overlap ≤ Real.sqrt δ := by
    have hsqrt :
        Real.sqrt (qSDD ψ A.toSubMeas B) ≤ Real.sqrt δ := by
      exact Real.sqrt_le_sqrt hδ'
    have : diagA - overlap ≤ Real.sqrt (qSDD ψ A.toSubMeas B) := by
      exact (abs_le.mp hgapA_raw).2
    exact le_trans this hsqrt
  have hgapB_raw :
      |overlap - diagB| ≤ Real.sqrt (qSDD ψ A.toSubMeas B) := by
    simpa [diagB, overlap] using
      question_overlap_gap_right ψ hψ A.toSubMeas B
  have hgapB :
      overlap - diagB ≤ Real.sqrt δ := by
    have hsqrt :
        Real.sqrt (qSDD ψ A.toSubMeas B) ≤ Real.sqrt δ := by
      exact Real.sqrt_le_sqrt hδ'
    have : overlap - diagB ≤ Real.sqrt (qSDD ψ A.toSubMeas B) := by
      exact (abs_le.mp hgapB_raw).2
    exact le_trans this hsqrt
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
        ext i j
        rcases i with ⟨i₁, i₂⟩
        rcases j with ⟨j₁, j₂⟩
        simp [SubMeas.liftLeft, leftTensor, A.total_eq_one] }
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

end MIPStarRE.LDT.Preliminaries
