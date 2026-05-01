import MIPStarRE.LDT.Preliminaries.Defs

/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations extracted from
`MIPStarRE.LDT.Preliminaries.Theorems`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.ConsRel

/-- Monotonicity of `ConsRel` in the allowed error parameter. -/
lemma mono {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {𝒟 : Distribution Question}
    {A : IdxSubMeas Question Outcome ιA}
    {B : IdxSubMeas Question Outcome ιB}
    {δ δ' : Error} (hδ : δ ≤ δ') :
    _root_.MIPStarRE.LDT.ConsRel ψ 𝒟 A B δ →
      _root_.MIPStarRE.LDT.ConsRel ψ 𝒟 A B δ' := by
  intro h
  exact ⟨le_trans h.offDiagonalBound hδ⟩

end MIPStarRE.LDT.ConsRel

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:post-processing-preserves`.

Postprocessing preserves the total operator, so it preserves both the
submeasurement and measurement conditions. -/
theorem postprocessPreservesMeasurements {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (f : α → β) :
    (postprocess A f).total = A.total := by
  exact postprocess_total A f

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
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
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      BipartiteSDDRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
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
                simpa [SubMeas.liftLeft, (A q).total_eq_one] using
                  (leftTensor_one (ι₁ := ι) (ι₂ := ι)) }
          let B' : Measurement Outcome (ι × ι) :=
            { toSubMeas := ((B q).toSubMeas).liftRight
              total_eq_one := by
                simpa [SubMeas.liftRight, (B q).total_eq_one] using
                  (rightTensor_one (ι₁ := ι) (ι₂ := ι)) }
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

lemma ev_leftTensor_mul_rightTensor_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    {X Y : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ ev ψ (leftTensor (ι₂ := ι) X * rightTensor (ι₁ := ι) Y) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  quantum_nonneg

lemma qMatchMass_leftRight_postprocess_ge {α β : Type*}
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

/-- Postprocessing can only decrease the bipartite strong self-consistency
defect: the total mass is preserved while the diagonal overlap term can only
increase. -/
lemma qBipartiteSSCDefect_postprocess_le {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (M : SubMeas α ι) (f : α → β) :
    qBipartiteSSCDefect ψ (postprocess M f) ≤ qBipartiteSSCDefect ψ M := by
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
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) δ →
      ConsRel ψ 𝒟
        (fun q => postprocess ((A q).toSubMeas) f)
        (fun q => postprocess ((B q).toSubMeas) f) δ := by
  intro ⟨hcons⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed] at hcons ⊢
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

/-- Question-dependent postprocessing preserves bipartite consistency. -/
theorem consRelDataProcessing_questionDependent {Question α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α ι) (δ : Error) (f : Question → α → β) :
    ConsRel ψ 𝒟 A B δ →
      ConsRel ψ 𝒟
        (fun q => postprocess (A q) (f q))
        (fun q => postprocess (B q) (f q)) δ := by
  intro ⟨hcons⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed] at hcons ⊢
  unfold consError at *
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ
            (leftPlacedSubMeas (ιB := ι) (postprocess (A q) (f q)))
            (rightPlacedSubMeas (ιA := ι) (postprocess (B q) (f q))))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              (leftPlacedSubMeas (ιB := ι) (A q))
              (rightPlacedSubMeas (ιA := ι) (B q))) := by
          apply avgOver_mono
          intro q
          exact qConsDefect_leftRight_postprocess_le ψ (A q) (B q) (f q)
    _ ≤ δ := hcons

/-- If a uniformly sampled consistency statement depends only on the first
coordinate of a product question, it lifts to the full product with the same
error. -/
lemma consRel_uniform_prod_fst
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : IdxSubMeas α Outcome ιA)
    (B : IdxSubMeas α Outcome ιB)
    (δ : Error)
    (hAB : ConsRel ψ (uniformDistribution α) A B δ) :
    ConsRel ψ (uniformDistribution (α × β))
      (fun ab => A ab.1)
      (fun ab => B ab.1)
      δ := by
  rcases hAB with ⟨hAB⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver (uniformDistribution (α × β))
        (fun ab => qBipartiteConsDefect ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α)
          (fun a => qBipartiteConsDefect ψ (A a) (B a)) := by
            exact avgOver_uniform_fst (α := α) (β := β)
              (fun a => qBipartiteConsDefect ψ (A a) (B a))
    _ ≤ δ := hAB

/-- Reindexing a uniformly sampled consistency statement along an equivalence. -/
lemma consRel_uniform_equiv
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (e : α ≃ β)
    (ψ : QuantumState (ιA × ιB))
    (A : IdxSubMeas α Outcome ιA)
    (B : IdxSubMeas α Outcome ιB)
    (δ : Error) :
    ConsRel ψ (uniformDistribution α) A B δ ↔
      ConsRel ψ (uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  have hEq :
      bipartiteConsError ψ (uniformDistribution α) A B =
        bipartiteConsError ψ (uniformDistribution β)
          (fun b => A (e.symm b))
          (fun b => B (e.symm b)) := by
    let f : α → Error := fun a => qBipartiteConsDefect ψ (A a) (B a)
    unfold bipartiteConsError
    calc
      avgOver (uniformDistribution α) (fun a => qBipartiteConsDefect ψ (A a) (B a))
        = (1 / (Fintype.card α : Error)) *
            ∑ a : α, qBipartiteConsDefect ψ (A a) (B a) := by
              simp [avgOver, uniformDistribution, Finset.mul_sum]
      _ = (1 / (Fintype.card β : Error)) *
            ∑ a : α, qBipartiteConsDefect ψ (A a) (B a) := by
              rw [Fintype.card_congr e]
      _ = (1 / (Fintype.card β : Error)) *
            ∑ b : β, qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b)) := by
              congr 1
              exact (Fintype.sum_equiv e
                (fun a => qBipartiteConsDefect ψ (A a) (B a))
                (fun b => qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b)))
                (by intro a; simp))
      _ = avgOver (uniformDistribution β)
            (fun b => qBipartiteConsDefect ψ (A (e.symm b)) (B (e.symm b))) := by
              simp [avgOver, uniformDistribution, Finset.mul_sum]
  constructor <;> rintro ⟨h⟩ <;> constructor <;> simpa [hEq] using h


end MIPStarRE.LDT.Preliminaries
