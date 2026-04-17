import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain

/-!
# Preliminary comparison theorems: bipartite self-consistency

Lemmas relating bipartite self-consistency to local self-consistency notions.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

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

/-- Evaluating a completed polynomial submeasurement at a point is the same as
completing the evaluated submeasurement at the induced outcome. -/
lemma evaluateAt_completeAtOutcome
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    [FieldModel params.q]
    (H : SubMeas (Polynomial params) ι)
    (h0 : Polynomial params)
    (u : Point params) :
    evaluateAt params u (completeAtOutcome H h0).toSubMeas =
      (completeAtOutcome (evaluateAt params u H) (h0 u)).toSubMeas := by
  classical
  let R : MIPStarRE.Quantum.Op ι := 1 - H.total
  let L := evaluateAt params u (completeAtOutcome H h0).toSubMeas
  let Rhs := (completeAtOutcome (evaluateAt params u H) (h0 u)).toSubMeas
  have houtcome : L.outcome = Rhs.outcome := by
    funext b
    let S : Finset (Polynomial params) :=
      Finset.univ.filter fun h : Polynomial params => h u = b
    have hsplit :
        (∑ h ∈ S,
            if hh : h = h0 then H.outcome h + R else H.outcome h) =
          (∑ h ∈ S, H.outcome h) +
            ∑ h ∈ S, if h = h0 then R else 0 := by
      calc
        (∑ h ∈ S, if hh : h = h0 then H.outcome h + R else H.outcome h)
          = ∑ h ∈ S, (H.outcome h + if h = h0 then R else 0) := by
              refine Finset.sum_congr rfl ?_
              intro h hh
              by_cases hEq : h = h0 <;> simp [hEq]
        _ = (∑ h ∈ S, H.outcome h) + ∑ h ∈ S, if h = h0 then R else 0 := by
              rw [Finset.sum_add_distrib]
    have hresidual :
        (∑ h ∈ S, if h = h0 then R else 0) =
          if b = h0 u then R else 0 := by
      rw [Finset.sum_ite_eq' S h0 (fun _ => R)]
      by_cases hb : b = h0 u <;> simp [S, hb, eq_comm]
    have hLout :
        (evaluateAt params u (completeAtOutcome H h0).toSubMeas).outcome b =
          ∑ h ∈ Finset.univ.filter (fun g : Polynomial params => g u = b),
            (completeAtOutcome H h0).toSubMeas.outcome h := by
      ext i j
      simp [evaluateAt, postprocess]
      convert rfl
    have hEval :
        (evaluateAt params u H).outcome b =
          ∑ h ∈ Finset.univ.filter (fun g : Polynomial params => g u = b), H.outcome h := by
      ext i j
      simp [evaluateAt, postprocess]
      convert rfl
    calc
      L.outcome b = ∑ h ∈ S, if hh : h = h0 then H.outcome h + R else H.outcome h := by
              simpa [L, S, completeAtOutcome, R] using hLout
      _ = (∑ h ∈ S, H.outcome h) + ∑ h ∈ S, if h = h0 then R else 0 := hsplit
      _ = (evaluateAt params u H).outcome b + if b = h0 u then R else 0 := by
            rw [hEval]
            exact congrArg (fun X => (∑ h ∈ S, H.outcome h) + X) hresidual
      _ = Rhs.outcome b := by
            by_cases hb : b = h0 u
            · simp [Rhs, completeAtOutcome, hb, R, evaluateAt, postprocess_total]
            · simp [Rhs, completeAtOutcome, hb, R, evaluateAt, postprocess_total]
  have htotal : L.total = Rhs.total := by
    simp [L, Rhs, evaluateAt, completeAtOutcome, postprocess]
  exact SubMeas.ext (A := L) (B := Rhs) (fun a => congrFun houtcome a) htotal

/-- Completing the right submeasurement can increase the bipartite consistency
defect by at most the residual completion mass `1 - B.total`. -/
lemma qBipartiteConsDefect_completeAtOutcome_right_le
    {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA)
    (B : SubMeas Outcome ιB)
    (a0 : Outcome) :
    qBipartiteConsDefect ψ A.toSubMeas (completeAtOutcome B a0).toSubMeas ≤
      qBipartiteConsDefect ψ A.toSubMeas B +
        ev ψ (rightTensor (ι₁ := ιA) (1 - B.total)) := by
  classical
  let R : MIPStarRE.Quantum.Op ιB := 1 - B.total
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact sub_nonneg.mpr B.total_le_one
  have hmatchExtra_nonneg : 0 ≤ ev ψ (opTensor (A.outcome a0) R) := by
    exact ev_nonneg_of_psd ψ _ <|
      (Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp (A.toSubMeas.outcome_pos a0))
        (Matrix.nonneg_iff_posSemidef.mp hR_nonneg)).nonneg
  have hmatch :
      qBipartiteMatchMass ψ A.toSubMeas (completeAtOutcome B a0).toSubMeas =
        qBipartiteMatchMass ψ A.toSubMeas B + ev ψ (opTensor (A.outcome a0) R) := by
    unfold qBipartiteMatchMass
    calc
      ∑ a : Outcome,
          ev ψ
            (opTensor (A.toSubMeas.outcome a) ((completeAtOutcome B a0).toSubMeas.outcome a))
        = ∑ a : Outcome,
            ev ψ (opTensor (A.outcome a) (B.outcome a + if a = a0 then R else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              by_cases ha : a = a0 <;> simp [completeAtOutcome, ha, R]
      _ = ∑ a : Outcome,
            (ev ψ (opTensor (A.outcome a) (B.outcome a)) +
              ev ψ (opTensor (A.outcome a) (if a = a0 then R else 0))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              by_cases ha : a = a0
              · simp [ha, opTensor, ev_add, Matrix.kronecker_add]
              · simpa [ha, opTensor] using (ev_zero ψ)
      _ = qBipartiteMatchMass ψ A.toSubMeas B +
            ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (if a = a0 then R else 0)) := by
              simp [qBipartiteMatchMass, Finset.sum_add_distrib]
      _ = qBipartiteMatchMass ψ A.toSubMeas B + ev ψ (opTensor (A.outcome a0) R) := by
              rw [Finset.sum_eq_single a0]
              · simp [R]
              · intro a _ ha
                simpa [ha, opTensor] using (ev_zero ψ)
              · intro hnot
                exact (hnot (Finset.mem_univ a0)).elim
  have htotal :
      ev ψ (opTensor A.toSubMeas.total ((completeAtOutcome B a0).toSubMeas.total)) =
        ev ψ (opTensor A.toSubMeas.total B.total) + ev ψ (rightTensor (ι₁ := ιA) R) := by
    calc
      ev ψ (opTensor A.toSubMeas.total ((completeAtOutcome B a0).toSubMeas.total))
        = ev ψ (opTensor (1 : MIPStarRE.Quantum.Op ιA) (B.total + R)) := by
            simp [completeAtOutcome, A.total_eq_one, R]
      _ = ev ψ
            (opTensor (1 : MIPStarRE.Quantum.Op ιA) B.total +
              opTensor (1 : MIPStarRE.Quantum.Op ιA) R) := by
              congr 1
              simp [opTensor, Matrix.kronecker_add]
      _ = ev ψ (opTensor (1 : MIPStarRE.Quantum.Op ιA) B.total) +
            ev ψ (opTensor (1 : MIPStarRE.Quantum.Op ιA) R) := by
              rw [ev_add]
      _ = ev ψ (opTensor A.toSubMeas.total B.total) +
            ev ψ (opTensor (1 : MIPStarRE.Quantum.Op ιA) R) := by
              simp [A.total_eq_one]
      _ = ev ψ (opTensor A.toSubMeas.total B.total) + ev ψ (rightTensor (ι₁ := ιA) R) := by
            rfl
  have hinnerB_le :
      ev ψ (opTensor A.toSubMeas.total B.total) - qBipartiteMatchMass ψ A.toSubMeas B ≤
        qBipartiteConsDefect ψ A.toSubMeas B := by
    exact le_max_right 0 _
  have hinnerC_le :
      ev ψ (opTensor A.toSubMeas.total ((completeAtOutcome B a0).toSubMeas.total)) -
          qBipartiteMatchMass ψ A.toSubMeas (completeAtOutcome B a0).toSubMeas ≤
        qBipartiteConsDefect ψ A.toSubMeas B + ev ψ (rightTensor (ι₁ := ιA) R) := by
    rw [htotal, hmatch]
    linarith
  have hrhs_nonneg :
      0 ≤ qBipartiteConsDefect ψ A.toSubMeas B + ev ψ (rightTensor (ι₁ := ιA) R) := by
    have hright_nonneg : 0 ≤ ev ψ (rightTensor (ι₁ := ιA) R) :=
      ev_nonneg_of_psd ψ _ <|
        (Matrix.nonneg_iff_posSemidef.mp (rightTensor_nonneg (ι₁ := ιA) hR_nonneg)).nonneg
    exact add_nonneg (qBipartiteConsDefect_nonneg ψ A.toSubMeas B) hright_nonneg
  unfold qBipartiteConsDefect
  exact max_le_iff.mpr ⟨hrhs_nonneg, hinnerC_le⟩

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
lemma bipartiteSSC_implies_localSSC_liftLeft {Question Outcome : Type*}
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


end MIPStarRE.LDT.Preliminaries
