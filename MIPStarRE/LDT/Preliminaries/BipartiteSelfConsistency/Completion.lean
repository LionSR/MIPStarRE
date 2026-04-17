import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Core

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

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

end MIPStarRE.LDT.Preliminaries
