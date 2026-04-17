import MIPStarRE.LDT.Pasting.BridgeLemmas

/-!
# Section 12 pasting: Bernoulli recurrence weights

Bernoulli recurrence weights and the final pasting wrappers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

private lemma gHatTypeWeight_le {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight τ ≤ k := by
  unfold gHatTypeWeight
  simpa using (Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => τ i))

private lemma finCons_eq_prependTypeBit {k : ℕ} (b : Bool) (τ : GHatType k) :
    ((Fin.cons b τ : GHatType (k + 1))) = prependTypeBit b τ := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rfl

private lemma gHatTypeWeight_prepend_true {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit true τ) = gHatTypeWeight τ + 1 := by
  rw [← finCons_eq_prependTypeBit true τ]
  unfold gHatTypeWeight
  simpa [Fin.cons_zero, Fin.cons_succ, add_comm] using
    (Fin.card_filter_univ_succ
      (n := k) (p := fun i : Fin (k + 1) => (Fin.cons true τ : GHatType (k + 1)) i = true))

private lemma gHatTypeWeight_prepend_false {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit false τ) = gHatTypeWeight τ := by
  rw [← finCons_eq_prependTypeBit false τ]
  unfold gHatTypeWeight
  simpa [Fin.cons_zero, Fin.cons_succ] using
    (Fin.card_filter_univ_succ
      (n := k) (p := fun i : Fin (k + 1) => (Fin.cons false τ : GHatType (k + 1)) i = true))

private lemma gHatTypeWeight_fin_cons_true {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (Fin.cons true τ : GHatType (k + 1)) = gHatTypeWeight τ + 1 := by
  simpa [finCons_eq_prependTypeBit] using gHatTypeWeight_prepend_true τ

private lemma gHatTypeWeight_fin_cons_false {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (Fin.cons false τ : GHatType (k + 1)) = gHatTypeWeight τ := by
  simpa [finCons_eq_prependTypeBit] using gHatTypeWeight_prepend_false τ

private lemma gHatTypeOperator_nonneg
    (G : MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    {k : ℕ} (τ : GHatType k) :
    0 ≤ gHatTypeOperator G τ := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hGpow : 0 ≤ G ^ gHatTypeWeight τ := by
    exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hGpsd) _).nonneg
  have hIGpow : 0 ≤ (1 - G) ^ (k - gHatTypeWeight τ) := by
    exact
      (Matrix.PosSemidef.pow
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGleOne)) _).nonneg
  have hcommPow : Commute (G ^ gHatTypeWeight τ) ((1 - G) ^ (k - gHatTypeWeight τ)) :=
    (hcomm.pow_left _).pow_right _
  exact Commute.mul_nonneg hGpow hIGpow hcommPow

private lemma gHatTypeOperator_prepend_true
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit true τ) = gHatTypeOperator G τ * G := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hsub : k + 1 - (gHatTypeWeight τ + 1) = k - gHatTypeWeight τ := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_true, hsub, pow_succ]
  calc
    (G ^ gHatTypeWeight τ * G) * (1 - G) ^ (k - gHatTypeWeight τ)
      = G ^ gHatTypeWeight τ * (G * (1 - G) ^ (k - gHatTypeWeight τ)) := by
          simp [mul_assoc]
    _ = G ^ gHatTypeWeight τ * ((1 - G) ^ (k - gHatTypeWeight τ) * G) := by
          rw [(hcomm.pow_right _).eq]
    _ = (G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)) * G := by
          simp [mul_assoc]

private lemma gHatTypeOperator_prepend_false
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit false τ) = gHatTypeOperator G τ * (1 - G) := by
  have hsub : k + 1 - gHatTypeWeight τ = k - gHatTypeWeight τ + 1 := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_false, hsub, pow_succ]
  simp [mul_assoc]

private lemma gHatTypeOperator_fin_cons_true
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (Fin.cons true τ : GHatType (k + 1)) = gHatTypeOperator G τ * G := by
  simpa [finCons_eq_prependTypeBit] using gHatTypeOperator_prepend_true G τ

private lemma gHatTypeOperator_fin_cons_false
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (Fin.cons false τ : GHatType (k + 1)) =
      gHatTypeOperator G τ * (1 - G) := by
  simpa [finCons_eq_prependTypeBit] using gHatTypeOperator_prepend_false G τ

/-- The full sum of type operators equals the identity.

This is the commuting binomial expansion
`∑ τ : GHatType k, G ^ |τ| * (1 - G) ^ (k - |τ|) = (G + (1 - G))^k = 1`. -/
private lemma full_gHatType_sum_eq_one
    (G : MIPStarRE.Quantum.Op ι) :
    ∀ prefixLen : ℕ, ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix = 1
  | 0 => by
      simp [gHatTypeOperator, gHatTypeWeight]
  | prefixLen + 1 => by
      have hsplit :
          (∑ τprefix : GHatType (prefixLen + 1),
              gHatTypeOperator G τprefix) =
            ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := by
        exact (Fintype.sum_equiv
          ((Fin.consEquiv (fun _ : Fin (prefixLen + 1) => Bool)).symm)
          (fun τprefix => gHatTypeOperator G τprefix)
          (fun p => gHatTypeOperator G (Fin.cons p.1 p.2))
          (by
            intro τprefix
            simp))
      have hprod :
          (∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2)) =
            ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := by
        simpa using
          (Fintype.sum_prod_type'
            (f := fun b τprefix => gHatTypeOperator G (Fin.cons b τprefix)))
      calc
        ∑ τprefix : GHatType (prefixLen + 1), gHatTypeOperator G τprefix
          = ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := hsplit
        _ = ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := hprod
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (Fin.cons true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons false τprefix) := by
                rw [Fintype.sum_bool]
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (prependTypeBit true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (prependTypeBit false τprefix) := by
                simp [finCons_eq_prependTypeBit]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix * G) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix * (1 - G) := by
                simp_rw [gHatTypeOperator_prepend_true, gHatTypeOperator_prepend_false]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix) * G +
              (∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix) * (1 - G) := by
                rw [Finset.sum_mul, Finset.sum_mul]
        _ = 1 * G + 1 * (1 - G) := by
              simpa [full_gHatType_sum_eq_one G prefixLen]
        _ = 1 := by
              have hcancel : G + (1 - G) = (1 : MIPStarRE.Quantum.Op ι) := by
                abel
              simpa [one_mul] using hcancel

/-- `lem:truncated-type-sum-recurrence`.

This packages the Hermitian, positivity, boundedness, and one-step recurrence
properties of the truncated type sums used in the `fromHToG` reduction. -/
theorem truncatedTypeSumRecurrence
    (G : MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums G d prefixLen τtail)ᴴ = truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ truncatedTypeSums G d prefixLen τtail ∧
      truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums G d (prefixLen + 1) τtail =
        truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G +
          truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
  /-
  Paper reference: `references/ldt-paper/ld-pasting.tex`,
  `lem:truncated-type-sum-recurrence`.
  The proof is the commuting-polynomial argument in `G` and `I - G`.
  -/
  have hnonneg :
      0 ≤ truncatedTypeSums G d prefixLen τtail := by
    unfold truncatedTypeSums
    refine Finset.sum_nonneg ?_
    intro τprefix _
    split_ifs with hcond
    · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
    · simp
  have hle_one :
      truncatedTypeSums G d prefixLen τtail ≤ 1 := by
    calc
      truncatedTypeSums G d prefixLen τtail
        ≤ ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix := by
            unfold truncatedTypeSums
            refine Finset.sum_le_sum ?_
            intro τprefix _
            split_ifs with hcond
            · exact le_rfl
            · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
      _ = 1 := full_gHatType_sum_eq_one G prefixLen
  have hherm :
      (truncatedTypeSums G d prefixLen τtail)ᴴ = truncatedTypeSums G d prefixLen τtail := by
    exact (Matrix.nonneg_iff_posSemidef.mp hnonneg).isHermitian.eq
  have hsplit :
      truncatedTypeSums G d (prefixLen + 1) τtail =
        ∑ p : Bool × GHatType prefixLen,
          if d + 1 ≤ gHatTypeWeight (Fin.cons p.1 p.2) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : MIPStarRE.Quantum.Op ι) := by
    unfold truncatedTypeSums
    exact (Fintype.sum_equiv
      ((Fin.consEquiv (fun _ : Fin (prefixLen + 1) => Bool)).symm)
      (fun τprefix =>
        if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail then
          gHatTypeOperator G τprefix
        else (0 : MIPStarRE.Quantum.Op ι))
      (fun p =>
        if d + 1 ≤ gHatTypeWeight (Fin.cons p.1 p.2) + gHatTypeWeight τtail then
          gHatTypeOperator G (Fin.cons p.1 p.2)
        else (0 : MIPStarRE.Quantum.Op ι))
      (by
        intro τprefix
        simp))
  have hprod :
      (∑ p : Bool × GHatType prefixLen,
          if d + 1 ≤ gHatTypeWeight (Fin.cons p.1 p.2) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : MIPStarRE.Quantum.Op ι)) =
        ∑ b : Bool,
          ∑ τprefix : GHatType prefixLen,
            if d + 1 ≤ gHatTypeWeight (Fin.cons b τprefix) + gHatTypeWeight τtail then
              gHatTypeOperator G (Fin.cons b τprefix)
            else (0 : MIPStarRE.Quantum.Op ι) := by
    simpa using
      (Fintype.sum_prod_type' (f := fun b τprefix =>
        if d + 1 ≤ gHatTypeWeight (Fin.cons b τprefix) + gHatTypeWeight τtail then
          gHatTypeOperator G (Fin.cons b τprefix)
        else (0 : MIPStarRE.Quantum.Op ι)))
  have htrue :
      (∑ τprefix : GHatType prefixLen,
          (if d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons true τprefix)
          else (0 : MIPStarRE.Quantum.Op ι))) =
        truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G := by
    calc
      (∑ τprefix : GHatType prefixLen,
          (if d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons true τprefix)
          else (0 : MIPStarRE.Quantum.Op ι)))
        =
          ∑ τprefix : GHatType prefixLen,
            ((if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight (prependTypeBit true τtail) then
              gHatTypeOperator G τprefix
            else (0 : MIPStarRE.Quantum.Op ι)) * G) := by
              refine Finset.sum_congr rfl ?_
              intro τprefix _
              have hcond :
                  (d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) + gHatTypeWeight τtail) ↔
                    (d + 1 ≤ gHatTypeWeight τprefix +
                      gHatTypeWeight (prependTypeBit true τtail)) := by
                rw [gHatTypeWeight_fin_cons_true, gHatTypeWeight_prepend_true]
                omega
              by_cases h : d + 1 ≤ gHatTypeWeight τprefix +
                  gHatTypeWeight (prependTypeBit true τtail)
              · have h' :
                    d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) +
                      gHatTypeWeight τtail :=
                  hcond.mpr h
                simpa [h, h'] using gHatTypeOperator_fin_cons_true G τprefix
              · have h' :
                    ¬ d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) +
                      gHatTypeWeight τtail := by
                  exact fun h' => h (hcond.mp h')
                simp [h, h']
      _ = truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G := by
            unfold truncatedTypeSums
            rw [Finset.sum_mul]
  have hfalse :
      (∑ τprefix : GHatType prefixLen,
          (if d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons false τprefix)
          else (0 : MIPStarRE.Quantum.Op ι))) =
        truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
    calc
      (∑ τprefix : GHatType prefixLen,
          (if d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons false τprefix)
          else (0 : MIPStarRE.Quantum.Op ι)))
        =
          ∑ τprefix : GHatType prefixLen,
            ((if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight (prependTypeBit false τtail) then
              gHatTypeOperator G τprefix
            else (0 : MIPStarRE.Quantum.Op ι)) * (1 - G)) := by
              refine Finset.sum_congr rfl ?_
              intro τprefix _
              have hcond :
                  (d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) + gHatTypeWeight τtail) ↔
                    (d + 1 ≤ gHatTypeWeight τprefix +
                      gHatTypeWeight (prependTypeBit false τtail)) := by
                simpa [gHatTypeWeight_fin_cons_false, gHatTypeWeight_prepend_false]
              by_cases h : d + 1 ≤ gHatTypeWeight τprefix +
                  gHatTypeWeight (prependTypeBit false τtail)
              · have h' :
                    d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) +
                      gHatTypeWeight τtail :=
                  hcond.mpr h
                simpa [h, h'] using gHatTypeOperator_fin_cons_false G τprefix
              · have h' :
                    ¬ d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) +
                      gHatTypeWeight τtail := by
                  exact fun h' => h (hcond.mp h')
                simp [h, h']
      _ = truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
            unfold truncatedTypeSums
            rw [Finset.sum_mul]
  refine ⟨hherm, hnonneg, hle_one, ?_⟩
  calc
    truncatedTypeSums G d (prefixLen + 1) τtail
      = ∑ p : Bool × GHatType prefixLen,
          if d + 1 ≤ gHatTypeWeight (Fin.cons p.1 p.2) + gHatTypeWeight τtail then
            gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : MIPStarRE.Quantum.Op ι) := hsplit
    _ = ∑ b : Bool,
          ∑ τprefix : GHatType prefixLen,
            if d + 1 ≤ gHatTypeWeight (Fin.cons b τprefix) + gHatTypeWeight τtail then
              gHatTypeOperator G (Fin.cons b τprefix)
            else (0 : MIPStarRE.Quantum.Op ι) := hprod
    _ = (∑ τprefix : GHatType prefixLen,
            (if d + 1 ≤ gHatTypeWeight (Fin.cons true τprefix) + gHatTypeWeight τtail then
              gHatTypeOperator G (Fin.cons true τprefix)
            else (0 : MIPStarRE.Quantum.Op ι))) +
          (∑ τprefix : GHatType prefixLen,
            (if d + 1 ≤ gHatTypeWeight (Fin.cons false τprefix) + gHatTypeWeight τtail then
              gHatTypeOperator G (Fin.cons false τprefix)
            else (0 : MIPStarRE.Quantum.Op ι))) := by
              rw [Fintype.sum_bool]
    _ = truncatedTypeSums G d prefixLen (prependTypeBit true τtail) * G +
          truncatedTypeSums G d prefixLen (prependTypeBit false τtail) * (1 - G) := by
            rw [htrue, hfalse]

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
private lemma fromHToGRecurrenceWeight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail)ᴴ =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1

/-- One-step recurrence for `fromHToGRecurrenceWeight`: adding a new prefix bit
splits the weight into the `τ_ℓ = 1` and `τ_ℓ = 0` branches, each multiplied by
the appropriate Bernoulli factor `G` or `I - G`. -/
theorem fromHToGRecurrenceWeight_succ
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family (prefixLen + 1) τtail =
      fromHToGRecurrenceWeight params family prefixLen (prependTypeBit true τtail) *
          family.averagedSubMeas.total +
        fromHToGRecurrenceWeight params family prefixLen (prependTypeBit false τtail) *
          (1 - family.averagedSubMeas.total) :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.2

/-- `lem:from-H-to-G`.

The bipartite state in the goal `FromHToGStatement` and in the recurrence
hypothesis `hhalf` is taken to be `strategy.state` directly, matching the
paper's identification of `\ket{\psi_{\mathrm{bi}}}` with the symmetric
strategy's bipartite state (both are typed `QuantumState (ι × ι)` since
`SymStrat.state` is itself bipartite — see
`MIPStarRE/LDT/Test/Strategy.lean:75`). This keeps the Lean signature in
lockstep with the blueprint statement (`blueprint/src/chapter/ch09_pasting.tex:887–903`)
and lets `hself`/`hcons`/`hbound`, which are phrased over `strategy.state`,
be reused without an equality bridge. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params strategy.state family gamma zeta k) :
    FromHToGStatement params strategy strategy.state family gamma zeta k := by
  constructor -- FromHToGStatement
  · -- recurrenceStep: per-step Bernoulli-tail commutation
    intro ℓ hℓ τ
    constructor -- SDDOpRel
    /- Inductive step ℓ of the Bernoulli-tail recurrence (ld-pasting.tex
    lines 1346–1666). Three commutation sub-steps per induction step:
    (a) move rightmost Ĝ^{x_ℓ} to 2nd tensor factor (√(2ζ)),
    (b) commute leftmost Ĝ past remaining factors (√ν₄),
    (c) move leftmost to 2nd tensor factor (√(2ζ)).
    Per-step error: 2√(2ζ) + 2√ν₄ = fromHToGRecurrenceError. -/
    /- Outstanding gap (tracked in issue #395):
    `fromHToGRecurrenceLeftFamily` / `fromHToGRecurrenceRightFamily`
    (`Sandwich.lean:930-955`) are currently in collapsed form
    `allOutcomesExpansion.total * suffixBernoulliWeightOperator k ℓ τ` and
    `bernoulliTailFromFamily.total * suffixBernoulliWeightOperator k ℓ τ`;
    the paper's recurrence step relates the *intermediate* family
    `Ĥ^{x_≥ℓ} ⊗ S_{τ_≥ℓ}` to `Ĥ^{x_>ℓ} ⊗ S_{τ_>ℓ}` (eq:i-think-this-is-what-
    i'm-supposed-to-prove-2). To finish this case the families need to be
    refactored to expose the per-step Ĥ-on-suffix structure (a new
    `intermediateHSuffixFamily k ℓ` definition), then the three commutation
    sub-steps above can be discharged using `hhalf` (for √ν₄) and
    `cor:G-hat-facts` (for √(2ζ)), each composed via `sddOpRel_mono` /
    `sddOpRel_trans`, reusing `hself`/`hcons`/`hbound` directly against
    `strategy.state`. -/
    sorry
  · -- bernoulliPolynomialRewrite: aggregate k recurrence steps
    constructor -- SDDRel
    /- Aggregate k recurrence steps to show allOutcomesExpansion ≈ F(G).
    Total error ≤ k × per-step error ≤ fromHToGError. The chained
    `sddOpRel_trans` argument depends on the refactored families above
    so that `RightFamily ℓ` definitionally equals `LeftFamily (ℓ+1)`,
    enabling the telescoping in ld-pasting.tex lines 1354–1376. -/
    sorry

/-- `lem:chernoff-bernoulli-matrix`.

The core scalar inequality `ev ψ (F(X)) ≥ 1 - κ/(1-θ) - exp(-θ²k/2)` (paper
`ld-pasting.tex` lines 1670–1797) is taken as the explicit hypothesis
`hMatrixChernoff` rather than derived internally: its proof requires matrix
Chernoff infrastructure (additive Chernoff for sums of iid Bernoullis and
`Matrix.IsHermitian.spectral_theorem` composed with `ev`/`normalizedTrace`
expansion) that is not yet available in Mathlib. Once that infrastructure
lands, `hMatrixChernoff` can be discharged and removed from the signature. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := by
           intro _
           exact hXpsd
         sum_eq_total := by
           simp
         total_le_one := by
           exact hXleOne } : SubMeas Unit ι)
      (1 - kappa))
    (hMatrixChernoff :
      1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
        ev ψ (bernoulliTailOperator k degree X)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact hMatrixChernoff

/-- `cor:ld-pasting-N-completeness`. -/
theorem ldPastingNCompleteness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    LdPastingNCompletenessStatement params strategy family kappa
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k := by
  -- Chain the three completeness-chain lemmas (§9.4 of the paper)
  have _hOAO := overAllOutcomes params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound k
  constructor -- LdPastingNCompletenessStatement
  · exact hk -- largeEnough: 400 * m * d ≤ k
  · -- completenessBound
    constructor -- CompletenessAtLeast
    /- Paper: `cor:ld-pasting-N-completeness` (ld-pasting.tex lines 1798–1849).
    Chains: overAllOutcomes (ν₇) + fromHToG (ν₈) → SDDRel H vs F(G);
    chernoffBernoulliMatrix (θ = 1/(200m)): ev ψ F(G) ≥ 1-κ/(1-θ)-exp(...);
    SDDRel → mass transfer: ev ψ H ≥ ev ψ F(G) - √(ν₇+ν₈);
    parameter match: κ/(1-θ) ≤ κ(1+1/(100m)),
    exp(-θ²k/2) = exp(-k/(80000m²)).
    Requires: SDDRel → completeness transfer for Unit-indexed families. -/
    sorry

/-- `lem:ld-pasting-sub-measurement`. -/
lemma ldPastingSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      LdPastingSubMeasConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedSubMeas params family k, ?_⟩
  have hconsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk
  exact
    { largeEnough := hk
      constructedSubMeas := rfl
      pointConsistency := hconsistency
      completeness := hcompleteness.completenessBound }

/-- `thm:ld-pasting`. -/
theorem ldPasting
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingConclusion params strategy family H eps delta gamma kappa zeta k := by
  refine ⟨constructedPastedMeasurement params family k, ?_⟩
  have hsubmeasConsistency :=
    hAConsistency_submeas params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk
  have hcompleteness :=
    ldPastingNCompleteness params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcomplete hcons hself hbound k hk
  have hconsistency :=
    hAConsistency_completed params strategy eps delta gamma kappa zeta
      strategy.isNormalized family k hsubmeasConsistency hcompleteness.completenessBound
  exact
    { largeEnough := hk
      constructedMeasurement := rfl
      pointConsistency := hconsistency }


end MIPStarRE.LDT.Pasting
