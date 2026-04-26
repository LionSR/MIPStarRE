import MIPStarRE.LDT.Pasting.Defs.Tuples

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false

/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
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

end MIPStarRE.LDT.Pasting
