import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions

/-!
# Section 12 pasting: complete and incomplete part self-consistency

Scalar and state-dependent-distance consequences for the complete and incomplete
parts of the pasted slice family.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lem:looks-easy-but-took-me-a-while`. -/
lemma looksEasyButTookMeAWhile
    (lambda : Error) (d : ℕ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda * (1 - lambda ^ d)
      ≤ 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) (1 / ((d + 1 : ℕ) : Error)) := by
  by_cases hl_boundary : lambda = 0 ∨ lambda = 1
  · -- Boundary cases `lambda = 0` and `lambda = 1` share the same proof pattern.
    have hz : 0 ≤ (0 : Error) ^ (1 / ((d + 1 : ℕ) : Error)) := Real.zero_rpow_nonneg _
    rcases hl_boundary with hzero | hone
    · subst hzero
      simpa using hz
    · subst hone
      simpa using hz
  · -- Interior case: `lambda ≠ 0` and `lambda ≠ 1`, hence `0 < lambda < 1`.
    push Not at hl_boundary
    have hlpos : 0 < lambda := lt_of_le_of_ne h0 (Ne.symm hl_boundary.1)
    let e : Error := 1 / ((d + 1 : ℕ) : Error)
    have hd1_ne : (((d + 1 : ℕ) : Error)) ≠ 0 := by positivity
    have he_mul : (((d + 1 : ℕ) : Error)) * e = 1 := by
      dsimp [e]
      field_simp [hd1_ne]
    have he_mul' : e * (((d + 1 : ℕ) : Error)) = 1 := by
      simpa [mul_comm] using he_mul
    have hgeom :
        (∑ i ∈ Finset.range d, lambda ^ i) * (1 - lambda) = 1 - lambda ^ d := by
      simpa [mul_comm] using geom_sum_mul_neg lambda d
    have hsum_le : ∑ i ∈ Finset.range d, lambda ^ i ≤ d := by
      calc
        ∑ i ∈ Finset.range d, lambda ^ i ≤ ∑ _i ∈ Finset.range d, (1 : Error) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact pow_le_one₀ h0 h1
        _ = d := by simp
    have hlin : 1 - lambda ^ d ≤ (d : Error) * (1 - lambda) := by
      rw [← hgeom]
      exact mul_le_mul_of_nonneg_right hsum_le (sub_nonneg.mpr h1)
    have hone_sub_nonneg : 0 ≤ 1 - lambda ^ d := by
      exact sub_nonneg.mpr (pow_le_one₀ h0 h1)
    have hone_sub_le_one : 1 - lambda ^ d ≤ 1 := by
      exact sub_le_self _ (pow_nonneg h0 _)
    have hpow_small : (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := by
      calc
        (1 - lambda ^ d) ^ (d + 1) = (1 - lambda ^ d) ^ d * (1 - lambda ^ d) := by
          rw [pow_succ]
        _ ≤ 1 * (1 - lambda ^ d) := by
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ hone_sub_nonneg hone_sub_le_one)
            hone_sub_nonneg
        _ = 1 - lambda ^ d := by ring
    have hd_nat : d ≤ 2 ^ (d + 1) := by
      refine le_trans (Nat.le_of_lt d.lt_two_pow_self) ?_
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by decide)
    have hd_cast : (d : Error) ≤ (2 : Error) ^ (d + 1) := by
      exact_mod_cast hd_nat
    have hone_rpow_pow : (Real.rpow (1 - lambda) e) ^ (d + 1) = 1 - lambda := by
      rw [← Real.rpow_natCast]
      change ((1 - lambda) ^ e) ^ (((d + 1 : ℕ) : Error)) = 1 - lambda
      rw [← Real.rpow_mul (sub_nonneg.mpr h1)]
      change (1 - lambda) ^ (e * (((d + 1 : ℕ) : Error))) = 1 - lambda
      rw [he_mul', Real.rpow_one]
    have hmain_pow : (1 - lambda ^ d) ^ (d + 1) ≤ (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
      calc
        (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := hpow_small
        _ ≤ (d : Error) * (1 - lambda) := hlin
        _ ≤ (2 : Error) ^ (d + 1) * (1 - lambda) := by
          exact mul_le_mul_of_nonneg_right hd_cast (sub_nonneg.mpr h1)
        _ = (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
          rw [mul_pow, hone_rpow_pow]
    have hroot :
        1 - lambda ^ d ≤ 2 * Real.rpow (1 - lambda) e := by
      exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d)
        (mul_nonneg zero_le_two (Real.rpow_nonneg (sub_nonneg.mpr h1) _)) hmain_pow
    have hlambda_rpow : Real.rpow (lambda ^ (d + 1)) e = lambda := by
      rw [← Real.rpow_natCast]
      change (lambda ^ (((d + 1 : ℕ) : Error))) ^ e = lambda
      rw [← Real.rpow_mul h0]
      change lambda ^ ((((d + 1 : ℕ) : Error)) * e) = lambda
      rw [he_mul, Real.rpow_one]
    have hmul_rpow :
        Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e =
          Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e := by
      exact Real.mul_rpow (pow_nonneg h0 _) (sub_nonneg.mpr h1)
    calc
      lambda * (1 - lambda ^ d) ≤ lambda * (2 * Real.rpow (1 - lambda) e) := by
        exact mul_le_mul_of_nonneg_left hroot h0
      _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
        calc
          lambda * (2 * Real.rpow (1 - lambda) e) = 2 * (lambda * Real.rpow (1 - lambda) e) := by
            ring
          _ = 2 * (Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e) := by
            nth_rw 1 [← hlambda_rpow]
          _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
            rw [← hmul_rpow]

/-- `lem:q-sdd-complete-part-slice-bound`. -/
lemma qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (x : Fq params) :
    qSDD ψbi
        ((completePartSubMeas params family x).liftLeft)
        ((completePartSubMeas params family x).liftRight)
      ≤
    qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ev ψbi (opTensor T T) := by
    calc
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight)
        = ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
            (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
              unfold qSDD qSDDCore
              simp only [Finset.univ_unique, PUnit.default_eq_unit,
                SubMeas.liftLeft, SubMeas.liftRight,
                mkLeftPlacedSubMeas_outcome, mkRightPlacedSubMeas_outcome,
                Matrix.conjTranspose_sub, Finset.sum_singleton,
                leftTensor_conjTranspose, rightTensor_conjTranspose,
                completePartSubMeas_outcome_unit, completePartSubMeas_total, T]
              simp [P]
      _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
            ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
              have hLherm : (leftTensor (ι₂ := ι) T)ᴴ = leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι)
                      (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (rightTensor (ι₁ := ι) T)ᴴ = rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι)
                    (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                    (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))
                  = ev ψbi (((leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) T -
                        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T) -
                      (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) T -
                        rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
                      ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
      _ = ev ψbi (leftTensor (ι₂ := ι) T) +
            ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ev ψbi (opTensor T T) := by
            simp [hTT]
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
    have hsum_left :
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) =
          ev ψbi (leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))
          = ev ψbi (∑ a, leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => leftTensor (ι₂ := ι) (P.outcome g))]
        _ = ev ψbi (leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = ev ψbi (leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    have hsum_right :
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) =
          ev ψbi (rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g))
          = ev ψbi (∑ a, rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => rightTensor (ι₁ := ι) (P.outcome g))]
        _ = ev ψbi (rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = ev ψbi (rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
              ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = ev ψbi
                      (((leftTensor (ι₂ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          leftTensor (ι₂ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)) -
                        (rightTensor (ι₁ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          rightTensor (ι₁ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [SubMeas.liftLeft, SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          simp [P.proj g]
      _ = (∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
  have hmatch :
      ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) ≤
        ev ψbi (opTensor T T) := by
    simpa [T, P, qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas, postprocess,
      completePartSubMeas, leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith

/-- `lem:g-complete-self-consistency`.
This is exactly the slice strong self-consistency hypothesis, repackaged under
the Section 12 statement name. -/
lemma gCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (_hperm : PermInvState ψbi)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    GCompleteSelfConsistencyStatement params ψbi family zeta := by
  exact ⟨hself.sliceSelfConsistency⟩

/-- Internal form of `cor:g-bot-self-consistency` after applying
`lem:g-complete-self-consistency`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:537-558`
uses `lem:g-complete-self-consistency` internally.  The paper-facing theorem
`gBotSelfConsistency` below derives that input from strong self-consistency
rather than exposing it as a public hypothesis. -/
theorem gBotSelfConsistency_ofCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (_hperm : PermInvState ψbi)
    (hcomplete : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    GBotSelfConsistencyStatement params ψbi family zeta := by
  refine {
    incompletePartSelfConsistency := ?_
  }
  rcases hcomplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
  have hcomplete_total :
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family)
        ≤ zeta := by
    unfold sddError at *
    calc
      avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((completePartLeftFamily params family) x)
              ((completePartRightFamily params family) x))
        ≤ avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
              apply avgOver_mono
              intro x
              simpa [completePartLeftFamily, completePartRightFamily,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas] using
                qSDD_completePart_le_slice params ψbi family x
      _ ≤ zeta := hcomplete_bound
  refine ⟨?_⟩
  calc
    sddError ψbi
        (uniformDistribution (SliceQuestion params))
        (incompletePartLeftFamily params family)
        (incompletePartRightFamily params family)
      =
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            let T : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family x).total
            have hdiff :
                leftTensor (ι₂ := ι) (1 - T) - rightTensor (ι₁ := ι) (1 - T) =
                  - (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              simp [T, leftTensor, rightTensor, sub_eq_add_neg]
              ring
            calc
              qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)
                =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))ᴴ) *
                      (leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))) := by
                          simp [qSDD, qSDDCore, incompletePartLeftFamily,
                            incompletePartRightFamily, incompletePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T]
              _ =
                  ev ψbi
                    ((-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))ᴴ *
                      (-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))) := by
                          rw [hdiff]
              _ =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                      (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
                          have hswap :
                              ((rightTensor (ι₁ := ι) T)ᴴ -
                                  (leftTensor (ι₂ := ι) T)ᴴ) *
                                  (rightTensor (ι₁ := ι) T - leftTensor (ι₂ := ι) T) =
                                ((leftTensor (ι₂ := ι) T)ᴴ -
                                    (rightTensor (ι₁ := ι) T)ᴴ) *
                                  (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
                            noncomm_ring
                          simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
              _ =
                  qSDD ψbi
                    ((completePartLeftFamily params family) x)
                    ((completePartRightFamily params family) x) := by
                          simp [qSDD, qSDDCore, completePartLeftFamily,
                            completePartRightFamily, completePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T,
                            (family.meas x).sum_eq_total]
    _ ≤ zeta := hcomplete_total

/-- `cor:g-bot-self-consistency`, source-facing form. -/
theorem gBotSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hperm : PermInvState ψbi)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    GBotSelfConsistencyStatement params ψbi family zeta :=
  gBotSelfConsistency_ofCompleteSelfConsistency params ψbi family zeta hperm
    (gCompleteSelfConsistency params ψbi family zeta hperm hself)

end MIPStarRE.LDT.Pasting
