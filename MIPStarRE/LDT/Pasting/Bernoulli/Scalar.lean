import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff wrapper.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Scalar Bernoulli tail polynomial
`F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from
`lem:chernoff-bernoulli-matrix`. -/
noncomputable def scalarBernoulliTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The complementary lower-tail sum `∑_{r=0}^d C(k,r) p^r (1-p)^(k-r)`. -/
private noncomputable def scalarBernoulliLowerTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.range (degree + 1),
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The affine lower envelope used in the matrix Chernoff reduction. -/
noncomputable def bernoulliTailLowerAffine (theta c : Error) (p : Error) : Error :=
  (1 - c) - ((1 / (1 - theta)) * (1 - p))

/-- The scalar Bernoulli tail polynomial is nonnegative on `[0,1]`. -/
private lemma scalarBernoulliTail_nonneg
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ scalarBernoulliTail k degree p := by
  unfold scalarBernoulliTail
  refine Finset.sum_nonneg ?_
  intro r hr
  apply mul_nonneg
  · exact_mod_cast Nat.zero_le (Nat.choose k r)
  · apply mul_nonneg
    · exact pow_nonneg hp0 _
    · exact pow_nonneg (sub_nonneg.mpr hp1) _

/-- Hoeffding's lemma for a centered Bernoulli random variable. -/
private lemma bernoulli_centered_mgf_le {p t : Error}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (t * p) + p * Real.exp (t * (p - 1)) ≤
      Real.exp (t ^ (2 : ℕ) / 8) := by
  let pNN : NNReal := ⟨p, hp0⟩
  have hpNN_coe : (pNN : Error) = p := rfl
  have hpNN : pNN ≤ 1 := by
    exact hp1
  let μ : Measure Bool := (PMF.bernoulli pNN hpNN).toMeasure
  have hm : AEMeasurable (fun b : Bool => cond b (1 : Error) 0) μ := by
    simpa using (measurable_of_finite (fun b : Bool => cond b (1 : Error) 0)).aemeasurable
  have hb : ∀ᵐ b ∂μ, (cond b (1 : Error) 0) ∈ Set.Icc (0 : Error) 1 := by
    filter_upwards with b
    cases b <;> simp
  have hsubG := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have hcentered :
      ProbabilityTheory.HasSubgaussianMGF
        (fun b : Bool => p - cond b (1 : Error) 0)
        ((‖(1 : Error) - 0‖₊ / 2) ^ (2 : ℕ)) μ := by
    refine hsubG.neg.congr ?_
    filter_upwards with b
    simp [μ, PMF.bernoulli_expectation, hpNN_coe]
  have hmgf := hcentered.mgf_le t
  have hmgf' :
      p * Real.exp (t * (p - 1)) +
          Real.exp (p * t) * ((1 - pNN : NNReal) : Error) ≤
        Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) := by
    simpa [μ, ProbabilityTheory.mgf, PMF.integral_eq_sum, PMF.bernoulli_apply,
      smul_eq_mul, hpNN_coe, mul_comm, add_comm, add_left_comm, add_assoc]
      using hmgf
  have hcoeff : ((1 - pNN : NNReal) : Error) = 1 - p := by
    simpa [pNN] using (NNReal.coe_sub hpNN)
  have hexp :
      Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) = Real.exp (t ^ (2 : ℕ) / 8) := by
    congr 1
    ring_nf
  rw [hcoeff, hexp] at hmgf'
  simpa [mul_comm, add_comm] using hmgf'

/-- The centered moment-generating function of the binomial law is the binomial expansion of the
corresponding one-step Bernoulli moment-generating function. -/
private lemma binomial_centered_mgf_eq
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : Fin (k + 1) => p * k - i)
      ((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k).toMeasure) t =
        ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
  let pmf : PMF (Fin (k + 1)) := PMF.binomial ⟨p, hp0⟩ (by exact hp1) k
  calc
    ProbabilityTheory.mgf (fun i : Fin (k + 1) => p * k - i) pmf.toMeasure t
      = ∑ i : Fin (k + 1), (pmf i).toReal * Real.exp (t * (p * k - i)) := by
          rw [ProbabilityTheory.mgf, PMF.integral_eq_sum]
          simp [pmf, smul_eq_mul]
    _ = ∑ r ∈ Finset.range (k + 1),
          (pmf (Fin.ofNat (k + 1) r)).toReal * Real.exp (t * (p * k - r)) := by
          simpa using (Fin.sum_univ_eq_sum_range
            (f := fun r =>
              (pmf (Fin.ofNat (k + 1) r)).toReal * Real.exp (t * (p * k - r)))
            (n := k + 1))
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hr' : r < k + 1 := Finset.mem_range.mp hr
          have hpmf : ((pmf (Fin.ofNat (k + 1) r)).toReal : Error) =
              (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) := by
            have hfin : Fin.ofNat (k + 1) r = ⟨r, hr'⟩ := by
              ext
              simp [Fin.ofNat, Nat.mod_eq_of_lt hr']
            rw [hfin]
            change (((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k) ⟨r, hr'⟩).toReal : Error) = _
            rw [PMF.binomial_apply, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast,
              ENNReal.coe_toReal]
            let pNN : NNReal := ⟨p, hp0⟩
            have hpENN : (pNN : ENNReal) ≤ 1 := by
              exact_mod_cast hp1
            have hcoeff : (1 - (pNN : ENNReal)).toReal = 1 - p := by
              simpa [pNN] using
                (ENNReal.toReal_sub_of_le hpENN (by simp) :
                  (1 - (pNN : ENNReal)).toReal = 1 - (pNN : Error))
            have hcoeff' : (1 - (pNN : ENNReal)).toReal = 1 - p := hcoeff
            rw [hcoeff']
            change p ^ r * (1 - p) ^ (k - r) * (Nat.choose k r : Error) =
              (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
            ring
          calc
            (pmf (Fin.ofNat (k + 1) r)).toReal * Real.exp (t * (p * k - r))
              = ((Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) *
                  Real.exp (t * (p * k - r)) := by
                    rw [hpmf]
            _ = (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
                  Real.exp (t * (p * k - r)) := by
                    ring

/-- A Hoeffding bound for the centered binomial moment-generating function. -/
private lemma binomial_centered_mgf_le
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : Fin (k + 1) => p * k - i)
      ((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k).toMeasure) t ≤
        Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
  let a : Error := p * Real.exp (t * (p - 1))
  let b : Error := (1 - p) * Real.exp (t * p)
  have hrewrite :
      (∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          Real.exp (t * (p * k - r))) =
        ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    dsimp [a, b]
    have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hexp :
        Real.exp (t * (p * k - r)) =
          Real.exp (((k : Error) - r) * (t * p)) * Real.exp ((r : Error) * (t * (p - 1))) := by
      rw [show t * (p * k - r) =
          ((k : Error) - r) * (t * p) + (r : Error) * (t * (p - 1)) by ring]
      rw [Real.exp_add]
    have hfirst :
        Real.exp (((k : Error) - r) * (t * p)) = Real.exp (t * p) ^ (k - r) := by
      rw [← Nat.cast_sub hrle]
      simpa using (Real.exp_nat_mul (t * p) (k - r))
    have hsecond :
        Real.exp ((r : Error) * (t * (p - 1))) = Real.exp (t * (p - 1)) ^ r := by
      simpa using (Real.exp_nat_mul (t * (p - 1)) r)
    rw [hexp, hfirst, hsecond]
    calc
      (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          (Real.exp (t * p) ^ (k - r) * Real.exp (t * (p - 1)) ^ r)
        = (Nat.choose k r : Error) *
            ((p ^ r * Real.exp (t * (p - 1)) ^ r) *
              ((1 - p) ^ (k - r) * Real.exp (t * p) ^ (k - r))) := by
              ring
      _ = (Nat.choose k r : Error) *
            ((p * Real.exp (t * (p - 1))) ^ r * ((1 - p) * Real.exp (t * p)) ^ (k - r)) := by
              rw [← mul_pow, ← mul_pow]
      _ = (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
              rfl
  have hpow :
      (∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r))) =
        (a + b) ^ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow a b k).symm
  calc
    ProbabilityTheory.mgf (fun i : Fin (k + 1) => p * k - i)
        ((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k).toMeasure) t
      = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) :=
        binomial_centered_mgf_eq k hp0 hp1
    _ = ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := hrewrite
    _ = (a + b) ^ k := hpow
    _ ≤ (Real.exp (t ^ (2 : ℕ) / 8)) ^ k := by
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            positivity
          have hOneSub_nonneg : 0 ≤ 1 - p := by
            linarith
          have hb_nonneg : 0 ≤ b := by
            dsimp [b]
            exact mul_nonneg hOneSub_nonneg (by positivity)
          have hab_nonneg : 0 ≤ a + b := by
            linarith
          apply pow_le_pow_left₀ hab_nonneg
          simpa [a, b, add_comm] using bernoulli_centered_mgf_le hp0 hp1
    _ = Real.exp ((k : Error) * (t ^ (2 : ℕ) / 8)) := by
          symm
          simpa [mul_comm] using (Real.exp_nat_mul (t ^ (2 : ℕ) / 8) k)
    _ = Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
          congr 1
          ring

/-- The lower tail of the binomial law is the lower partial sum of the Bernoulli polynomial. -/
private lemma binomial_lowerTail_eq
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k).toMeasure).real
        {i : Fin (k + 1) | (i : Error) ≤ degree} =
      scalarBernoulliLowerTail k degree p := by
  let pmf : PMF (Fin (k + 1)) := PMF.binomial ⟨p, hp0⟩ (by exact hp1) k
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  have hpmf : ∀ {r : ℕ}, r < k + 1 → ((pmf (Fin.ofNat (k + 1) r)).toReal : Error) = f r := by
    intro r hr
    have hfin : Fin.ofNat (k + 1) r = ⟨r, hr⟩ := by
      ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt hr]
    rw [hfin]
    change (((PMF.binomial ⟨p, hp0⟩ (by exact hp1) k) ⟨r, hr⟩).toReal : Error) = f r
    rw [PMF.binomial_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.coe_toReal]
    let pNN : NNReal := ⟨p, hp0⟩
    have hpENN : (pNN : ENNReal) ≤ 1 := by
      exact_mod_cast hp1
    have hcoeff : (1 - (pNN : ENNReal)).toReal = 1 - p := by
      simpa [pNN] using
        (ENNReal.toReal_sub_of_le hpENN (by simp) :
          (1 - (pNN : ENNReal)).toReal = 1 - (pNN : Error))
    have hcoeff' : (1 - (pNN : ENNReal)).toReal = 1 - p := hcoeff
    rw [hcoeff']
    change p ^ r * (1 - p) ^ (k - r) * (Nat.choose k r : Error) = f r
    ring
  calc
    pmf.toMeasure.real {i : Fin (k + 1) | (i : Error) ≤ degree}
      = ∑ i : Fin (k + 1), if (i : Error) ≤ degree then (pmf i).toReal else 0 := by
          rw [measureReal_def]
          let s : Finset (Fin (k + 1)) :=
            Finset.univ.filter fun i : Fin (k + 1) => (i : Error) ≤ degree
          have hs : (↑s : Set (Fin (k + 1))) = {i : Fin (k + 1) | (i : Error) ≤ degree} := by
            ext i
            simp [s]
          rw [← hs, PMF.toMeasure_apply_finset, ENNReal.toReal_sum]
          · simp [s, Finset.sum_filter]
          · intro i hi
            simpa using PMF.apply_ne_top pmf i
    _ = ∑ r ∈ Finset.range (k + 1),
          if (r : Error) ≤ degree then (pmf (Fin.ofNat (k + 1) r)).toReal else 0 := by
          simpa using (Fin.sum_univ_eq_sum_range
            (f := fun r =>
              if (r : Error) ≤ degree then (pmf (Fin.ofNat (k + 1) r)).toReal else 0)
            (n := k + 1))
    _ = ∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hr' : r < k + 1 := Finset.mem_range.mp hr
          by_cases hrd : r ≤ degree
          · have hrd' : (r : Error) ≤ degree := by
              exact_mod_cast hrd
            rw [if_pos hrd', if_pos hrd]
            exact hpmf hr'
          · have hrd' : ¬ (r : Error) ≤ degree := by
              exact fun h => hrd (by exact_mod_cast h)
            rw [if_neg hrd', if_neg hrd]
    _ = ∑ r ∈ Finset.range (degree + 1), f r := by
          by_cases hdk : degree ≤ k
          · have hRange :
                (∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (degree + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                simp [hrle]
            have hIcoZero :
                (∑ r ∈ Finset.Ico (degree + 1) (k + 1), if r ≤ degree then f r else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro r hr
                have hlt : degree < r := (Finset.mem_Ico.mp hr).1
                simp [Nat.not_le.mpr hlt]
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := fun r => if r ≤ degree then f r else 0)
                (h := Nat.succ_le_succ hdk)
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                =
                  ∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0 := by
                      symm
                      rw [hIcoZero, add_zero] at hsplit
                      exact hsplit
              _ = ∑ r ∈ Finset.range (degree + 1), f r := hRange
          · have hdk' : k < degree := Nat.lt_of_not_ge hdk
            have hAll :
                (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (k + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                have hrdeg : r ≤ degree := hrle.trans (Nat.le_of_lt hdk')
                simp [hrdeg]
            have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
              refine Finset.sum_eq_zero ?_
              intro r hr
              have hklt : k < r := (Finset.mem_Ico.mp hr).1
              change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
              rw [Nat.choose_eq_zero_of_lt hklt]
              simp
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                = ∑ r ∈ Finset.range (k + 1), f r := hAll
              _ = ∑ r ∈ Finset.range (degree + 1), f r := by
                    rw [hIcoZero, add_zero] at hsplit
                    exact hsplit
    _ = scalarBernoulliLowerTail k degree p := by
          rfl

/-- The binomial lower tail obeys the additive Hoeffding bound. -/
private lemma scalarBernoulliLowerTail_le_exp
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpd : (degree : Error) / (k : Error) ≤ p) :
    scalarBernoulliLowerTail k degree p ≤
      Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
  by_cases hk0 : k = 0
  · subst hk0
    have htail : scalarBernoulliLowerTail 0 degree p = 1 := by
      unfold scalarBernoulliLowerTail
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r hr hr0
        have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr0
        simp [Nat.choose_eq_zero_of_lt hrpos]
      · simp
    rw [htail]
    simp
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    let ε : Error := p * (k : Error) - degree
    let t : Error := 4 * (p - degree / (k : Error))
    let pmf : PMF (Fin (k + 1)) := PMF.binomial ⟨p, hp0⟩ (by exact hp1) k
    have hε_nonneg : 0 ≤ ε := by
      dsimp [ε]
      have hpd' : (degree : Error) ≤ p * (k : Error) := by
        rw [div_le_iff₀ hkpos] at hpd
        simpa [mul_comm] using hpd
      linarith
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      nlinarith
    have hInt :
        Integrable (fun i : Fin (k + 1) => Real.exp (t * (p * (k : Error) - i)))
          pmf.toMeasure := by
      exact Integrable.of_finite
    have hCher :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := pmf.toMeasure) (X := fun i : Fin (k + 1) => p * (k : Error) - i) (t := t) ε
        ht_nonneg hInt
    have hEvent :
        {i : Fin (k + 1) | ε ≤ p * (k : Error) - i} =
          {i : Fin (k + 1) | (i : Error) ≤ degree} := by
      ext i
      dsimp [ε]
      constructor <;> intro hi <;> linarith
    calc
      scalarBernoulliLowerTail k degree p
        = pmf.toMeasure.real {i : Fin (k + 1) | ε ≤ p * (k : Error) - i} := by
            rw [hEvent]
            symm
            exact binomial_lowerTail_eq k degree hp0 hp1
      _ ≤ Real.exp (-t * ε) * ProbabilityTheory.mgf (fun i : Fin (k + 1) => p * (k : Error) - i)
            pmf.toMeasure t := hCher
      _ ≤ Real.exp (-t * ε) * Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
            gcongr
            exact binomial_centered_mgf_le k hp0 hp1 (t := t)
      _ = Real.exp (-t * ε + (k : Error) * t ^ (2 : ℕ) / 8) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
            have hε_eq : ε = (p - degree / (k : Error)) * (k : Error) := by
              dsimp [ε]
              field_simp [hkpos.ne']
            dsimp [t]
            rw [hε_eq]
            congr 1
            ring_nf

/-- The lower and upper binomial tails partition the full Bernoulli polynomial. -/
private lemma scalarBernoulliLowerTail_add_scalarBernoulliTail
    (k degree : ℕ) (p : Error) :
    scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p = 1 := by
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  have hfull : ∑ r ∈ Finset.range (k + 1), f r = 1 := by
    calc
      ∑ r ∈ Finset.range (k + 1), f r
        = ∑ r ∈ Finset.range (k + 1), p ^ r * (1 - p) ^ (k - r) * Nat.choose k r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              ring
      _ = (p + (1 - p)) ^ k := by
            simpa using (add_pow p (1 - p) k).symm
      _ = 1 := by
            ring
  by_cases hdk : degree ≤ k
  · have hTail :
        ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r = scalarBernoulliTail k degree p := by
      have hIco : Finset.Ico (degree + 1) (k + 1) = Finset.Icc (degree + 1) k := by
        ext r
        simp
      simp [scalarBernoulliTail, f, hIco]
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        =
          (∑ r ∈ Finset.range (degree + 1), f r) +
            ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r := by
              rw [scalarBernoulliLowerTail, ← hTail]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            exact Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ hdk)
      _ = 1 := hfull
  · have hdk' : k < degree := Nat.lt_of_not_ge hdk
    have hTailZero : scalarBernoulliTail k degree p = 0 := by
      unfold scalarBernoulliTail
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hr1 : degree + 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hr2 : r ≤ k := (Finset.mem_Icc.mp hr).2
      omega
    have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hklt : k < r := (Finset.mem_Ico.mp hr).1
      change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
      rw [Nat.choose_eq_zero_of_lt hklt]
      simp
    have hsplit :=
      Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        = ∑ r ∈ Finset.range (degree + 1), f r := by
            rw [scalarBernoulliLowerTail, hTailZero, add_zero]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            rw [hIcoZero, add_zero] at hsplit
            exact hsplit.symm
      _ = 1 := hfull

/-- The scalar Bernoulli tail satisfies the additive Hoeffding lower bound used by
`lem:chernoff-bernoulli-matrix`. -/
theorem scalarBernoulliTail_hoeffding_lower_bound
    (k degree : ℕ) {p : Error}
    (hpd : (degree : Error) / (k : Error) ≤ p) (hp1 : p ≤ 1) :
    1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
      scalarBernoulliTail k degree p := by
  have hp0 : 0 ≤ p := by
    have hdk_nonneg : 0 ≤ (degree : Error) / (k : Error) := by
      positivity
    linarith
  have hLower := scalarBernoulliLowerTail_le_exp k degree hp0 hp1 hpd
  have hsum := scalarBernoulliLowerTail_add_scalarBernoulliTail k degree p
  linarith

/-- The paper's size condition `k ≥ 2d/θ` implies `d/k ≤ θ/2`. -/
private lemma degree_div_le_theta_half
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hk : (2 * (degree : Error)) / theta ≤ (k : Error)) :
    (degree : Error) / (k : Error) ≤ theta / 2 := by
  by_cases hk0 : k = 0
  · subst hk0
    have hdeg : degree = 0 := by
      by_contra hdeg
      have hdegpos : 0 < (degree : Error) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hdeg
      have hfracpos : 0 < (2 * (degree : Error)) / theta := by
        positivity
      linarith
    subst hdeg
    have hnonneg : 0 ≤ theta / 2 := by
      positivity
    simpa using hnonneg
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    have hk' := hk
    field_simp [hθ0.ne', hkpos.ne'] at hk'
    have h2 : (2 * (degree : Error)) / (k : Error) ≤ theta := by
      rw [div_le_iff₀ hkpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk'
    have h2' : 2 * ((degree : Error) / (k : Error)) ≤ theta := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2
    linarith

/-- Pointwise lower bound on `[0,1]` combining the scalar Hoeffding estimate with
`k ≥ 2d/θ`. -/
theorem bernoulliTailLowerAffine_le_scalarBernoulliTail
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliTailLowerAffine theta
      (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤
        scalarBernoulliTail k degree p := by
  by_cases hpθ : p < theta
  · have htail_nonneg : 0 ≤ scalarBernoulliTail k degree p :=
      scalarBernoulliTail_nonneg k degree hp0 hp1
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac_ge_one : 1 ≤ (1 - p) / (1 - theta) := by
      rw [one_le_div₀ hθden]
      linarith
    have hbase : 1 - (1 - p) / (1 - theta) ≤ 0 := by
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      positivity
    have hLower :
        bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤ 0 := by
      unfold bernoulliTailLowerAffine
      have hrew : (1 / (1 - theta)) * (1 - p) = (1 - p) / (1 - theta) := by
        ring
      rw [hrew]
      linarith
    exact hLower.trans htail_nonneg
  · have hpθ' : theta ≤ p := le_of_not_gt hpθ
    have hdk_half : (degree : Error) / (k : Error) ≤ theta / 2 :=
      degree_div_le_theta_half theta k degree hθ0 hk
    have hdk_le_p : (degree : Error) / (k : Error) ≤ p := by
      linarith
    have hScalar := scalarBernoulliTail_hoeffding_lower_bound k degree hdk_le_p hp1
    have hk_nonneg : 0 ≤ (k : Error) := by positivity
    have hpd_half : theta / 2 ≤ p - (degree : Error) / (k : Error) := by
      linarith
    have hsq : theta ^ (2 : ℕ) / 4 ≤ (p - (degree : Error) / (k : Error)) ^ (2 : ℕ) := by
      nlinarith [hpd_half, hθ0.le,
        sq_nonneg (p - (degree : Error) / (k : Error) - theta / 2)]
    have hExpCompare :
        Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
          Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsq, hk_nonneg]
    have hConst :
        1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
          1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) *
            (k : Error))) := by
      linarith
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hθinv_nonneg : 0 ≤ 1 / (1 - theta) := one_div_nonneg.mpr hθden.le
    have hp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hterm_nonneg : 0 ≤ (1 / (1 - theta)) * (1 - p) :=
      mul_nonneg hθinv_nonneg hp_nonneg
    have hLowerConst :
        bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤
          1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      unfold bernoulliTailLowerAffine
      linarith
    exact hLowerConst.trans (hConst.trans hScalar)

end MIPStarRE.LDT.Pasting
