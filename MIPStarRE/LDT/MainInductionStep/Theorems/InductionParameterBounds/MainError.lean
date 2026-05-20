import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.Preliminaries

/-!
# Section 6 — Main-Induction Error Bounds

This file is one leaf of `InductionParameterBounds`. It contains the scalar
consequences of the non-vacuous hypothesis `mainInductionError < 1`, including
the bounds `eps ≤ 1`, `delta ≤ 1`, `gamma ≤ 1`, `params.d ≤ params.q`, and
`mainInductionNu < 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma k_ne_zero_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    k ≠ 0 := by
  intro hk0
  subst hk0
  have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast params.hm
    nlinarith
  have hmain_ge_one : (1 : Error) ≤ mainInductionError params 0 eps delta gamma := by
    calc
      (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) * (0 + 1) := by
            nlinarith
      _ = mainInductionError params 0 eps delta gamma := by
            simp [mainInductionError, mainInductionNu]
  linarith

/-- In the nontrivial main-induction branch, the integer parameter `k` is
positive.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`, where the
successor proof is reduced to the nontrivial small-error regime before the
slice estimates are used.  The implication `mainInductionError < 1 → 1 ≤ k`
is a formalization-only scalar consequence: if `k = 0`, then the main-induction
error is at least `m^2`, hence at least `1`. -/
lemma one_le_k_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    1 ≤ k :=
  Nat.succ_le_of_lt
    (Nat.pos_of_ne_zero
      (k_ne_zero_of_mainInductionError_lt_one params k eps delta gamma hsmall))

/-- Internal helper: `mainInductionNu < 1` follows from `mainInductionError < 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma mainInductionNu_lt_one_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    mainInductionNu params k eps delta gamma < 1 := by
  by_cases hnu_nonneg : 0 ≤ mainInductionNu params k eps delta gamma
  · have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
      have hm_one : (1 : Error) ≤ (params.m : Error) := by
        exact_mod_cast params.hm
      nlinarith
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      positivity
    have hnu_le : mainInductionNu params k eps delta gamma
        ≤ mainInductionError params k eps delta gamma := by
      calc
        mainInductionNu params k eps delta gamma
          ≤ ((params.m : Error) ^ (2 : ℕ)) * mainInductionNu params k eps delta gamma := by
              nlinarith
        _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
              (mainInductionNu params k eps delta gamma +
                Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              have hinner :
                  mainInductionNu params k eps delta gamma ≤
                    mainInductionNu params k eps delta gamma +
                      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
                le_add_of_nonneg_right hexp_nonneg
              exact mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = mainInductionError params k eps delta gamma := by
              simp [mainInductionError]
    exact lt_of_le_of_lt hnu_le hsmall
  · linarith

private lemma mainInductionCoeff_ge_one
    (params : Parameters) {k : ℕ}
    (hk0 : k ≠ 0) :
    (1 : Error) ≤
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
  have hk_one : (1 : Error) ≤ (k : Error) := by
    have hk_nat_one : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    exact_mod_cast hk_nat_one
  have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast params.next.hm
  have hk_sq_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
    nlinarith [hk_one]
  have hm_sq_ge_one : (1 : Error) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    nlinarith [hm_one]
  nlinarith

private lemma le_one_of_mainInductionError_lt_one_of_scaled_bound
    (params : Parameters) {k : ℕ} {eps delta gamma x : Error}
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hscaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma) :
    x ≤ 1 := by
  have hk0 :=
    k_ne_zero_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hcoef_ge_one := mainInductionCoeff_ge_one params hk0
  have hnu_lt :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  have hroot_lt : Real.rpow x (1 / (1024 : Error)) < 1 := by
    by_contra hroot
    have hroot_ge : 1 ≤ Real.rpow x (1 / (1024 : Error)) :=
      le_of_not_gt hroot
    have : 1 ≤
        1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith
  exact le_one_of_rpow_le_one (by positivity) hroot_lt.le

private lemma mainInductionNu_scaled_component_le
    (params : Parameters) {k : ℕ} {x y z w : Error}
    (hrest_nonneg : 0 ≤ y + z + w) :
    1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) * x ≤
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
        (x + y + z + w) := by
  have hsummono : x ≤ x + y + z + w := by
    nlinarith [hrest_nonneg]
  have hcoef_nonneg :
      0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
    positivity
  exact mul_le_mul_of_nonneg_left hsummono hcoef_nonneg

/-- Internal helper: under `mainInductionError < 1`, the axis-parallel error `eps ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma eps_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have heps_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow eps (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using
      (mainInductionNu_scaled_component_le (params := params) (k := k)
        (x := Real.rpow eps (1 / (1024 : Error)))
        (y := Real.rpow delta (1 / (1024 : Error)))
        (z := Real.rpow gamma (1 / (1024 : Error)))
        (w := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))
        hrest_nonneg)
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall heps_scaled_le

/-- Internal helper: under `mainInductionError < 1`, the self-consistency error `delta ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma delta_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    delta ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have hdelta_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow delta (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using
      (mainInductionNu_scaled_component_le (params := params) (k := k)
        (x := Real.rpow delta (1 / (1024 : Error)))
        (y := Real.rpow eps (1 / (1024 : Error)))
        (z := Real.rpow gamma (1 / (1024 : Error)))
        (w := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))
        hrest_nonneg)
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hdelta_scaled_le

/-- Internal helper: `3 ≤ k² · m_next` in the small-parameter regime.

Exposed for cross-module use in `AvgSliceErrors`. -/
lemma three_le_k_sq_mul_next_m_of_hsmall
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : Error) ≤ ((k : Error) ^ (2 : ℕ)) * (params.next.m : Error) := by
  have hk1_nat : 1 ≤ k :=
    one_le_k_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hnext_two : params.next.m = 2
    · have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
      have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
      have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
        positivity
      have hnu_nonneg : 0 ≤ mainInductionNu params.next 1 eps delta gamma := by
        have hsumnn :
            0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) := by
          have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
          have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hratio_root_nonneg :
              0 ≤ Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
          nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg,
            hratio_root_nonneg]
        unfold mainInductionNu
        exact mul_nonneg (by positivity) hsumnn
      have hnext_two' : (params.next.m : Error) = 2 := by
        exact_mod_cast hnext_two
      have hexp_quarter :
          (1 / 4 : Error) ≤
            Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
        have hbase : (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := by
          norm_num
        have hexp :
            1 - (1 / 320000 : Error) ≤ Real.exp (-(1 / 320000 : Error)) := by
          simpa using Real.one_sub_le_exp_neg (1 / 320000 : Error)
        calc
          (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := hbase
          _ ≤ Real.exp (-(1 / 320000 : Error)) := hexp
          _ = Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
                rw [hnext_two']
                norm_num
      have hmain_ge_one : (1 : Error) ≤ mainInductionError params.next 1 eps delta gamma := by
        have hm_sq_eq_four : ((params.next.m : Error) ^ (2 : ℕ)) = 4 := by
          nlinarith [hnext_two']
        have hinner :
            (1 / 4 : Error) ≤
              mainInductionNu params.next 1 eps delta gamma +
                Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
          nlinarith
        calc
          (1 : Error) = ((params.next.m : Error) ^ (2 : ℕ)) * (1 / 4 : Error) := by
              rw [hm_sq_eq_four]
              norm_num
          _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) *
                (mainInductionNu params.next 1 eps delta gamma +
                  Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))) := by
                gcongr
          _ = mainInductionError params.next 1 eps delta gamma := by
                simp [mainInductionError]
      have hsmall' : mainInductionError params.next 1 eps delta gamma < 1 := by
        simpa using hsmall
      linarith
    · have hmnat : 2 ≤ params.next.m := Nat.succ_le_succ params.hm
      have hnext_ge_three : 3 ≤ params.next.m := by
        omega
      have : (3 : Error) ≤ (params.next.m : Error) := by
        exact_mod_cast hnext_ge_three
      simpa using this
  · have hk_ge_two : 2 ≤ k := by
      omega
    have hk_sq_ge_four : (4 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
      have hk_two : (2 : Error) ≤ (k : Error) := by
        exact_mod_cast hk_ge_two
      nlinarith
    have hnext_ge_two : (2 : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.succ_le_succ params.hm
    nlinarith

/-- Internal helper: under `mainInductionError < 1`, the diagonal error `gamma ≤ 1`.

Exposed for cross-module use in `MainTheorems`. -/
lemma gamma_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    gamma ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    exact add_nonneg (add_nonneg heps_root_nonneg hdelta_root_nonneg) hratio_root_nonneg
  have hgamma_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow gamma (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using
      (mainInductionNu_scaled_component_le (params := params) (k := k)
        (x := Real.rpow gamma (1 / (1024 : Error)))
        (y := Real.rpow eps (1 / (1024 : Error)))
        (z := Real.rpow delta (1 / (1024 : Error)))
        (w := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))
        hrest_nonneg)
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hgamma_scaled_le

/-- Internal helper: under `mainInductionError < 1`, `params.d ≤ params.q`.

Exposed for cross-module use in `MainTheorems`. -/
lemma dq_le_q_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    params.d ≤ params.q := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    nlinarith
  have hratio_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using
      (mainInductionNu_scaled_component_le (params := params) (k := k)
        (x := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))
        (y := Real.rpow eps (1 / (1024 : Error)))
        (z := Real.rpow delta (1 / (1024 : Error)))
        (w := Real.rpow gamma (1 / (1024 : Error)))
        hrest_nonneg)
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact
      le_one_of_mainInductionError_lt_one_of_scaled_bound
        params hsmall hratio_scaled_le
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  exact_mod_cast ((div_le_one hq_pos).1 hratio_le_one)

end MIPStarRE.LDT.MainInductionStep
