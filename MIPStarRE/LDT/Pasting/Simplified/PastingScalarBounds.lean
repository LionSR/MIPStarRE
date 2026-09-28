import MIPStarRE.LDT.Pasting.Simplified.PastingFinal
import MIPStarRE.LDT.Pasting.Simplified.ConsistencyAggregation
import MIPStarRE.LDT.Pasting.Bernoulli.ScalarBounds

/-!
# Scalar bounds for simplified pasting

The root budget from first-moment completeness is controlled by the
exact sum of prefix lengths. These bounds prepare the quantitative
`21 k² √m` form of the pasting theorem.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:ld-pasting`.
- `references/ldt-paper/ld-pasting.tex`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators

/-- The root budget has at most quadratic growth. -/
theorem marginalRootBudget_le_half_square (k : ℕ) :
    marginalRootBudget k ≤ (k : Error) ^ (2 : ℕ) / 2 := by
  calc
    marginalRootBudget k ≤ ∑ i : Fin k, (i.1 : Error) :=
      marginalRootBudget_le_prefix_sum k
    _ = (k : Error) * ((k : Error) - 1) / 2 := sum_fin_prefix_lengths k
    _ ≤ (k : Error) ^ (2 : ℕ) / 2 := by
      have hk : 0 ≤ (k : Error) := by positivity
      nlinarith

/-- The quotient in the first-moment loss does not enlarge the root
budget beyond its quadratic scale when there is at least one extra
attempt beyond the degree. -/
theorem marginalRootBudget_div_le_half_square
    (d k : ℕ) (hdk : d < k) :
    marginalRootBudget k / ((k - d : ℕ) : Error) ≤
      (k : Error) ^ (2 : ℕ) / 2 := by
  have hden_nat : 1 ≤ k - d := by omega
  have hden : (1 : Error) ≤ ((k - d : ℕ) : Error) := by exact_mod_cast hden_nat
  have hbudget_nonneg : 0 ≤ marginalRootBudget k := by
    unfold marginalRootBudget
    positivity
  calc
    marginalRootBudget k / ((k - d : ℕ) : Error) ≤ marginalRootBudget k := by
      exact div_le_self hbudget_nonneg hden
    _ ≤ (k : Error) ^ (2 : ℕ) / 2 := marginalRootBudget_le_half_square k

/-- The square root of the Section 11 commutativity error, expressed
at the eighth-power scale used by simplified pasting. -/
theorem sqrt_comMainError_le_eighth_sum
    (params : Parameters) (gamma zeta : Error)
    (hgamma : 0 ≤ gamma) (hzeta : 0 ≤ zeta) :
    Real.sqrt (Commutativity.comMainError params gamma zeta) ≤
      (11 / 2 : Error) * Real.sqrt (params.m : Error) *
        (Real.rpow gamma (1 / (8 : Error)) +
          Real.rpow zeta (1 / (8 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (8 : Error))) := by
  let a : Error := Real.rpow gamma (1 / (8 : Error))
  let b : Error := Real.rpow zeta (1 / (8 : Error))
  let c : Error := Real.rpow ((params.d : Error) / (params.q : Error))
    (1 / (8 : Error))
  have hratio : 0 ≤ (params.d : Error) / (params.q : Error) := by positivity
  have ha : 0 ≤ a := Real.rpow_nonneg hgamma _
  have hb : 0 ≤ b := Real.rpow_nonneg hzeta _
  have hc : 0 ≤ c := Real.rpow_nonneg hratio _
  have ha2 : a ^ (2 : ℕ) = Real.rpow gamma (1 / (4 : Error)) := by
    dsimp [a]
    calc
      (Real.rpow gamma (1 / (8 : Error))) ^ (2 : ℕ) =
          (Real.rpow gamma (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (8 : Error)) * (2 : Error)) := by
        symm
        exact Real.rpow_mul hgamma _ _
      _ = _ := by norm_num
  have hb2 : b ^ (2 : ℕ) = Real.rpow zeta (1 / (4 : Error)) := by
    dsimp [b]
    calc
      (Real.rpow zeta (1 / (8 : Error))) ^ (2 : ℕ) =
          (Real.rpow zeta (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (8 : Error)) * (2 : Error)) := by
        symm
        exact Real.rpow_mul hzeta _ _
      _ = _ := by norm_num
  have hc2 : c ^ (2 : ℕ) =
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (4 : Error)) := by
    dsimp [c]
    calc
      (Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (8 : Error))) ^
          (2 : ℕ) =
          (Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (8 : Error))) ^
            (2 : Error) := by norm_num
      _ = Real.rpow ((params.d : Error) / (params.q : Error))
          ((1 / (8 : Error)) * (2 : Error)) := by
        symm
        exact Real.rpow_mul hratio _ _
      _ = _ := by norm_num
  have hsum : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤
      (a + b + c) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have hroot : Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ)) ≤
      a + b + c := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · exact hsum
  have hthirty : Real.sqrt (30 : Error) ≤ 11 / 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num
  have hm : 0 ≤ (params.m : Error) := by positivity
  have hs : 0 ≤ Real.sqrt (params.m : Error) := Real.sqrt_nonneg _
  have hq : 0 ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) := by positivity
  calc
    Real.sqrt (Commutativity.comMainError params gamma zeta) =
        Real.sqrt (30 : Error) * Real.sqrt (params.m : Error) *
          Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
      rw [Commutativity.comMainError, ← ha2, ← hb2, ← hc2]
      rw [mul_assoc]
      rw [Real.sqrt_mul (by positivity : 0 ≤ (30 : Error))]
      rw [Real.sqrt_mul hm]
      ring
    _ ≤ (11 / 2 : Error) * Real.sqrt (params.m : Error) * (a + b + c) := by
      gcongr
    _ = _ := by rfl

/-- Algebraic form of the `21 k² √m` budget. Each source of error is
charged to its corresponding eighth-power summand. -/
private theorem pasting_error_algebra
    (K R a b c e r : Error)
    (hK : 2 ≤ K) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hr : 0 ≤ r) :
    2 * K * e + (2 * K + 1) * (4 * R * (a + b)) +
      2 * K * (K - 1) * ((11 / 2 : Error) * R * (c + e + r) + 4 * e) +
      K ^ (2 : ℕ) * e + K ^ (2 : ℕ) * r ≤
        21 * K ^ (2 : ℕ) * R * (a + b + c + e + r) := by
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hK1 : 0 ≤ K - 1 := by linarith
  have hab : 0 ≤ a + b := by linarith
  have hcer : 0 ≤ c + e + r := by linarith
  have hKR : 0 ≤ K ^ (2 : ℕ) * R := by positivity
  have hcoeff : 4 * (2 * K + 1) ≤ 9 * K ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (K - 2)]
  have hprefix :
      (2 * K + 1) * (4 * R * (a + b)) ≤
        9 * K ^ (2 : ℕ) * R * (a + b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff)
      (mul_nonneg hR0 hab)]
  have hcommcoeff : K * (K - 1) ≤ K ^ (2 : ℕ) := by nlinarith
  have hcomm :
      2 * K * (K - 1) * ((11 / 2 : Error) * R * (c + e + r)) ≤
        11 * K ^ (2 : ℕ) * R * (c + e + r) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcommcoeff)
      (mul_nonneg hR0 hcer)]
  have hroot : K * (K - 1) * e ≤ K ^ (2 : ℕ) * R * e := by
    have hleft : K * (K - 1) * e ≤ K ^ (2 : ℕ) * e := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcommcoeff) he]
    have hright : K ^ (2 : ℕ) * e ≤ K ^ (2 : ℕ) * R * e := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (mul_nonneg (sq_nonneg K) he)]
    exact hleft.trans hright
  have hzeta : 2 * K * e ≤ K ^ (2 : ℕ) * R * e := by
    have hcoef : 2 * K ≤ K ^ (2 : ℕ) := by nlinarith
    have hleft : 2 * K * e ≤ K ^ (2 : ℕ) * e := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) he]
    have hright : K ^ (2 : ℕ) * e ≤ K ^ (2 : ℕ) * R * e := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (mul_nonneg (sq_nonneg K) he)]
    exact hleft.trans hright
  have hmass : K ^ (2 : ℕ) * e ≤ K ^ (2 : ℕ) * R * e := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (mul_nonneg (sq_nonneg K) he)]
  have hcollision : K ^ (2 : ℕ) * r ≤ K ^ (2 : ℕ) * R * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (mul_nonneg (sq_nonneg K) hr)]
  have hsum :
      9 * K ^ (2 : ℕ) * R * (a + b) +
        11 * K ^ (2 : ℕ) * R * (c + e + r) +
        8 * (K ^ (2 : ℕ) * R * e) +
        K ^ (2 : ℕ) * R * e + K ^ (2 : ℕ) * R * e +
        K ^ (2 : ℕ) * R * r ≤
          21 * K ^ (2 : ℕ) * R * (a + b + c + e + r) := by
    nlinarith [mul_nonneg hKR ha, mul_nonneg hKR hb,
      mul_nonneg hKR hc, mul_nonneg hKR hr]
  nlinarith [hprefix, hcomm, hroot, hzeta, hmass, hcollision, hsum]

/-- On the unit interval, the eighth power dominates both the
parameter and its square root. -/
theorem error_le_eighth_and_sqrt_le_eighth
    (x : Error) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ Real.rpow x (1 / (8 : Error)) ∧
      Real.sqrt x ≤ Real.rpow x (1 / (8 : Error)) := by
  have hfirst := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
    (by norm_num : 0 ≤ (1 / (8 : Error)))
    (by norm_num : (1 / (8 : Error)) ≤ 1)
  have hsecond := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
    (by norm_num : 0 ≤ (1 / (8 : Error)))
    (by norm_num : (1 / (8 : Error)) ≤ (1 / (2 : Error)))
  constructor
  · simpa using hfirst
  · simpa [Real.sqrt_eq_rpow] using hsecond

/-- The axis-line and point-test error enters pasting at the
eighth-power scale. -/
theorem sqrt_axis_error_le_eighth
    (M eps delta : Error)
    (hM : 1 ≤ M)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    Real.sqrt (8 * M * eps + 4 * delta) ≤
      4 * Real.sqrt M *
        (Real.rpow eps (1 / (8 : Error)) +
          Real.rpow delta (1 / (8 : Error))) := by
  let a : Error := Real.rpow eps (1 / (8 : Error))
  let b : Error := Real.rpow delta (1 / (8 : Error))
  let R : Error := Real.sqrt M
  have ha0 : 0 ≤ a := Real.rpow_nonneg heps0 _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hdelta0 _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ (2 : ℕ) = M := Real.sq_sqrt (by linarith)
  have hepsq : eps ≤ a ^ (2 : ℕ) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge' heps0 heps1
      (by norm_num : 0 ≤ (1 / (4 : Error)))
      (by norm_num : (1 / (4 : Error)) ≤ 1)
    have ha2 : a ^ (2 : ℕ) = Real.rpow eps (1 / (4 : Error)) := by
      dsimp [a]
      calc
        (Real.rpow eps (1 / (8 : Error))) ^ (2 : ℕ) =
            (Real.rpow eps (1 / (8 : Error))) ^ (2 : Error) := by norm_num
        _ = Real.rpow eps ((1 / (8 : Error)) * (2 : Error)) := by
          symm
          exact Real.rpow_mul heps0 _ _
        _ = _ := by norm_num
    simpa [ha2] using hp
  have hdeltaq : delta ≤ b ^ (2 : ℕ) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge' hdelta0 hdelta1
      (by norm_num : 0 ≤ (1 / (4 : Error)))
      (by norm_num : (1 / (4 : Error)) ≤ 1)
    have hb2 : b ^ (2 : ℕ) = Real.rpow delta (1 / (4 : Error)) := by
      dsimp [b]
      calc
        (Real.rpow delta (1 / (8 : Error))) ^ (2 : ℕ) =
            (Real.rpow delta (1 / (8 : Error))) ^ (2 : Error) := by norm_num
        _ = Real.rpow delta ((1 / (8 : Error)) * (2 : Error)) := by
          symm
          exact Real.rpow_mul hdelta0 _ _
        _ = _ := by norm_num
    simpa [hb2] using hp
  have h1 : 8 * M * eps ≤ 8 * M * a ^ (2 : ℕ) := by
    gcongr
  have h2 : 4 * delta ≤ 4 * M * b ^ (2 : ℕ) := by
    have hmb : b ^ (2 : ℕ) ≤ M * b ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sq_nonneg b)]
    nlinarith
  have hcross : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hright : 0 ≤ 4 * R * (a + b) := by positivity
  have h3 : 8 * M * a ^ (2 : ℕ) + 4 * M * b ^ (2 : ℕ) ≤
      (4 * R * (a + b)) ^ (2 : ℕ) := by
    rw [← hR2]
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg a),
      mul_nonneg (sq_nonneg R) (sq_nonneg b),
      mul_nonneg (sq_nonneg R) hcross]
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hright
  · exact (add_le_add h1 h2).trans h3

/-- The five-term eighth-power sum in the simplified pasting theorem. -/
noncomputable def pastingEighthSum
    (params : Parameters) (eps delta gamma zeta : Error) : Error :=
  Real.rpow eps (1 / (8 : Error)) +
    Real.rpow delta (1 / (8 : Error)) +
    Real.rpow gamma (1 / (8 : Error)) +
    Real.rpow zeta (1 / (8 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (8 : Error))

/-- The explicit completed-measurement error satisfies the simplified
paper's quantitative pasting bound for positive degree. -/
theorem distinctSuccessPastingError_le_paperBound
    (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hd : 0 < params.d) (hdk : params.d < k)
    (hdq : params.d ≤ params.q)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) :
    distinctSuccessPastingError params k eps delta gamma kappa zeta ≤
      (k : Error) / ((k - params.d : ℕ) : Error) * kappa +
        21 * (k : Error) ^ (2 : ℕ) * Real.sqrt (params.m : Error) *
          pastingEighthSum params eps delta gamma zeta := by
  let K : Error := k
  let R : Error := Real.sqrt (params.m : Error)
  let a : Error := Real.rpow eps (1 / (8 : Error))
  let b : Error := Real.rpow delta (1 / (8 : Error))
  let c : Error := Real.rpow gamma (1 / (8 : Error))
  let e : Error := Real.rpow zeta (1 / (8 : Error))
  let r : Error := Real.rpow ((params.d : Error) / (params.q : Error))
    (1 / (8 : Error))
  have hK_nat : 2 ≤ k := by omega
  have hK : 2 ≤ K := by
    change (2 : Error) ≤ (k : Error)
    exact_mod_cast hK_nat
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 0 ≤ K - 1 := by linarith
  have hm : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ (2 : ℕ) = (params.m : Error) := Real.sq_sqrt (by linarith)
  have hR : 1 ≤ R := by nlinarith
  have ha : 0 ≤ a := Real.rpow_nonneg heps0 _
  have hb : 0 ≤ b := Real.rpow_nonneg hdelta0 _
  have hc : 0 ≤ c := Real.rpow_nonneg hgamma0 _
  have he : 0 ≤ e := Real.rpow_nonneg hzeta0 _
  have hq : (0 : Error) < (params.q : Error) := by exact_mod_cast params.hq
  have hratio0 : 0 ≤ (params.d : Error) / (params.q : Error) := by positivity
  have hratio1 : (params.d : Error) / (params.q : Error) ≤ 1 := by
    exact (div_le_one hq).2 (by exact_mod_cast hdq)
  have hr : 0 ≤ r := Real.rpow_nonneg hratio0 _
  have hζ := (error_le_eighth_and_sqrt_le_eighth zeta hzeta0 hzeta1).1
  have hrootζ := (error_le_eighth_and_sqrt_le_eighth zeta hzeta0 hzeta1).2
  have hratio := (error_le_eighth_and_sqrt_le_eighth
    ((params.d : Error) / (params.q : Error)) hratio0 hratio1).1
  have haxis := sqrt_axis_error_le_eighth
    (params.m : Error) eps delta hm heps0 heps1 hdelta0 hdelta1
  have hcom := sqrt_comMainError_le_eighth_sum params gamma zeta hgamma0 hzeta0
  have hsqrt2 : Real.sqrt (2 : Error) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have hsqrt2ζ : Real.sqrt (2 * zeta) ≤ 2 * e := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt2) (Real.sqrt_nonneg zeta)]
  have hbudget := marginalRootBudget_div_le_half_square params.d k hdk
  have hmass : Real.sqrt (2 * zeta) * marginalRootBudget k /
      ((k - params.d : ℕ) : Error) ≤ K ^ (2 : ℕ) * e := by
    have hbudget0 : 0 ≤ marginalRootBudget k /
        ((k - params.d : ℕ) : Error) := by
      have hden : 0 ≤ ((k - params.d : ℕ) : Error) := by positivity
      have hnum : 0 ≤ marginalRootBudget k := by
        unfold marginalRootBudget
        positivity
      exact div_nonneg hnum hden
    calc
      Real.sqrt (2 * zeta) * marginalRootBudget k /
          ((k - params.d : ℕ) : Error) =
          Real.sqrt (2 * zeta) *
            (marginalRootBudget k / ((k - params.d : ℕ) : Error)) := by ring
      _ ≤ 2 * e * (K ^ (2 : ℕ) / 2) := by
        exact mul_le_mul hsqrt2ζ hbudget hbudget0 (by positivity)
      _ = K ^ (2 : ℕ) * e := by ring
  have hdinv : (1 : Error) / (params.q : Error) ≤
      (params.d : Error) / (params.q : Error) := by
    have hd1 : (1 : Error) ≤ (params.d : Error) := by
      exact_mod_cast hd
    exact (div_le_div_iff₀ hq hq).2 (by nlinarith)
  have hcollision : K ^ (2 : ℕ) / (params.q : Error) ≤ K ^ (2 : ℕ) * r := by
    calc
      K ^ (2 : ℕ) / (params.q : Error) =
          K ^ (2 : ℕ) * ((1 : Error) / (params.q : Error)) := by ring
      _ ≤ K ^ (2 : ℕ) * r := by
        exact mul_le_mul_of_nonneg_left (hdinv.trans hratio) (sq_nonneg K)
  have halgebra := pasting_error_algebra K R a b c e r
    hK hR ha hb hc he hr
  have htermζ : 2 * K * zeta ≤ 2 * K * e := by
    exact mul_le_mul_of_nonneg_left hζ (by positivity)
  have htermAxis : (2 * K + 1) *
      Real.sqrt (8 * (params.m : Error) * eps + 4 * delta) ≤
      (2 * K + 1) * (4 * R * (a + b)) := by
    exact mul_le_mul_of_nonneg_left haxis (by positivity)
  have htermCom : 2 * K * (K - 1) *
      (Real.sqrt (Commutativity.comMainError params gamma zeta) +
        4 * Real.sqrt zeta) ≤
      2 * K * (K - 1) * ((11 / 2 : Error) * R * (c + e + r) + 4 * e) := by
    have hinside :
        Real.sqrt (Commutativity.comMainError params gamma zeta) +
            4 * Real.sqrt zeta ≤
          (11 / 2 : Error) * R * (c + e + r) + 4 * e := by
      have hcom' : Real.sqrt (Commutativity.comMainError params gamma zeta) ≤
          (11 / 2 : Error) * R * (c + e + r) := hcom
      have hrootζ' : Real.sqrt zeta ≤ e := hrootζ
      linarith
    exact mul_le_mul_of_nonneg_left hinside (by positivity)
  calc
    distinctSuccessPastingError params k eps delta gamma kappa zeta =
        K / ((k - params.d : ℕ) : Error) * kappa +
          (2 * K * zeta +
            (2 * K + 1) * Real.sqrt (8 * (params.m : Error) * eps + 4 * delta) +
            2 * K * (K - 1) *
              (Real.sqrt (Commutativity.comMainError params gamma zeta) +
                4 * Real.sqrt zeta) +
            Real.sqrt (2 * zeta) * marginalRootBudget k /
              ((k - params.d : ℕ) : Error) +
            K ^ (2 : ℕ) / (params.q : Error)) := by
      unfold distinctSuccessPastingError
      ring
    _ ≤ K / ((k - params.d : ℕ) : Error) * kappa +
        (2 * K * e + (2 * K + 1) * (4 * R * (a + b)) +
          2 * K * (K - 1) *
            ((11 / 2 : Error) * R * (c + e + r) + 4 * e) +
          K ^ (2 : ℕ) * e + K ^ (2 : ℕ) * r) := by
      linarith [htermζ, htermAxis, htermCom, hmass, hcollision]
    _ ≤ K / ((k - params.d : ℕ) : Error) * kappa +
        21 * K ^ (2 : ℕ) * R * (a + b + c + e + r) := by
      linarith [halgebra]
    _ = _ := by rfl

/-- The quantitative consistency parameter stated in simplified pasting. -/
noncomputable def simplifiedPastingPaperError
    (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error) : Error :=
  (k : Error) / ((k - params.d : ℕ) : Error) * kappa +
    21 * (k : Error) ^ (2 : ℕ) * Real.sqrt (params.m : Error) *
      pastingEighthSum params eps delta gamma zeta

/-- Quantitative simplified pasting in the unit error regime. The
measurement is constructed by the first-success word and then completed
at a fixed polynomial. -/
theorem distinctSuccessPastedMeasurement_pointConsistency_paperBound_small
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hd : 0 < params.d) (hdq : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) (hdk : params.d < k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedMeasurement params family k).toSubMeas)
      (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  have hraw := distinctSuccessPastedMeasurement_pointConsistency_ofPaperHypotheses
    params strategy family eps delta gamma kappa zeta
    hgood hgamma0 hgamma1 hzeta0 hzeta1 hdq
    hcomplete hcons hself hbound k hdk
  have hscalar := distinctSuccessPastingError_le_paperBound
    params k eps delta gamma kappa zeta
    hd hdk hdq heps0 heps1 hdelta0 hdelta1 hgamma0 hzeta0 hzeta1
  exact ConsRel.mono (by simpa [simplifiedPastingPaperError] using hscalar) hraw

/-- The error parameter of pasting in the simplified induction step. -/
noncomputable def simplifiedInductionPaperError
    (params : Parameters) (eps delta gamma kappa zeta : Error) : Error :=
  ((params.m + 1 : ℕ) : Error) / (params.m : Error) * kappa +
    21 * (((params.m + 1 : ℕ) : Error) ^ (2 : ℕ)) *
      ((params.d : Error) ^ (2 : ℕ)) * Real.sqrt (params.m : Error) *
        pastingEighthSum params eps delta gamma zeta

/-- The internal attempt count gives the induction theorem's exact
displayed consistency parameter. -/
theorem simplifiedPastingPaperError_induction_eq
    (params : Parameters) (eps delta gamma kappa zeta : Error)
    (hd : 0 < params.d) :
    simplifiedPastingPaperError params (simplifiedInductionAttemptCount params)
        eps delta gamma kappa zeta =
      simplifiedInductionPaperError params eps delta gamma kappa zeta := by
  have hsub : simplifiedInductionAttemptCount params - params.d =
      params.m * params.d := by
    unfold simplifiedInductionAttemptCount
    rw [Nat.add_mul]
    simp only [one_mul]
    omega
  have hm : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
  have hdreal : (0 : Error) < (params.d : Error) := by exact_mod_cast hd
  unfold simplifiedPastingPaperError simplifiedInductionPaperError
  rw [hsub]
  simp only [simplifiedInductionAttemptCount]
  push_cast
  have hmd : (params.m : Error) * (params.d : Error) ≠ 0 :=
    mul_ne_zero (ne_of_gt hm) (ne_of_gt hdreal)
  have hratio :
      (((params.m : Error) + 1) * (params.d : Error)) /
          ((params.m : Error) * (params.d : Error)) =
        ((params.m : Error) + 1) / (params.m : Error) := by
    field_simp
  rw [hratio]
  ring

/-- Positive-degree simplified pasting with no externally supplied
attempt count and the induction section's stated error formula. -/
theorem distinctSuccessPastedMeasurement_induction_paperBound_small
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hd : 0 < params.d) (hdq : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedMeasurement params family
          (simplifiedInductionAttemptCount params)).toSubMeas)
      (simplifiedInductionPaperError params eps delta gamma kappa zeta) := by
  have hdk : params.d < simplifiedInductionAttemptCount params := by
    unfold simplifiedInductionAttemptCount
    have hm := params.hm
    have hm2 : 2 ≤ params.m + 1 := by omega
    have htwo : params.d < 2 * params.d := by omega
    exact htwo.trans_le (Nat.mul_le_mul_right params.d hm2)
  have h := distinctSuccessPastedMeasurement_pointConsistency_paperBound_small
    params strategy family eps delta gamma kappa zeta
    hgood heps0 heps1 hdelta0 hdelta1 hgamma0 hgamma1 hzeta0 hzeta1
    hd hdq hcomplete hcons hself hbound
    (simplifiedInductionAttemptCount params) hdk
  simpa [simplifiedPastingPaperError_induction_eq params eps delta gamma kappa zeta hd]
    using h

/-- A saturated eighth-power summand makes the paper's pasting error
at least one. -/
theorem one_le_simplifiedPastingPaperError_of_large_sum
    (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error)
    (hdk : params.d < k) (hkappa : 0 ≤ kappa)
    (hsum : 1 ≤ pastingEighthSum params eps delta gamma zeta) :
    1 ≤ simplifiedPastingPaperError params k eps delta gamma kappa zeta := by
  have hK_nat : 1 ≤ k := by omega
  have hK : (1 : Error) ≤ (k : Error) := by exact_mod_cast hK_nat
  have hden_nat : 1 ≤ k - params.d := by omega
  have hden : (0 : Error) < ((k - params.d : ℕ) : Error) := by
    exact_mod_cast (show 0 < k - params.d by omega)
  have hm : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hroot : (1 : Error) ≤ Real.sqrt (params.m : Error) := by
    have hroot0 := Real.sqrt_nonneg (params.m : Error)
    have hroot2 := Real.sq_sqrt (show 0 ≤ (params.m : Error) by linarith)
    nlinarith
  have hK0 : 0 ≤ (k : Error) := by positivity
  have hbase : 0 ≤ (k : Error) / ((k - params.d : ℕ) : Error) * kappa := by
    exact mul_nonneg (div_nonneg hK0 (le_of_lt hden)) hkappa
  have hcoef : (1 : Error) ≤
      21 * (k : Error) ^ (2 : ℕ) * Real.sqrt (params.m : Error) := by
    have hksq : (1 : Error) ≤ (k : Error) ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (sq_nonneg (k : Error))]
  have hterm : (1 : Error) ≤
      21 * (k : Error) ^ (2 : ℕ) * Real.sqrt (params.m : Error) *
        pastingEighthSum params eps delta gamma zeta := by
    have hcoef0 : 0 ≤
        21 * (k : Error) ^ (2 : ℕ) * Real.sqrt (params.m : Error) := by
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum) hcoef0]
  unfold simplifiedPastingPaperError
  linarith

/-- Any of the five eighth-power terms can saturate the pasting
bound. -/
theorem one_le_pastingEighthSum_of_component
    (params : Parameters) (eps delta gamma zeta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hgamma : 0 ≤ gamma) (hzeta : 0 ≤ zeta)
    (hcomponent :
      1 ≤ Real.rpow eps (1 / (8 : Error)) ∨
      1 ≤ Real.rpow delta (1 / (8 : Error)) ∨
      1 ≤ Real.rpow gamma (1 / (8 : Error)) ∨
      1 ≤ Real.rpow zeta (1 / (8 : Error)) ∨
      1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (8 : Error))) :
    1 ≤ pastingEighthSum params eps delta gamma zeta := by
  have hq : 0 ≤ (params.d : Error) / (params.q : Error) := by positivity
  have h₁ := Real.rpow_nonneg heps (1 / (8 : Error))
  have h₂ := Real.rpow_nonneg hdelta (1 / (8 : Error))
  have h₃ := Real.rpow_nonneg hgamma (1 / (8 : Error))
  have h₄ := Real.rpow_nonneg hzeta (1 / (8 : Error))
  have h₅ := Real.rpow_nonneg hq (1 / (8 : Error))
  change 0 ≤ Real.rpow eps (1 / (8 : Error)) at h₁
  change 0 ≤ Real.rpow delta (1 / (8 : Error)) at h₂
  change 0 ≤ Real.rpow gamma (1 / (8 : Error)) at h₃
  change 0 ≤ Real.rpow zeta (1 / (8 : Error)) at h₄
  change 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
    (1 / (8 : Error)) at h₅
  unfold pastingEighthSum
  rcases hcomponent with h | h | h | h | h <;> linarith

/-- Positive-degree simplified pasting, with the large error cases
closed by a fixed polynomial measurement. -/
theorem exists_simplifiedPastedMeasurement_positiveDegree
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hd : 0 < params.d) (k : ℕ) (hdk : params.d < k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  have heps0 := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta0 := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma0 := gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta0 := IdxPolyFamily.zeta_nonneg_of_consistentWithPoints
    strategy family hcons
  have hkappa0 := kappa_nonneg_of_complete params strategy family hcomplete
  by_cases hregime : eps ≤ 1 ∧ delta ≤ 1 ∧ gamma ≤ 1 ∧
      zeta ≤ 1 ∧ params.d ≤ params.q
  · rcases hregime with ⟨heps1, hdelta1, hgamma1, hzeta1, hdq⟩
    let H := distinctSuccessPastedMeasurement params family k
    refine ⟨H, ?_⟩
    exact distinctSuccessPastedMeasurement_pointConsistency_paperBound_small
      params strategy family eps delta gamma kappa zeta
      hgood heps0 heps1 hdelta0 hdelta1 hgamma0 hgamma1 hzeta0 hzeta1
      hd hdq hcomplete hcons hself hbound k hdk
  · have hbad : 1 < eps ∨ 1 < delta ∨ 1 < gamma ∨
        1 < zeta ∨ params.q < params.d := by
      by_contra h
      push Not at h
      exact hregime ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    have hcomponent :
        1 ≤ Real.rpow eps (1 / (8 : Error)) ∨
        1 ≤ Real.rpow delta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow gamma (1 / (8 : Error)) ∨
        1 ≤ Real.rpow zeta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8 : Error)) := by
      rcases hbad with h | h | h | h | h
      · exact Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num)))
      · exact Or.inr (Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num))))
      · exact Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num))))))
      · have hq : (0 : Error) < (params.q : Error) := by exact_mod_cast params.hq
        have hratio : (1 : Error) <
            (params.d : Error) / (params.q : Error) := by
          apply (lt_div_iff₀ hq).2
          have hcast : (params.q : Error) < (params.d : Error) := by
            exact_mod_cast h
          simpa using hcast
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (le_of_lt (Real.one_lt_rpow hratio (by norm_num))))))
    have hsum := one_le_pastingEighthSum_of_component
      params eps delta gamma zeta heps0 hdelta0 hgamma0 hzeta0 hcomponent
    have herror := one_le_simplifiedPastingPaperError_of_large_sum
      params k eps delta gamma kappa zeta hdk hkappa0 hsum
    let H : Measurement (Polynomial params.next) ι :=
      Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
    refine ⟨H, ?_⟩
    exact ⟨le_trans
      (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)) herror⟩

/-- Simplified Section 6 pasting with its internal attempt count and
the displayed induction error parameter. -/
theorem exists_simplifiedPastedMeasurement_induction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hd : 0 < params.d) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedInductionPaperError params eps delta gamma kappa zeta) := by
  have hdk : params.d < simplifiedInductionAttemptCount params := by
    unfold simplifiedInductionAttemptCount
    have hm := params.hm
    have hm2 : 2 ≤ params.m + 1 := by omega
    have htwo : params.d < 2 * params.d := by omega
    exact htwo.trans_le (Nat.mul_le_mul_right params.d hm2)
  obtain ⟨H, hH⟩ := exists_simplifiedPastedMeasurement_positiveDegree
    params strategy family eps delta gamma kappa zeta
    hgood hcomplete hcons hself hbound hd
    (simplifiedInductionAttemptCount params) hdk
  exact ⟨H, by
    simpa [simplifiedPastingPaperError_induction_eq
      params eps delta gamma kappa zeta hd] using hH⟩

end MIPStarRE.LDT.Pasting
