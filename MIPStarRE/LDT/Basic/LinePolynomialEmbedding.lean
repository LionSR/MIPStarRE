import MIPStarRE.LDT.Basic.LowDegreePolynomial

/-!
# Axis-line to global polynomial lifts

Utility lemmas for substituting a univariate axis-line polynomial into a chosen
ambient coordinate.
-/

namespace MIPStarRE.LDT

/-- Substituting a univariate polynomial into one multivariate variable preserves its
degree bound in that variable and gives degree zero in all other variables. -/
theorem degreeOf_eval₂_C_X_le_natDegree {K σ : Type*} [Field K] [DecidableEq σ]
    (p : _root_.Polynomial K) (i j : σ) :
    MvPolynomial.degreeOf i
      (p.eval₂ MvPolynomial.C (MvPolynomial.X j) : MvPolynomial σ K) ≤
        if i = j then p.natDegree else 0 := by
  rw [_root_.Polynomial.eval₂_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le i (Finset.range (p.natDegree + 1)) _).trans ?_
  refine Finset.sup_le fun n hn => ?_
  calc
    MvPolynomial.degreeOf i
        (MvPolynomial.C (p.coeff n) * MvPolynomial.X j ^ n : MvPolynomial σ K)
        ≤ MvPolynomial.degreeOf i (MvPolynomial.X j ^ n : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_C_mul_le _ _ _
    _ ≤ n * MvPolynomial.degreeOf i (MvPolynomial.X j : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_pow_le _ _ _
    _ ≤ if i = j then p.natDegree else 0 := by
          by_cases hij : i = j
          · have hn_le : n ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            simp [hij, hn_le]
          · simp [hij, MvPolynomial.degreeOf_X]

/-- Extend an axis-line answer to a global polynomial by substituting the ambient
coordinate `X i` for the formal line parameter. Away from direction `i`, the result
is constant, so in the `m = 1` base case this identifies the unique axis-parallel
line polynomial with an ambient low-degree polynomial. -/
noncomputable def axisLinePolynomialToPolynomial
    (params : Parameters) [FieldModel params.q]
    (i : Fin params.m) (f : AxisLinePolynomial params) : Polynomial params where
  poly := f.poly.eval₂ MvPolynomial.C (MvPolynomial.X i)
  lowIndividualDegree := by
    intro j
    calc
      MvPolynomial.degreeOf j
          (f.poly.eval₂ MvPolynomial.C (MvPolynomial.X i) : PolynomialModel params)
        ≤ if j = i then f.poly.natDegree else 0 :=
          degreeOf_eval₂_C_X_le_natDegree f.poly j i
      _ ≤ params.d := by
        by_cases hji : j = i
        · simp [hji, f.degreeBounded]
        · simp [hji]

/-- Evaluating the lifted polynomial at a point `u` recovers the original line
polynomial at the `i`th coordinate `u i`. -/
@[simp] theorem axisLinePolynomialToPolynomial_apply
    (params : Parameters) [FieldModel params.q]
    (i : Fin params.m) (f : AxisLinePolynomial params) (u : Point params) :
    axisLinePolynomialToPolynomial params i f u = f (u i) := by
  unfold axisLinePolynomialToPolynomial Polynomial.toFun AxisLinePolynomial.toFun
    evalPolynomialModel evalLinePolynomialModel
  rw [show
      MvPolynomial.eval (decodePoint u)
          (f.poly.eval₂ MvPolynomial.C (MvPolynomial.X i) : PolynomialModel params) =
        f.poly.eval₂
          ((MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C)
          (MvPolynomial.eval (decodePoint u) (MvPolynomial.X i)) by
    simpa using
      (_root_.Polynomial.hom_eval₂ (p := f.poly)
        (f := MvPolynomial.C) (g := MvPolynomial.eval (decodePoint u))
        (x := MvPolynomial.X i))]
  have hcomp :
      ((MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C) =
        RingHom.id (Scalar params) := by
    ext a
    simp
  rw [hcomp]
  simp [decodePoint]

end MIPStarRE.LDT
