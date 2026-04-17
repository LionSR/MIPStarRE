import MIPStarRE.LDT.Basic.LowDegreePolynomial

/-!
# Finite answer spaces for the low individual degree test

Finite-type instances for the bounded polynomial answer spaces defined in
`MIPStarRE.LDT.Basic.LowDegreePolynomial`.
-/

namespace MIPStarRE.LDT

/-! ### Finite answer spaces -/

/-- Axis-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (AxisLinePolynomial params) := by
  classical
  let e :
      AxisLinePolynomial params ≃
        {p : LinePolynomialModel params // p.natDegree ≤ params.d} := {
    toFun := fun f => ⟨f.poly, f.degreeBounded⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl
  }
  let e' : {p : LinePolynomialModel params // p.natDegree ≤ params.d} ≃
      (Fin (params.d + 1) → Scalar params) := {
    toFun := fun p =>
      Polynomial.degreeLTEquiv (Scalar params) (params.d + 1) ⟨p.1, by
        rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
          ← Polynomial.natDegree_le_iff_degree_le]
        exact p.2⟩
    invFun := fun f =>
      let p : Polynomial.degreeLT (Scalar params) (params.d + 1) :=
        (Polynomial.degreeLTEquiv (Scalar params) (params.d + 1)).symm f
      ⟨(p : LinePolynomialModel params), by
        have hf : (p : LinePolynomialModel params) ∈
            Polynomial.degreeLT (Scalar params) (params.d + 1) :=
          p.2
        have hf' :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLE (Scalar params) params.d := by
          simpa [Polynomial.degreeLT_succ_eq_degreeLE] using hf
        exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hf')⟩
    left_inv := by
      intro p
      simp
    right_inv := by
      intro f
      simp
  }
  exact Fintype.ofEquiv _ (e.trans e').symm

/-- Diagonal-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (DiagonalLinePolynomial params) := by
  classical
  let e :
      DiagonalLinePolynomial params ≃
        {p : LinePolynomialModel params // p.natDegree ≤ params.m * params.d} := {
    toFun := fun f => ⟨f.poly, f.degreeBounded⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl
  }
  let e' : {p : LinePolynomialModel params // p.natDegree ≤ params.m * params.d} ≃
      (Fin (params.m * params.d + 1) → Scalar params) := {
    toFun := fun p =>
      Polynomial.degreeLTEquiv (Scalar params) (params.m * params.d + 1) ⟨p.1, by
        rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
          ← Polynomial.natDegree_le_iff_degree_le]
        exact p.2⟩
    invFun := fun f =>
      let p : Polynomial.degreeLT (Scalar params) (params.m * params.d + 1) :=
        (Polynomial.degreeLTEquiv (Scalar params) (params.m * params.d + 1)).symm f
      ⟨(p : LinePolynomialModel params), by
        have hf :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLT (Scalar params) (params.m * params.d + 1) := p.2
        have hf' :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLE (Scalar params) (params.m * params.d) := by
          simpa [Polynomial.degreeLT_succ_eq_degreeLE] using hf
        exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hf')⟩
    left_inv := by
      intro p
      simp
    right_inv := by
      intro f
      simp
  }
  exact Fintype.ofEquiv _ (e.trans e').symm

/-- Global low-individual-degree polynomial answers form a finite type. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (Polynomial params) := by
  classical
  let e :
      Polynomial params ≃
        MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d := {
    toFun := fun g => ⟨g.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩
    invFun := fun g => ⟨g.1, by
      have hg := (MvPolynomial.mem_restrictDegree_iff_sup
        (σ := Fin params.m) (R := Scalar params) (p := g.1) (n := params.d)).mp g.2
      simpa [MvPolynomial.degreeOf_def] using hg⟩
    left_inv := by intro g; cases g; rfl
    right_inv := by intro g; cases g; rfl
  }
  let _ : Finite (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Module.finite_of_finite (Scalar params)
  /-
  `Fintype.ofFinite` keeps this instance definition short. If typeclass search
  here ever becomes a bottleneck, replace it with an explicit coefficient-vector
  enumeration as in the one-variable polynomial instances above.
  -/
  letI : Fintype (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _ e.symm

end MIPStarRE.LDT
