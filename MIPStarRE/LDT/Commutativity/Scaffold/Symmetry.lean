import MIPStarRE.LDT.Commutativity.Scaffold.Core

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-! ## Scaffold theorem statements -/

/-- Coordinatewise transport between coded `F_q` points and the underlying scalar model. -/
private def pointScalarEquiv (params : Parameters) [FieldModel params.q] :
    Point params ≃ (Fin params.m → Scalar params) where
  toFun := decodePoint
  invFun := fun u i => encodeScalar (u i)
  left_inv := by
    intro u
    funext i
    simp [decodePoint, encode_decodeScalar]
  right_inv := by
    intro u
    funext i
    simp [decodePoint, decode_encodeScalar]

/-- Reindex evaluation equality from coded `Point params` points to the scalar
function space used by `schwartzZippel_individualDegree`. -/
private lemma fullPolynomial_agreement_avg_eq_scalarDomain
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) =
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) := by
  let e := pointScalarEquiv params
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u => if g (e.symm u) = g' (e.symm u) then (1 : Error) else 0) := by
            simpa [e] using
              (avgOver_uniform_equiv e
                (fun u : Point params => if g u = g' u then (1 : Error) else 0))
    _ = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) := by
            apply avgOver_congr
            intro u
            have hdecode : decodePoint (e.symm u) = u := by
              simpa [e, pointScalarEquiv] using e.right_inv u
            by_cases hEval : MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly
            · have hPointEval : g (e.symm u) = g' (e.symm u) := by
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly)
                congr 1
                simpa [hdecode] using hEval
              simp [hEval, hPointEval]
            · have hPointEval : ¬ g (e.symm u) = g' (e.symm u) := by
                intro hEq
                apply hEval
                apply (FieldModel.equiv (q := params.q)).injective
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly) at hEq
                simpa [encodeScalar, hdecode] using hEq
              simp [hEval, hPointEval]

/-- Schwartz-Zippel bound for the pointwise agreement indicator of two distinct
full polynomial outcomes. This packages the `dm / q` loss from the first
evaluated-at-points marginalization in the commutativity proof. -/
private lemma fullPolynomial_agreement_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let gLow : MIPStarRE.LDT.Preliminaries.polyFunc params.m (Scalar params) params.d :=
    ⟨g.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩
  let g'Low : MIPStarRE.LDT.Preliminaries.polyFunc params.m (Scalar params) params.d :=
    ⟨g'.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g'.lowIndividualDegree⟩
  have hneqLow : gLow ≠ g'Low := by
    intro hEq
    have hpoly : g.poly = g'.poly := congrArg Subtype.val hEq
    apply hneq
    cases g
    cases g'
    cases hpoly
    rfl
  have hsz :=
    MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree gLow g'Low hneqLow
  have havg_scalar :
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) =
      (MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability
        params.m (Scalar params) g.poly g'.poly : Error) := by
    calc
      avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0)
        = ∑ u : Fin params.m → Scalar params,
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (Fintype.card (Scalar params) ^ params.m : Error)⁻¹
            else 0 := by
              simp [avgOver, uniformDistribution]
      _ = Finset.sum
            ((Finset.univ : Finset (Fin params.m → Scalar params)).filter
              (fun u => MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly))
            (fun _ => (Fintype.card (Scalar params) ^ params.m : Error)⁻¹) := by
              rw [← Finset.sum_filter]
      _ = (((Finset.univ.filter fun u : Fin params.m → Scalar params =>
              MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly).card : ℕ) : Error) *
            (Fintype.card (Scalar params) ^ params.m : Error)⁻¹ := by
              simp
      _ = (MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability
            params.m (Scalar params) g.poly g'.poly : Error) := by
              simp [MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability,
                div_eq_mul_inv]
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) :=
            fullPolynomial_agreement_avg_eq_scalarDomain params g g'
    _ = (MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability
          params.m (Scalar params) g.poly g'.poly : Error) :=
          havg_scalar
    _ ≤ ((((params.m * params.d : ℕ) : ℚ≥0) / Fintype.card (Scalar params)) : Error) := by
          exact_mod_cast hsz
    _ = (params.m * params.d : Error) / params.q := by
          simp [scalar_card, div_eq_mul_inv]

/-- Package the point-consistency field using the local evaluated-point-family
notation. -/
private lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta := by
  simpa [evaluatedPointFamily] using hcons.pointConsistency

private lemma qMatchMass_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qMatchMass ψ A B = qMatchMass ψ B A := by
  unfold qMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)

private lemma qConsDefect_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qConsDefect ψ A B = qConsDefect ψ B A := by
  simp [qConsDefect, qMatchMass_symm,
    ev_mul_comm_of_psd ψ _ _ A.total_nonneg B.total_nonneg]

omit [Fintype ι] [DecidableEq ι] in
private lemma swapDensity_eq_reindex
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

private lemma normalizedTrace_reindex
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (X : MIPStarRE.Quantum.Op α) :
    MIPStarRE.Quantum.normalizedTrace (Matrix.reindex e e X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e.symm
  unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => X i i)]
  simp [hcard]

private lemma swapDensity_mul
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  simpa [swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

private lemma normalizedTrace_swapDensity
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace (swapDensity X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  simpa [swapDensity_eq_reindex] using
    normalizedTrace_reindex (Equiv.prodComm ι ι) X

private lemma swapDensity_opTensor
    (X Y : MIPStarRE.Quantum.Op ι) :
    swapDensity (opTensor X Y) = opTensor Y X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [swapDensity, opTensor, mul_comm]

private lemma ev_swapDensity_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

private lemma ev_opTensor_swap_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

private lemma qBipartiteMatchMass_symm_of_density_fixed
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

private lemma qBipartiteConsDefect_symm_of_density_fixed
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect, qBipartiteMatchMass_symm_of_density_fixed,
    ev_opTensor_swap_of_density_fixed, hfix]

private lemma consRel_symm_of_density_fixed
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

private lemma evaluatedPointFamily_pointConsistency_swapped_of_density_fixed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hfix : swapDensity strategy.state.density = strategy.state.density)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
  exact consRel_symm_of_density_fixed
    strategy.state hfix
    (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (evaluatedPointFamily params family)
    zeta
    (by simpa [evaluatedPointFamily] using hcons.pointConsistency)


end MIPStarRE.LDT.Commutativity
