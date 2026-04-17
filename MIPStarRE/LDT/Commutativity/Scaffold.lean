import MIPStarRE.LDT.Commutativity.Defs
import MIPStarRE.LDT.CommutativityPoints.Theorem
import MIPStarRE.LDT.Preliminaries.Polynomials
import MIPStarRE.LDT.Preliminaries.SelfConsistency
import MIPStarRE.LDT.Test.Strategy

/-!
# Section 11 commutativity: scaffold and setup

Error terms, packaged inputs, and the early commutativity scaffold extracted from
`MIPStarRE.LDT.Commutativity.Theorems`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Error terms and packaged conclusions -/

/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : MIPStarRE.Quantum.Op ι) : Prop :=
  X ≤ Y

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Output package for `lem:comm-data-processed-g`.

The strategy state is bipartite.  Alice-side measurements are lifted to
the left tensor factor, while Bob-side postprocessed point measurements
are lifted to the right tensor factor.

The parameter `G` is the slice-indexed family `x ↦ G^x`; the hypothesis
`familyG` ties it back to `family.meas` so that the stability weights
`√(G^y_h)` and `√(G^x_g)` agree with the family's projective
sub-measurements. -/
structure CommDataProcessedGConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  familyG : ∀ x, G x = (family.meas x).toSubMeas
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
  postprocessedSelfConsistency :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta
  evaluatedSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy family G gamma zeta
  evaluationSpecialization :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Explicit remaining input for the evaluated-slice commutation step in
`lem:comm-data-processed-g`. -/
abbrev CommDataProcessedGEvaluatedSliceInput (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) : Prop :=
  strategy.state.IsNormalized →
    strategy.IsGood eps delta gamma →
    family.StronglySelfConsistent strategy.state zeta →
    family.ConsistentWithPoints strategy zeta →
    IdxPolyFamily.SliceBoundednessInput strategy family zeta →
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta →
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Explicit remaining input for `clm:g-comm-stability`. -/
abbrev GCommStabilityInput (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (eps delta gamma zeta : Error) : Prop :=
  strategy.state.IsNormalized →
    strategy.IsGood eps delta gamma →
    family.ConsistentWithPoints strategy zeta →
    family.StronglySelfConsistent strategy.state zeta →
    IdxPolyFamily.SliceBoundednessInput strategy family zeta →
    (∀ x, G x = (family.meas x).toSubMeas) →
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta)

/-- Explicit remaining input for `clm:g-comm-stability2`. -/
abbrev GCommStabilityTwoInput (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (eps delta gamma zeta : Error) : Prop :=
  strategy.state.IsNormalized →
    strategy.IsGood eps delta gamma →
    family.ConsistentWithPoints strategy zeta →
    family.StronglySelfConsistent strategy.state zeta →
    IdxPolyFamily.SliceBoundednessInput strategy family zeta →
    (∀ x, G x = (family.meas x).toSubMeas) →
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)))

/-- Explicit remaining input for the Schwartz-Zippel transport from evaluated
slice commutation to full-slice commutation. -/
abbrev FullSliceCommutationEvaluatedInput (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop :=
  strategy.state.IsNormalized →
    0 ≤ gamma →
    0 ≤ zeta →
    family.StronglySelfConsistent strategy.state zeta →
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta) →
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) : Prop where
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  sandwichedBoundedByIdentity :
    OperatorDominatedBy
      (normalizationConditionSquareOperator P Q)
      (normalizationConditionIdentityBound P Q)

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

/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
private lemma projSubMeas_outcome_orthogonal
    {α : Type*} [Fintype α]
    (P : ProjSubMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hsum : Pa + Pb ≤ P.total := by
    calc
      Pa + Pb
        = ∑ i ∈ ({a, b} : Finset α), P.outcome i := by
            simp [Pa, Pb, hab]
      _ ≤ ∑ i : α, P.outcome i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by simp)
              (fun i _ _ => P.outcome_pos i)
      _ = P.total := P.sum_eq_total
  have hPb_le : Pb ≤ 1 - Pa := by
    calc
      Pb = Pa + Pb - Pa := by abel
      _ ≤ P.total - Pa := by
          exact sub_le_sub_right hsum Pa
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right P.total_le_one Pa
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    MIPStarRE.Quantum.sandwich_nonneg (P.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    calc
      Pa * (1 - Pa) * Pa = (Pa * 1 - Pa * Pa) * Pa := by rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * Pb * Pa ≤ Pa * (1 - Pa) * Pa :=
          MIPStarRE.Quantum.sandwich_mono hPa_herm hPb_le
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (Pb * Pa)ᴴ * (Pb * Pa) = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
        simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc
    Pa * Pb = (Pb * Pa)ᴴ := by
      simp [Matrix.conjTranspose_mul, hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
private lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  classical
  let s : Finset α := Finset.univ.filter fun a => f a = b
  calc
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b
      = (∑ a ∈ s, P.outcome a) * ∑ c ∈ s, P.outcome c := by
          simp [postprocess, s]
    _ = ∑ a ∈ s, P.outcome a * ∑ c ∈ s, P.outcome c := by
          rw [Finset.sum_mul]
    _ = ∑ a ∈ s, ∑ c ∈ s, P.outcome a * P.outcome c := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Matrix.mul_sum]
    _ = ∑ a ∈ s, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.sum_eq_single a]
          · simp [P.proj a]
          · intro c hc hca
            exact projSubMeas_outcome_orthogonal P a c (Ne.symm hca)
          · intro hnot
            exact (hnot ha).elim
    _ = (postprocess P.toSubMeas f).outcome b := by
          simp [postprocess, s]

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a := by
  simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt] using
    postprocess_proj_outcome (family.meas (pointHeight params u))
      (fun g => g (truncatePoint params u)) a

lemma sqrt_subMeas_outcome_mul_self
    {α : Type*} [Fintype α]
    (A : SubMeas α ι) (a : α) :
    CFC.sqrt (A.outcome a) * CFC.sqrt (A.outcome a) = A.outcome a := by
  simpa using CFC.sqrt_mul_sqrt_self (A.outcome a) (A.outcome_pos a)

/-- Fixed-question expansion of the first scalar-stability `qSDDOp` term.

This is the pointwise algebra behind the paper's `G^y` insertion/removal step:
the left-register defect is sandwiched by `1 - G^y`, while the right-register
weight is the projective outcome `G^y_h`. -/
lemma commDataProcessedGStabilityOne_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (commDataProcessedGStabilityOneLeft params strategy family G q)
      (commDataProcessedGStabilityOneRight params strategy family G q) =
      ∑ ah : StabilityOneOutcome params,
        (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.2)).total) *
              (((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                (evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2))) *
              (1 - (G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.2)).outcome ah.2))) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro ah _
  let S : MIPStarRE.Quantum.Op ι :=
    (evaluatedSliceSandwichRaw params strategy family q).outcome
      (ah.1, ah.2 (truncatePoint params q.2))
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.2)).total
  let W : MIPStarRE.Quantum.Op ι := CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)
  have hT :
      (fullSliceSecondFactor params family
        (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceSecondFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.2)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.2)).outcome ah.2 := by
    simpa [W] using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.2)) ah.2
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [W] using CFC.sqrt_nonneg ((G (pointHeight params q.2)).outcome ah.2)
      ).isHermitian.eq
  have hW_adj_mul : Wᴴ * W = (G (pointHeight params q.2)).outcome ah.2 := by
    simpa [hW_herm] using hW_sq
  calc
    ev strategy.state
        (((commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah -
            (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah)ᴴ *
          ((commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah -
            (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah))
      = ev strategy.state
          (((opTensor (S * T) W - opTensor S W)ᴴ) *
            (opTensor (S * T) W - opTensor S W)) := by
            have hleft :
                (leftPlacedSubMeas (ιB := ι)
                    (evaluatedSliceSandwichRaw params strategy family q)).outcome
                    (ah.1, ah.2 (truncatePoint params q.2)) *
                  leftTensor (ι₂ := ι) T *
                  rightTensor (ι₁ := ι) W =
                opTensor (S * T) W := by
              calc
                (leftPlacedSubMeas (ιB := ι)
                      (evaluatedSliceSandwichRaw params strategy family q)).outcome
                      (ah.1, ah.2 (truncatePoint params q.2)) *
                    leftTensor (ι₂ := ι) T *
                    rightTensor (ι₁ := ι) W
                  = leftTensor (ι₂ := ι) S *
                      leftTensor (ι₂ := ι) T *
                      rightTensor (ι₁ := ι) W := by
                        change
                          leftTensor (ι₂ := ι)
                              ((evaluatedSliceSandwichRaw params strategy family q).outcome
                                (ah.1, ah.2 (truncatePoint params q.2))) *
                            leftTensor (ι₂ := ι) T *
                            rightTensor (ι₁ := ι) W =
                              leftTensor (ι₂ := ι) S *
                                leftTensor (ι₂ := ι) T *
                                rightTensor (ι₁ := ι) W
                        simp [S]
                _ = leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) W := by
                      rw [leftTensor_mul_leftTensor]
                _ = opTensor (S * T) W := by
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
            have hright :
                leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) W =
                  opTensor S W := by
              simp [S, W, leftTensor_mul_rightTensor_eq_opTensor]
            rw [commDataProcessedGStabilityOneLeft_outcome,
              commDataProcessedGStabilityOneRight_outcome]
            rw [hT, hleft, hright]
    _ = ev strategy.state
          (((opTensor (S * (T - 1)) W)ᴴ) * opTensor (S * (T - 1)) W) := by
            have hsub : S * T - S = S * (T - 1) := by
              calc
                S * T - S = S * T - S * 1 := by simp
                _ = S * (T - 1) := by rw [mul_sub]
            rw [opTensor_sub_left]
            rw [hsub]
    _ = ev strategy.state
          (opTensor (((S * (T - 1))ᴴ) * (S * (T - 1))) (Wᴴ * W)) := by
            simp [conjTranspose_opTensor, opTensor_mul]
    _ = ev strategy.state
          (opTensor
            ((1 - T) * (Sᴴ * S) * (1 - T))
            ((G (pointHeight params q.2)).outcome ah.2)) := by
            have hleft :
                ((S * (T - 1))ᴴ) * (S * (T - 1)) =
                  (1 - T) * (Sᴴ * S) * (1 - T) := by
              calc
                ((S * (T - 1))ᴴ) * (S * (T - 1))
                  = ((T - 1)ᴴ * Sᴴ) * (S * (T - 1)) := by
                      simp [Matrix.conjTranspose_mul]
                _ = ((T - 1) * Sᴴ) * (S * (T - 1)) := by
                      simp [hT_herm]
                _ = (-(1 - T) * Sᴴ) * (S * (-(1 - T))) := by
                      simp
                _ = (1 - T) * (Sᴴ * S) * (1 - T) := by
                      noncomm_ring
            rw [hW_adj_mul]
            rw [hleft]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι)
            ((1 - T) * (Sᴴ * S) * (1 - T)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)) := by
            rw [ev_opTensor]
    _ = (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.2)).total) *
              (((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                (evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2))) *
              (1 - (G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.2)).outcome ah.2))) := by
            simp [S, T]

/-- For a projective submeasurement on a permutation-invariant bipartite state,
the bipartite SSC defect is exactly half of the left/right SDD defect. -/
lemma commDataProcessedGStabilityTwo_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (commDataProcessedGStabilityTwoLeft params strategy family G q)
      (commDataProcessedGStabilityTwoRight params strategy family G q) =
      ∑ gb : StabilityTwoOutcome params,
        (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.1)).total) *
              (((orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                (orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.1)).outcome gb.1))) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gb _
  let S : MIPStarRE.Quantum.Op ι :=
    (orderedProductOpFamily
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)).outcome
      (gb.1 (truncatePoint params q.1), gb.2)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let W : MIPStarRE.Quantum.Op ι := CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)
  have hT :
      (fullSliceFirstFactor params family
        (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceFirstFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.1)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.1)).outcome gb.1 := by
    simpa [W] using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.1)) gb.1
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [W] using CFC.sqrt_nonneg ((G (pointHeight params q.1)).outcome gb.1)
      ).isHermitian.eq
  have hW_adj_mul : Wᴴ * W = (G (pointHeight params q.1)).outcome gb.1 := by
    simpa [hW_herm] using hW_sq
  calc
    ev strategy.state
        (((commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb -
            (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb)ᴴ *
          ((commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb -
            (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb))
      = ev strategy.state
          (((opTensor (S * T) W - opTensor S W)ᴴ) *
            (opTensor (S * T) W - opTensor S W)) := by
            rw [commDataProcessedGStabilityTwoLeft_outcome,
              commDataProcessedGStabilityTwoRight_outcome]
            rw [hT]
            simp [S, T, W, evaluatedSliceProductLeft, leftOrderedProductOpFamily,
              OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor,
              leftTensor_mul_rightTensor_eq_opTensor]
    _ = ev strategy.state
          (((opTensor (S * (T - 1)) W)ᴴ) * opTensor (S * (T - 1)) W) := by
            have hsub : S * T - S = S * (T - 1) := by
              calc
                S * T - S = S * T - S * 1 := by simp
                _ = S * (T - 1) := by rw [mul_sub]
            rw [opTensor_sub_left]
            rw [hsub]
    _ = ev strategy.state
          (opTensor (((S * (T - 1))ᴴ) * (S * (T - 1))) (Wᴴ * W)) := by
            simp [conjTranspose_opTensor, opTensor_mul]
    _ = ev strategy.state
          (opTensor
            ((1 - T) * (Sᴴ * S) * (1 - T))
            ((G (pointHeight params q.1)).outcome gb.1)) := by
            have hleft :
                ((S * (T - 1))ᴴ) * (S * (T - 1)) =
                  (1 - T) * (Sᴴ * S) * (1 - T) := by
              calc
                ((S * (T - 1))ᴴ) * (S * (T - 1))
                  = ((T - 1)ᴴ * Sᴴ) * (S * (T - 1)) := by
                      simp [Matrix.conjTranspose_mul]
                _ = ((T - 1) * Sᴴ) * (S * (T - 1)) := by
                      simp [hT_herm]
                _ = (-(1 - T) * Sᴴ) * (S * (-(1 - T))) := by
                      simp
                _ = (1 - T) * (Sᴴ * S) * (1 - T) := by
                      noncomm_ring
            rw [hW_adj_mul]
            rw [hleft]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι)
            ((1 - T) * (Sᴴ * S) * (1 - T)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) := by
            rw [ev_opTensor]
    _ = (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.1)).total) *
              (((orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                (orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.1)).outcome gb.1))) := by
            simp [S, T]

/-- The `BAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

/-- The first evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceFirstFactor params family q
      proj := by
        intro a
        simpa [evaluatedSliceFirstFactor] using
          evaluatedPointFamily_outcome_proj params family q.1 a }

/-- The second evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceSecondFactor params family q
      proj := by
        intro b
        simpa [evaluatedSliceSecondFactor] using
          evaluatedPointFamily_outcome_proj params family q.2 b }

/-- The first full-slice factor viewed as a projective family. -/
noncomputable def fullSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.1

/-- The second full-slice factor viewed as a projective family. -/
noncomputable def fullSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.2

/-- The `BAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)


end MIPStarRE.LDT.Commutativity
