import MIPStarRE.LDT.GlobalVariance.MatrixRealization

/-!
# Section 8 — Theorems

Output structures and theorem statements for the global variance lemmas.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for `lem:generalize-b`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Prop where
  aggregateFamilyComparison :
    SDDRel ψbi
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  pointwiseNormBound :
    ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params
  averagedNormBound :
    generalizeBDeviation params strategy ψbi G ≤ generalizeBError params

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  aggregateEdgeComparison :
    SDDRel ψbi
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  pointwiseEdgeNormBound :
    ∀ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        localVarianceOfPointsError params eps delta
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  aggregateGlobalComparison :
    SDDRel ψbi
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  pointwiseGlobalNormBound :
    ∀ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        globalVarianceOfPointsError params eps delta
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

private lemma avgOver_uniform_swap
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (𝒟 : Distribution Question) (f : Question → α → Error) :
    avgOver 𝒟 (fun q => avgOver (uniformDistribution α) (fun a => f q a)) =
      avgOver (uniformDistribution α) (fun a => avgOver 𝒟 (fun q => f q a)) := by
  unfold avgOver uniformDistribution
  calc
    ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : α, (1 / (Fintype.card α : Error)) * f q a
      = ∑ q ∈ 𝒟.support, ∑ a : α,
          (1 / (Fintype.card α : Error)) * (𝒟.weight q * f q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = ∑ a : α, ∑ q ∈ 𝒟.support,
          (1 / (Fintype.card α : Error)) * (𝒟.weight q * f q a) := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (1 / (Fintype.card α : Error)) *
          ∑ q ∈ 𝒟.support, 𝒟.weight q * f q a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]
    _ = avgOver (uniformDistribution α) (fun a => avgOver 𝒟 (fun q => f q a)) := by
          simp [avgOver, uniformDistribution]

private lemma ev_uniformAverage_sq_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (D : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
      ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
        averageOperatorOverDistribution (uniformDistribution α) D)
      ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
  let c : Error := 1 / (Fintype.card α : Error)
  let S : MIPStarRE.Quantum.Op ι :=
    averageOperatorOverDistribution (uniformDistribution α) D
  let x : α → Error := fun a => ev ψ ((D a)ᴴ * D a)
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hx_nonneg : ∀ a, 0 ≤ x a := by
    intro a
    exact ev_adjoint_self_nonneg ψ (D a)
  have hcard : (Fintype.card α : Error) ≠ 0 := by
    positivity
  have hsumc : ∑ a : α, c = 1 := by
    unfold c
    calc
      ∑ a : α, (1 / (Fintype.card α : Error))
          = (Fintype.card α : Error) * (1 / (Fintype.card α : Error)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            field_simp [hcard]
  have h_expand :
      ev ψ (Sᴴ * S)
        = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
    have hSsum : S = ∑ a : α, c • D a := by
      ext i j
      simp [S, c, averageOperatorOverDistribution, uniformDistribution]
    have hconj :
        (∑ a : α, c • D a)ᴴ = ∑ a : α, c • (D a)ᴴ := by
      simpa using
        (Matrix.conjTranspose_sum (s := Finset.univ)
          (M := fun a : α => c • D a))
    calc
      ev ψ (Sᴴ * S)
        = ev ψ (((∑ a : α, c • D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hSsum]
      _ = ev ψ ((∑ a : α, c • (D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hconj]
      _ = ev ψ (∑ b : α, ∑ a : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Matrix.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
      _ = ev ψ (∑ a : α, ∑ b : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Finset.sum_comm]
      _ = ∑ a : α, ∑ b : α, ev ψ ((c • (D a)ᴴ) * (c • D b)) := by
            rw [ev_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sum]
      _ = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [show ((c • (D a)ᴴ) * (c • D b)) =
                c • (c • ((D a)ᴴ * D b)) by
                  rw [smul_mul_assoc, mul_smul_comm]]
            rw [show c • (c • ((D a)ᴴ * D b)) =
                ((c : ℂ) • ((c : ℂ) • ((D a)ᴴ * D b))) by rfl]
            rw [ev_scale, ev_scale]
  have h_bound :
      ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b))
        ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := by
    refine Finset.sum_le_sum ?_
    intro a _
    refine Finset.sum_le_sum ?_
    intro b _
    have hab :
        ev ψ ((D a)ᴴ * D b) ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
      calc
        ev ψ ((D a)ᴴ * D b) ≤ |ev ψ ((D a)ᴴ * D b)| := le_abs_self _
        _ ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
              simpa [x] using ev_abs_mul_le_sqrt ψ ((D a)ᴴ) (D b)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hab hc_nonneg) hc_nonneg
  let s : Error := ∑ a : α, c * Real.sqrt (x a)
  have hs_square :
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) = s * s := by
    unfold s
    calc
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b)))
        = ∑ a : α, (c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
      _ = (∑ a : α, c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            rw [← Finset.sum_mul]
      _ = s * s := by
            rfl
  have hs_le :
      s ≤ Real.sqrt (avgOver (uniformDistribution α) x) := by
    have hs_raw :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c
          ≤ Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => c * x a) (g := fun _ => c)
              (fun a => mul_nonneg hc_nonneg (hx_nonneg a))
              (fun _ => hc_nonneg)
    have hs_lhs :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c = s := by
      unfold s
      refine Finset.sum_congr rfl ?_
      intro a _
      calc
        Real.sqrt (c * x a) * Real.sqrt c
          = Real.sqrt c * Real.sqrt (x a) * Real.sqrt c := by
              rw [Real.sqrt_mul hc_nonneg (x a)]
        _ = (Real.sqrt c * Real.sqrt c) * Real.sqrt (x a) := by
              ring
        _ = c * Real.sqrt (x a) := by
              rw [show Real.sqrt c * Real.sqrt c = c by
                nlinarith [Real.sq_sqrt hc_nonneg]]
    have hs_rhs :
        Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) =
          Real.sqrt (avgOver (uniformDistribution α) x) := by
      rw [hsumc, Real.sqrt_one, mul_one]
      simp [avgOver, uniformDistribution, c]
    rw [hs_lhs, hs_rhs] at hs_raw
    exact hs_raw
  have hs_nonneg : 0 ≤ s := by
    unfold s
    exact Finset.sum_nonneg fun a _ => mul_nonneg hc_nonneg (Real.sqrt_nonneg _)
  have havg_nonneg : 0 ≤ avgOver (uniformDistribution α) x := by
    exact avgOver_nonneg _ _ hx_nonneg
  calc
    ev ψ (Sᴴ * S)
      = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := h_expand
    _ ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := h_bound
    _ = s * s := hs_square
    _ ≤ avgOver (uniformDistribution α) x := by
          nlinarith [hs_nonneg, hs_le, Real.sq_sqrt havg_nonneg]

private lemma qSDD_unit_family_of_average_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (MA MB : SubMeas Unit ι)
    (A B : α → MIPStarRE.Quantum.Op ι)
    (hMA :
      MA.outcome () = averageOperatorOverDistribution (uniformDistribution α) A)
    (hMB :
      MB.outcome () = averageOperatorOverDistribution (uniformDistribution α) B) :
    qSDD ψ MA MB
      ≤ avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
  let D : α → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  have havg_sub :
      averageOperatorOverDistribution (uniformDistribution α) A -
          averageOperatorOverDistribution (uniformDistribution α) B =
        averageOperatorOverDistribution (uniformDistribution α) D := by
    simp [D, averageOperatorOverDistribution,
      uniformDistribution, Finset.sum_sub_distrib, smul_sub]
  calc
    qSDD ψ MA MB
      = ev ψ
          (((averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)ᴴ) *
            (averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)) := by
              unfold qSDD qSDDCore
              simp [hMA, hMB]
    _ = ev ψ
          ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
            averageOperatorOverDistribution (uniformDistribution α) D) := by
          rw [havg_sub]
    _ ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
          exact ev_uniformAverage_sq_le_avg ψ D
    _ = avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
          rfl

private lemma sddRel_unit_family_of_pointwise
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (MA MB : Question → SubMeas Unit ι)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (hMA :
      ∀ q, (MA q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => A q a))
    (hMB :
      ∀ q, (MB q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => B q a))
    (δ : Error)
    (hpoint :
      ∀ a, avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a))) ≤ δ) :
    SDDRel ψ 𝒟 MA MB δ := by
  refine ⟨?_⟩
  unfold sddError
  calc
    avgOver 𝒟 (fun q => qSDD ψ (MA q) (MB q))
      ≤ avgOver 𝒟
          (fun q =>
            avgOver (uniformDistribution α)
              (fun a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
              apply avgOver_mono
              intro q
              exact qSDD_unit_family_of_average_le_avg ψ
                (MA q) (MB q) (fun a => A q a) (fun a => B q a) (hMA q) (hMB q)
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
            exact avgOver_uniform_swap 𝒟
              (fun q a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))
    _ ≤ avgOver (uniformDistribution α) (fun _ => δ) := by
          apply avgOver_mono
          intro a
          exact hpoint a
    _ = δ := by
          simp [avgOver, uniformDistribution]

private lemma matrixGeneralizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (hpoint :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params) :
    MatrixGeneralizeBStatement params model := by
  refine
    { pointwiseDeviationBound := hpoint
      averagedDeviationBound := by
        unfold matrixGeneralizeBDeviation
        calc
          avgOver (polynomialDistribution params)
              (fun g => matrixGeneralizeBDeviationAtPolynomial params model g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => generalizeBError params) := by
                  apply avgOver_mono
                  intro g
                  exact hpoint g
          _ = generalizeBError params := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

private lemma matrixLocalVarianceOfPoints_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hpoint :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g ≤
          localVarianceOfPointsError params eps delta) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine
    { pointwiseLocalVarianceBound := hpoint
      averagedLocalVarianceBound := by
        unfold matrixPointConditionedLocalVariance
        calc
          avgOver (polynomialDistribution params)
              (fun g => matrixPointConditionedLocalVarianceAtPolynomial params model g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => localVarianceOfPointsError params eps delta) := by
                  apply avgOver_mono
                  intro g
                  exact hpoint g
          _ = localVarianceOfPointsError params eps delta := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

private lemma matrixGlobalVarianceOfPoints_from_local
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hlocal : MatrixLocalVarianceOfPointsStatement params model eps delta) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  have hexpansion :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          (params.m : Error) *
            matrixPointConditionedLocalVarianceAtPolynomial params model g := by
    intro g
    simpa [matrixPointConditionedGlobalVarianceAtPolynomial,
      matrixPointConditionedLocalVarianceAtPolynomial]
      using
        (matrixLocalToGlobal params
          (matrixPointConditionedRealizationAtPolynomial params model g))
  have hglobal :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          globalVarianceOfPointsError params eps delta := by
    intro g
    calc
      matrixPointConditionedGlobalVarianceAtPolynomial params model g
        ≤ (params.m : Error) *
            matrixPointConditionedLocalVarianceAtPolynomial params model g :=
          hexpansion g
      _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta := by
            exact mul_le_mul_of_nonneg_left
              (hlocal.pointwiseLocalVarianceBound g) (by positivity)
      _ = globalVarianceOfPointsError params eps delta := by
            simp [globalVarianceOfPointsError, localVarianceOfPointsError]
            ring
  refine
    { pointwiseExpansionTransfer := hexpansion
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := ?_ }
  · unfold matrixPointConditionedGlobalVariance
    calc
      avgOver (polynomialDistribution params)
          (fun g => matrixPointConditionedGlobalVarianceAtPolynomial params model g)
        ≤ avgOver (polynomialDistribution params)
            (fun _ => globalVarianceOfPointsError params eps delta) := by
              apply avgOver_mono
              intro g
              exact hglobal g
      _ = globalVarianceOfPointsError params eps delta := by
            simp [polynomialDistribution, avgOver, uniformDistribution]

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  -- The analytic pointwise estimate is an explicit input here. In the
  -- self-improvement pipeline it is supplied by `SelfImprovementBridgePackage`.
  refine
    { aggregateFamilyComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (axisParallelLineQuestionDistribution params)
          (generalizeBLeftFamily params strategy G)
          (generalizeBRightFamily params strategy G)
          (fun qu g =>
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
          (fun qu g =>
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
          (by
            intro qu
            simp [generalizeBLeftFamily, averageUnitSubMeas_outcome])
          (by
            intro qu
            simp [generalizeBRightFamily, averageUnitSubMeas_outcome])
          (generalizeBError params) (by
            intro g
            simpa [generalizeBDeviationAtPolynomial] using hpoint g)
      pointwiseNormBound := hpoint
      averagedNormBound := by
        unfold generalizeBDeviation
        calc
          avgOver (polynomialDistribution params)
              (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => generalizeBError params) := by
                  apply avgOver_mono
                  intro g
                  exact hpoint g
          _ = generalizeBError params := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

/-- `lem:local-variance-of-points`. -/
lemma localVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocal :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (rerandomizeCoord params)
          (localVarianceLeftFamily params strategy G)
          (localVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [localVarianceLeftFamily, averageUnitSubMeas_outcome])
          (by
            intro uv
            simp [localVarianceRightFamily, averageUnitSubMeas_outcome])
          (localVarianceOfPointsError params eps delta) (by
            intro g
            simpa [localVarianceDeviationAtPolynomial] using hedge g)
      pointwiseEdgeNormBound := hedge
      pointwiseLocalVarianceBound := hlocal
      averagedLocalVarianceBound := by
        unfold pointConditionedLocalVariance
        calc
          avgOver (polynomialDistribution params)
              (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => localVarianceOfPointsError params eps delta) := by
                  apply avgOver_mono
                  intro g
                  exact hlocal g
          _ = localVarianceOfPointsError params eps delta := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

/-- `lem:global-variance-of-points`.
Depends on `localVarianceOfPoints` through explicit pointwise local-variance
inputs. `localToGlobal` lifts pointwise local bounds to global bounds, and the
averaging step is fully proved. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocalVar :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hdev :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          globalVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  let hlocal :=
    localVarianceOfPoints params strategy eps delta gamma hgood G ψbi hlocalDev hlocalVar
  have hglobal :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta := by
    intro g
    calc
      pointConditionedGlobalVarianceAtPolynomial params strategy G g
        ≤ (params.m : Error) *
            pointConditionedLocalVarianceAtPolynomial params strategy G g := by
              simpa [pointConditionedGlobalVarianceAtPolynomial,
                pointConditionedLocalVarianceAtPolynomial]
                using
                  (localToGlobal params
                    (fun u =>
                      leftTensor (ι₂ := ι)
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
                    (weightedPolynomialState params strategy G g))
      _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta := by
            exact mul_le_mul_of_nonneg_left
              (hlocal.pointwiseLocalVarianceBound g) (by positivity)
      _ = globalVarianceOfPointsError params eps delta := by
            simp [globalVarianceOfPointsError, localVarianceOfPointsError]
            ring
  refine
    { aggregateGlobalComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (independentPointPair params)
          (globalVarianceLeftFamily params strategy G)
          (globalVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [globalVarianceLeftFamily, localVarianceLeftFamily, averageUnitSubMeas_outcome])
          (by
            intro uv
            simp [globalVarianceRightFamily, localVarianceRightFamily, averageUnitSubMeas_outcome])
          (globalVarianceOfPointsError params eps delta) (by
            intro g
            simpa [globalVarianceDeviationAtPolynomial] using hdev g)
      pointwiseGlobalNormBound := hdev
      pointwiseExpansionTransfer := by
        intro g
        simpa [pointConditionedGlobalVarianceAtPolynomial,
          pointConditionedLocalVarianceAtPolynomial]
          using
            (localToGlobal params
              (fun u =>
                leftTensor (ι₂ := ι)
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
              (weightedPolynomialState params strategy G g))
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := by
        unfold pointConditionedGlobalVariance
        calc
          avgOver (polynomialDistribution params)
              (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => globalVarianceOfPointsError params eps delta) := by
                  apply avgOver_mono
                  intro g
                  exact hglobal g
          _ = globalVarianceOfPointsError params eps delta := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

/-- Matrix-level counterpart of `lem:generalize-b`, proved by reducing to the
abstract version via an explicit compatibility hypothesis linking the matrix
realization to a `SymStrat`. -/
lemma matrixGeneralizeB
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params)
    (hcompat :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g =
          generalizeBDeviationAtPolynomial params strategy ψbi G g) :
    MatrixGeneralizeBStatement params model := by
  refine matrixGeneralizeB_of_pointwise params model ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:local-variance-of-points`, proved by reducing
to the abstract version via an explicit compatibility hypothesis linking the
matrix realization to a `SymStrat`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:global-variance-of-points`, proved by
reducing to the abstract version via an explicit compatibility hypothesis
linking the matrix realization to a `SymStrat`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  refine matrixGlobalVarianceOfPoints_from_local params model eps delta ?_
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g


end MIPStarRE.LDT.GlobalVariance
