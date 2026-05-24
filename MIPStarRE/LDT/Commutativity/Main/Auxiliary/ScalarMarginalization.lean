import MIPStarRE.LDT.Commutativity.Transport.FullSlice
import MIPStarRE.LDT.Commutativity.Transport.EvaluationSpecialization
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages

/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

Architecture: Implements the scalar↔tensor bridge chain (Option 3 hybrid).
Public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities; their proofs
compose internal-use tensor-form bridges from
`Transport/FullSlice/Bridges.lean` over tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluated point family, bundled as a projective submeasurement family. -/
private noncomputable def evaluatedPointProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    { toSubMeas := evaluatedPointFamily params family u
      proj := by
        intro a
        exact evaluatedPointFamily_outcome_proj params family u a }

/-- The averaged slice operator `G = E_x Gˣ` is a valid switch-sandwich middle
operator. -/
private lemma averagedSubMeas_total_bounded01
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    MIPStarRE.LDT.Preliminaries.OpBounded01
      ((IdxPolyFamily.averagedSubMeas family).total) := by
  refine ⟨?_, ?_⟩
  · exact (IdxPolyFamily.averagedSubMeas family).total_nonneg
  · exact sub_nonneg.mpr (IdxPolyFamily.averagedSubMeas family).total_le_one

/-- Triangle inequality with explicit bounds for an intermediate point. -/
private lemma abs_sub_le_of_two_step
    {a b c e₁ e₂ : Error}
    (hab : |a - b| ≤ e₁) (hbc : |b - c| ≤ e₂) :
    |a - c| ≤ e₁ + e₂ :=
  (abs_sub_le a b c).trans (add_le_add hab hbc)

/-- Marginalizing a uniform point in `Point params.next` to its final coordinate
gives the uniform slice-height distribution. -/
private lemma avgOver_pointHeight
    (params : Parameters) [FieldModel params.q]
    (f : Fq params → Error) :
    avgOver (uniformDistribution (Point params.next)) (fun u => f (pointHeight params u)) =
      avgOver (uniformDistribution (Fq params)) f := by
  calc
    avgOver (uniformDistribution (Point params.next)) (fun u => f (pointHeight params u))
        = avgOver (uniformDistribution (Point params × Fq params))
            (fun ux => f (pointHeight params ((pointNextEquiv params).symm ux))) := by
            exact MIPStarRE.LDT.avgOver_uniform_equiv (pointNextEquiv params)
              (fun u : Point params.next => f (pointHeight params u))
    _ = avgOver (uniformDistribution (Point params × Fq params)) (fun ux => f ux.2) := by
          apply avgOver_congr
          intro ux
          simp [pointNextEquiv]
    _ = avgOver (uniformDistribution (Fq params)) f := avgOver_uniform_snd f

/-- Summing the inner outcome in an `ABA` expectation turns it into the
submeasurement total. -/
private lemma sum_ev_leftTensor_sandwich_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : MIPStarRE.Quantum.Op ι) (B : SubMeas α ι) :
    (∑ b : α, ev ψ (leftTensor (ι₂ := ι) (A * B.outcome b * A))) =
      ev ψ (leftTensor (ι₂ := ι) (A * B.total * A)) := by
  rw [← ev_sum ψ (fun b : α => leftTensor (ι₂ := ι) (A * B.outcome b * A))]
  congr 1
  rw [← B.sum_eq_total]
  rw [Matrix.mul_sum]
  rw [Matrix.sum_mul]
  rw [leftTensor_finset_sum]

/-- Summing the right-register outcome in the middle switch-sandwich term turns
it into the submeasurement total. -/
private lemma sum_ev_middle_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (G : MIPStarRE.Quantum.Op ι) (A : SubMeas α ι) :
    (∑ a : α, ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) (A.outcome a))) =
      ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) A.total) := by
  rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) G *
    rightTensor (ι₁ := ι) (A.outcome a))]
  congr 1
  rw [← A.sum_eq_total]
  rw [← Matrix.mul_sum]
  rw [rightTensor_finset_sum]

/-- Averaging the middle total in an `ABA` sandwich produces the averaged
slice operator `G = E_y Gʸ`. -/
private lemma avgOver_slice_total_left_sandwich_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (family : IdxPolyFamily params ι)
    (A : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params))
        (fun y => ev ψ (leftTensor (ι₂ := ι) (A * (family.meas y).total * A))) =
      ev ψ (leftTensor (ι₂ := ι) A *
        leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
        leftTensor (ι₂ := ι) A) := by
  unfold avgOver IdxPolyFamily.averagedSubMeas
  rw [leftTensor_mul_leftTensor]
  rw [leftTensor_mul_leftTensor]
  rw [Matrix.mul_sum]
  rw [Matrix.sum_mul]
  rw [← leftTensor_finset_sum]
  rw [ev_finset_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hmatrix :
      A * (uniformDistribution (Fq params)).weight y • (family.meas y).total * A =
        (((uniformDistribution (Fq params)).weight y : Error) : ℂ) •
          (A * (family.meas y).total * A) := by
    simp [mul_assoc]
    rfl
  rw [hmatrix]
  rw [← leftTensor_smul (ι₂ := ι)
    (((uniformDistribution (Fq params)).weight y : Error) : ℂ)
    (A * (family.meas y).total * A)]
  rw [ev_scale]

/-- Full-slice cubic first term as the left switch-sandwich expectation. -/
private lemma fullSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    fullSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold fullSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
  rw [avgOver_uniform_prod (α := Fq params) (β := Fq params) (f := fun x y =>
    ∑ gh : FullSliceOutcome params,
      ev strategy.state (leftTensor (ι₂ := ι)
        ((family.meas x).toSubMeas.outcome gh.1 *
          (family.meas y).toSubMeas.outcome gh.2 *
          (family.meas x).toSubMeas.outcome gh.1)))]
  apply avgOver_congr
  intro x
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro g _
  calc
    avgOver (uniformDistribution (Fq params))
        (fun y => ∑ h : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((family.meas x).outcome g * (family.meas y).outcome h *
              (family.meas x).outcome g)))
        = avgOver (uniformDistribution (Fq params))
            (fun y => ev strategy.state (leftTensor (ι₂ := ι)
              ((family.meas x).outcome g * (family.meas y).total *
                (family.meas x).outcome g))) := by
            apply avgOver_congr
            intro y
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((family.meas x).outcome g) (family.meas y).toSubMeas
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((family.meas x).outcome g) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((family.meas x).outcome g)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((family.meas x).outcome g)

/-- Evaluated-slice cubic first term as the evaluated left switch-sandwich expectation. -/
private lemma evaluatedSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold evaluatedSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
    evaluatedPointProj
  change avgOver (uniformDistribution (Point params.next × Point params.next))
      (fun uv => (fun u v => ∑ ab : Fq params × Fq params,
        evaluatedSliceABATerm params strategy family (u, v) ab) uv.1 uv.2) =
    avgOver (uniformDistribution (Point params.next))
      (fun q => ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a)))
  rw [avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
    (f := fun u v => ∑ ab : Fq params × Fq params,
      evaluatedSliceABATerm params strategy family (u, v) ab)]
  apply avgOver_congr
  intro u
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold evaluatedSliceABATerm
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun v => ∑ b : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (evaluatedPointFamily params family v).outcome b *
              (evaluatedPointFamily params family u).outcome a)))
        = avgOver (uniformDistribution (Point params.next))
            (fun v => ev strategy.state (leftTensor (ι₂ := ι)
              ((evaluatedPointFamily params family u).outcome a *
                (evaluatedPointFamily params family v).total *
                (evaluatedPointFamily params family u).outcome a))) := by
            apply avgOver_congr
            intro v
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((evaluatedPointFamily params family u).outcome a)
              (evaluatedPointFamily params family v)
    _ = avgOver (uniformDistribution (Fq params))
          (fun y => ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (family.meas y).total *
              (evaluatedPointFamily params family u).outcome a))) := by
            have h := avgOver_pointHeight params
              (fun y : Fq params => ev strategy.state (leftTensor (ι₂ := ι)
                ((evaluatedPointFamily params family u).outcome a *
                  (family.meas y).total *
                  (evaluatedPointFamily params family u).outcome a)))
            rw [← h]
            apply avgOver_congr
            intro v
            simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
              postprocess_total]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((evaluatedPointFamily params family u).outcome a)

/-- The full and evaluated switch-sandwich middle terms are the same `G ⊗ G` average. -/
private lemma fullSlice_middleSandwichExpectation_eq_evaluated
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) =
      MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold MIPStarRE.LDT.Preliminaries.middleSandwichExpectation evaluatedPointProj
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  change avgOver (uniformDistribution (Fq params))
      (fun x => ∑ a : Polynomial params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
    avgOver (uniformDistribution (Point params.next))
      (fun u => ∑ a : Fq params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a)))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => ∑ a : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
      avgOver (uniformDistribution (Fq params))
        (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).total))) := by
        apply avgOver_congr
        intro x
        exact sum_ev_middle_total strategy.state G (family.meas x).toSubMeas
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) := by
        symm
        calc
          avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) =
            avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas (pointHeight params u)).total))) := by
              apply avgOver_congr
              intro u
              simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
                postprocess_total]
          _ = avgOver (uniformDistribution (Fq params))
              (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas x).total))) := by
              exact avgOver_pointHeight params
                (fun x : Fq params => ev strategy.state (leftTensor (ι₂ := ι) G *
                  rightTensor (ι₁ := ι) ((family.meas x).total)))
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ∑ a : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a))) := by
        apply avgOver_congr
        intro u
        exact (sum_ev_middle_total strategy.state G (evaluatedPointFamily params family u)).symm

/-- Paper first-term switch-sandwich transport
(`commutativity-G.tex` lines 295--305), stated in the public scalar API.

The paper does not use an `md/q` Schwartz--Zippel step for the cubic first term.
Instead, both the full and evaluated cubic terms are compared to the common
`G ⊗ G` switch-sandwich center, costing `2√ζ` on each side. -/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      4 * Real.sqrt zeta := by
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  have hG : MIPStarRE.LDT.Preliminaries.OpBounded01 G := by
    simpa [G] using averagedSubMeas_total_bounded01 params family
  have hfullApprox :
      MIPStarRE.LDT.Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (Fq params))
        (IdxProjSubMeas.toIdxSubMeas family.meas)
        (IdxProjSubMeas.toIdxSubMeas family.meas) zeta := by
    refine ⟨?_⟩
    simpa [MIPStarRE.LDT.Preliminaries.BipartiteSDDRel]
      using hself.sliceSelfConsistency.squaredDistanceBound
  have hfullSwitch :=
    MIPStarRE.LDT.Preliminaries.switchSandwich strategy.state
      (uniformDistribution (Fq params)) hnorm
      (uniformDistribution_weight_sum_le_one (Fq params))
      family.meas G hG zeta hfullApprox
  have hevalRel :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hevalApprox :
      MIPStarRE.LDT.Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family))
        (IdxProjSubMeas.toIdxSubMeas (evaluatedPointProj params family)) zeta := by
    refine ⟨?_⟩
    simpa [MIPStarRE.LDT.Preliminaries.BipartiteSDDRel, evaluatedPointProj]
      using hevalRel.squaredDistanceBound
  have hevalSwitch :=
    MIPStarRE.LDT.Preliminaries.switchSandwich strategy.state
      (uniformDistribution (Point params.next)) hnorm
      (uniformDistribution_weight_sum_le_one (Point params.next))
      (evaluatedPointProj params family) G hG zeta hevalApprox
  let fullCenter : Error :=
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
      (uniformDistribution (Fq params)) family.meas G
  let evalCenter : Error :=
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
      (uniformDistribution (Point params.next)) (evaluatedPointProj params family) G
  have hfull : |fullSliceABAAvg params strategy family - fullCenter| ≤ 2 * Real.sqrt zeta := by
    simpa [fullCenter, G, fullSliceABAAvg_eq_leftSandwichExpectation]
      using hfullSwitch.leftSandwichTransfer
  have heval : |evalCenter - evaluatedSliceABAAvg params strategy family| ≤ 2 * Real.sqrt zeta := by
    have h := hevalSwitch.leftSandwichTransfer
    have h' : |evaluatedSliceABAAvg params strategy family - evalCenter| ≤
        2 * Real.sqrt zeta := by
      simpa [evalCenter, G, evaluatedSliceABAAvg_eq_leftSandwichExpectation] using h
    rwa [abs_sub_comm]
  have hcenter : fullCenter = evalCenter := by
    simpa [fullCenter, evalCenter, G]
      using fullSlice_middleSandwichExpectation_eq_evaluated params strategy family
  have htri := abs_sub_le_of_two_step hfull (by simpa [hcenter] using heval)
  calc
    |fullSliceABAAvg params strategy family - evaluatedSliceABAAvg params strategy family|
      ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt zeta := htri
    _ = 4 * Real.sqrt zeta := by ring

/-- Proved package for the first `closenessOfIP` leg in the y-side
second-term prefix.

The earlier prefix steps from `commutativity-G.tex` lines 332--354 are proved in
`fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg`: `eq:gcom4` costs `√ζ` and
`eq:gcom4-diff` costs `md/q`.  The second line-360 `closenessOfIP` bridge from
`xEvaluatedFullSliceABABAvg` to `xEvaluatedFullSliceABABtensorAvg` is now proved
in `xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg`.

Thus this package records the first paper line-359 bridge from the
x-evaluated `BAB ⊗ A` tensor endpoint to the scalar endpoint in the display from
`eq:evaluate-gcom-at-points` to `eq:don't-understand-the-numbering-system`. -/
private structure FullSliceScalarMarginalizeYFirstCloseness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error) where
  first_closeness :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family| ≤
      Real.sqrt zeta

/-- First `closenessOfIP` witness for the `y` prefix.

This packages the proved paper `commutativity-G.tex` line-359 bridge.  The
earlier `eq:gcom4`/`eq:gcom4-diff` prefix, the line-360 scalar-to-tensor bridge,
and the y-marginalization tail are proved separately and composed below. -/
private noncomputable def fullSliceScalarMarginalizeYFirstCloseness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    FullSliceScalarMarginalizeYFirstCloseness params strategy family zeta := by
  exact ⟨xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
    params strategy family zeta hnorm hself⟩

/-- Paper-faithful second-term transport bound.

The proved x-prefix (`eq:gcom4` plus `eq:gcom4-diff`, paper lines 332--354)
costs `md/q + √ζ`; the proved line-359 `closenessOfIP` bridge costs `√ζ`;
the line-360 scalar↔tensor bridge is proved in
`xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg` and costs
another `√ζ`; and the proved y-tail uses y-Schwartz--Zippel marginalization
(paper lines 369--385) plus the `√ζ` doubly-evaluated scalar↔tensor bridge. Thus
the whole scalar second-term comparison costs `2·md/q + 4√ζ`. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (2 * ((↑params.m : Error) * ↑params.d / ↑params.q) + 4 * Real.sqrt zeta) := by
  let yClose :=
    fullSliceScalarMarginalizeYFirstCloseness
      params strategy family zeta hnorm hself
  have hxPrefix :=
    fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
      params strategy family zeta hnorm hself
  have htail :=
    xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
      params strategy family zeta hnorm hself
  have hsecond :=
    xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
      params strategy family zeta hnorm hself
  have hclose := abs_sub_le_of_two_step yClose.first_closeness hsecond
  have hclose_bound :
      |xEvaluatedSliceBABAtensorAvg params strategy family -
          xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
        2 * Real.sqrt zeta := by
    calc
      |xEvaluatedSliceBABAtensorAvg params strategy family -
          xEvaluatedFullSliceABABtensorAvg params strategy family|
        ≤ Real.sqrt zeta + Real.sqrt zeta := hclose
      _ = 2 * Real.sqrt zeta := by ring
  have hprefix := abs_sub_le_of_two_step hxPrefix hclose_bound
  have h := abs_sub_le_of_two_step hprefix htail
  calc
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family|
      ≤ (((↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta) +
          2 * Real.sqrt zeta) +
          ((↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta) := h
    _ = 2 * ((↑params.m : Error) * ↑params.d / ↑params.q) +
          4 * Real.sqrt zeta := by ring

end MIPStarRE.LDT.Commutativity
