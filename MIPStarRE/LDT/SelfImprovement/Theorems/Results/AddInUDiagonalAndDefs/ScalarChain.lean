import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs.Selection

/-!
# Scalar chain for the diagonal add-in-u transfer

This module contains the selected and diagonal Q₀--Q₄ scalar chains used for the
projection-simplified diagonal add-in-`u` transfer, together with the endpoint
identifications needed by the helper strong-self-consistency proof.

## References

- `references/ldt-paper/self_improvement.tex` lines 247--252
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-! ### Scalar chain for the projection-simplified diagonal add-in-u transfer -/

/-- Strong self-consistency for the point measurement, pulled back to the second
coordinate of the independent `(u, v)` average used by the add-in-`u` scalar
chain.

This is the distributional self-consistency input for the `A^v_{h(v)}` moves in
`self_improvement.tex`, lines 255--297: the point measurement sampled at `v`
has the same `2δ` left/right state-dependent distance after the product average
over `(u, v)`. -/
lemma addInU_pointMeasurement_snd_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    SDDRel strategy.state (uniformDistribution (Point params × Point params))
      (IdxSubMeas.liftLeft
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (IdxSubMeas.liftRight
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (2 * delta) := by
  classical
  have hssc_pair :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params × Point params))
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas)
        delta := by
    rcases hssc with ⟨hssc⟩
    constructor
    calc
      avgOver (uniformDistribution (Point params × Point params))
          (fun uv : Point params × Point params =>
            qBipartiteSSCDefect strategy.state
              ((strategy.pointMeasurement uv.2).toSubMeas))
        =
          avgOver (uniformDistribution (Point params))
            (fun v : Point params =>
              qBipartiteSSCDefect strategy.state
                ((strategy.pointMeasurement v).toSubMeas)) := by
            exact avgOver_uniform_snd
              (α := Point params) (β := Point params)
              (fun v : Point params =>
                qBipartiteSSCDefect strategy.state
                  ((strategy.pointMeasurement v).toSubMeas))
      _ ≤ delta := by
            simpa [bipartiteSSCError, IdxProjMeas.toIdxSubMeas] using hssc
  have hraw :=
    Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (strategy.pointMeasurement uv.2).toSubMeas)
      delta
      (fun _uv (a : Fq params) => a)
      hssc_pair
  simpa using hraw

/-- The grouped tensor mass over a fiber `h(v)=a` is a contraction.

This is the submeasurement bound used inside the first Cauchy--Schwarz square
root in `self_improvement.tex`, lines 267--272: after grouping by the value
`a = h(v)`, the selected operators
`H^u_h ⊗ T_h` are dominated by the total mass of the sandwiched polynomial
submeasurement at `u`, hence by `I`. -/
lemma addInU_filtered_sandwiched_tensor_sum_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u v : Point params) (a : Fq params) :
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h v = a),
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  exact SubMeas.opTensor_sum_filter_le_one
    (sandwichedPolynomialSubMeasAt params strategy T u)
    T
    (fun h : Polynomial params => h v = a)

/-! ### Selection-parametrized add-in-u scalar chain

The paper proves `lem:add-in-u` for an arbitrary outcome family `M` and
selection `S_u ⊆ 𝒪 × polyfunc`.  The diagonal helper strong-self-consistency
application below is one specialization of this statement.  The following
definitions record the same five scalar quantities before specializing to the
diagonal case, so that the off-diagonal point-consistency selection can reuse
the Cauchy--Schwarz chain rather than restating the transfer hypothesis. -/

/-- The selected-chain left endpoint `Q₀`.

For a selected pair `(o, h) ∈ S_u`, this is the expectation of
`M^u_o ⊗ H^v_h`, where `H^v_h = A^v_{h(v)} T_h A^v_{h(v)}`. -/
noncomputable def addInUSelectedCSChainQ0
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      ev strategy.state
        (opTensor ((M uv.1).outcome ah.1)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome ah.2)))

/-- The selected-chain scalar `Q₁`, after moving the right point projector
`A^v_{h(v)}` to the left tensor factor once. -/
noncomputable def addInUSelectedCSChainQ1
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Av * (M uv.1).outcome ah.1) (T.outcome ah.2 * Av)))

/-- The selected-chain scalar `Q₂`, after moving both right point projectors to
the left tensor factor. -/
noncomputable def addInUSelectedCSChainQ2
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Av * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₃`, after replacing the first point projector
at `v` by the corresponding point projector at `u`. -/
noncomputable def addInUSelectedCSChainQ3
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
      ev strategy.state
        (opTensor (Au * (M uv.1).outcome ah.1 * Av) (T.outcome ah.2)))

/-- The selected-chain scalar `Q₄`, after replacing both point projectors at
`v` by the corresponding point projectors at `u`. -/
noncomputable def addInUSelectedCSChainQ4
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ ah ∈ addInUSelectionPairs params S uv.1,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
      ev strategy.state
        (opTensor (Au * (M uv.1).outcome ah.1 * Au) (T.outcome ah.2)))

/-- The selected-chain endpoint `Q₀` is the generic add-in-u left quantity when
the second measurement is the averaged sandwiched polynomial submeasurement. -/
theorem addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T)
        S =
      addInUSelectedCSChainQ0 params strategy M T S := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInULeftOperatorAtPoint params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T) S u)) =
    addInUSelectedCSChainQ0 params strategy M T S
  unfold addInULeftOperatorAtPoint addInUSelectedCSChainQ0
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        ev strategy.state
          (opTensor ((M u).outcome ah.1)
            ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  calc
    ev strategy.state
        (∑ ah ∈ addInUSelectionPairs params S u,
          opTensor ((M u).outcome ah.1)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome ah.2))
        =
      ∑ ah ∈ addInUSelectionPairs params S u,
        ev strategy.state
          (opTensor ((M u).outcome ah.1)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome ah.2)) := by
        rw [ev_finset_sum]
    _ =
      ∑ ah ∈ addInUSelectionPairs params S u,
        avgOver (uniformDistribution (Point params)) (fun v =>
          ev strategy.state
            (opTensor ((M u).outcome ah.1)
              ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2))) := by
        refine Finset.sum_congr rfl ?_
        intro ah _
        simpa [averagedSandwichedPolynomialSubMeas, sandwichedPolynomialSubMeasAt] using
          ev_opTensor_averageOperatorOverDistribution_right strategy.state
            (uniformDistribution (Point params))
            ((M u).outcome ah.1)
            (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)
    _ =
      avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ ah ∈ addInUSelectionPairs params S u,
          ev strategy.state
            (opTensor ((M u).outcome ah.1)
              ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2))) := by
        exact (MIPStarRE.LDT.avgOver_finset_sum (uniformDistribution (Point params))
          (addInUSelectionPairs params S u)
          (fun v ah =>
            ev strategy.state
              (opTensor ((M u).outcome ah.1)
                ((sandwichedPolynomialSubMeasAt params strategy T v).outcome ah.2)))).symm

/-- The selected-chain endpoint `Q₄` is the generic add-in-u right quantity. -/
theorem addInUSelectedCSChainQ4_eq_rightQuantity
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInURightQuantity params strategy M T S =
      addInUSelectedCSChainQ4 params strategy M T S := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy M T S u)) =
    addInUSelectedCSChainQ4 params strategy M T S
  unfold addInURightOperatorAtPoint addInUSelectedCSChainQ4
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u _ =>
      ∑ ah ∈ addInUSelectionPairs params S u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state
          (opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [ev_finset_sum]
  exact (avgOver_uniform_const
    (∑ ah ∈ addInUSelectionPairs params S u,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
      ev strategy.state
        (opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)))).symm

/-- The expanded left endpoint `Q₀` of the four-step scalar chain in
`self_improvement.tex`, lines 247--252, after setting `M^u = H^u` and averaging
the second tensor factor `H = E_v H^v`. -/
noncomputable def addInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ev strategy.state
        (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome h)))

/-- The scalar `Q₁` obtained from `Q₀` by moving the right point projection
`A^v_{h(v)}` to the left tensor factor; this is the target of
`eq:move-one`. -/
noncomputable def addInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          (T.outcome h * Av)))

/-- The scalar `Q₂` obtained from `Q₁` by moving the second right point
projection to the left tensor factor; this is the target of `eq:move-another`. -/
noncomputable def addInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₃` obtained from `Q₂` by replacing the first point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; this is the target of `eq:change-one`. -/
noncomputable def addInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₄` obtained from `Q₃` by replacing the second point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; after the projection collapse, this is the
projection-simplified right endpoint of the diagonal add-in-u transfer. -/
noncomputable def addInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Au)
          (T.outcome h)))

/-- The expanded chain endpoint `Q₀` is the existing diagonal match-mass left
side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q0_eq_match_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) =
      addInUCSChainQ0 params strategy T := by
  classical
  calc
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (Point params)) (fun v =>
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
        unfold qBipartiteMatchMass averagedSandwichedPolynomialSubMeas
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [ev_opTensor_averageOperatorOverDistribution_left]
        refine avgOver_congr _ _ _ ?_
        intro u
        simpa [sandwichedPolynomialSubMeasAt] using
          ev_opTensor_averageOperatorOverDistribution_right strategy.state
            (uniformDistribution (Point params))
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
            (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome h)
    _ = addInUCSChainQ0 params strategy T := by
        symm
        unfold addInUCSChainQ0
        rw [avgOver_uniform_prod (α := Point params) (β := Point params)
          (f := fun u v =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))]
        calc
          avgOver (uniformDistribution (Point params)) (fun u =>
              avgOver (uniformDistribution (Point params)) (fun v =>
                ∑ h : Polynomial params,
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h))))
              =
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ h : Polynomial params,
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              refine avgOver_congr _ _ _ ?_
              intro u
              rw [avgOver_sum]
          _ =
            ∑ h : Polynomial params,
              avgOver (uniformDistribution (Point params)) (fun u =>
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              rw [avgOver_sum]

/-- The raw chain endpoint `Q₄` collapses to the projection-simplified scalar
right side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q4_eq_simplified_rhs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
  classical
  calc
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
              (T.outcome h))) := by
        unfold addInUCSChainQ4
        refine avgOver_congr _ _ _ ?_
        intro uv
        refine Finset.sum_congr rfl ?_
        intro h _
        have hproj :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 := by
          simpa [pointConditionedOutcomeOperatorAtPolynomial] using
            (strategy.pointMeasurement uv.1).proj (h uv.1)
        have hcollapse :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := by
          change
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                  T.outcome h *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1) *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          exact proj_outer_sandwich_eq _ _ hproj
        simp [hcollapse]
    _ =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
        exact avgOver_uniform_fst (α := Point params) (β := Point params)
          (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  (T.outcome h)))


end MIPStarRE.LDT.SelfImprovement
