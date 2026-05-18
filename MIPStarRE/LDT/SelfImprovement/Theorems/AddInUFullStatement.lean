import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Transfer
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems

/-!
# Section 7 — Selection-dependent transfer inequality for `lem:add-in-u`

This file proves the full selection-dependent transfer inequality of
`lem:add-in-u` (`references/ldt-paper/self_improvement.tex` lines 238–246).
The existing `addInU` lemma in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean:584`
formalizes only the variance-bound specialization used in subsequent arguments.

The theorem below combines the already formalized selected Cauchy--Schwarz
chain with the six-step cardinality-free local-variance transport bound to
establish the paper's fully quantified transfer inequality.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper-faithful full statement of `lem:add-in-u`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 238–246
(`\label{lem:add-in-u}`). The proof spans lines 247–343.

The paper's statement: for every auxiliary sub-measurement family
`M = {M^u_o}` indexed by points `u ∈ F_q^m` with outcomes in some set `O`,
and every selection rule `S : Point → Set (O × Polynomial)`, the two indexed
expectations

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| M^u_o ⊗ H_h |ψ⟩
```

and

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| (A^u_{h(u)} M^u_o A^u_{h(u)}) ⊗ T_h |ψ⟩
```

agree to within `4 √ζ_variance = addInUError params eps delta`. Here `H` is
**not** an arbitrary sub-measurement: per the paper's construction and the
existing `SelfImprovementHelperConclusion.averagedConstruction` field, `H` is
the averaged sandwiched family `H_h = E_u (A^u · T_h · A^u)` derived from the
SDP measurement `T` supplied by `lem:sdp`. We substitute that derivation
directly into the inequality rather than taking `H` as an extra parameter,
so the structure records exactly the paper's transfer inequality.

The reduced `AddInUStatement` (`Statements.lean:293`) only records the
variance-bound consequence used in subsequent arguments; this structure
records the universally-quantified transfer inequality itself.

The Lean parameter `T` is kept as a `Measurement`, matching the paper's fixed
SDP-optimal family. The operators appearing in the transfer inequality depend
only on `T.toSubMeas`, and the proof below passes to that submeasurement layer
internally for the selected Cauchy--Schwarz chain and global-variance bounds. -/
structure AddInUFullStatement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- The selection-dependent transfer inequality from `lem:add-in-u`, with
  the paper's `4 √ζ_variance` bound. Universally quantified over the
  auxiliary outcome set `Outcome`, the auxiliary `M`-family, and the
  selection rule `S`, matching the paper's "for any sub-measurement and any
  selection" framing. The averaged family `H` is the canonical
  `averagedSandwichedPolynomialSubMeas params strategy T`, matching
  `SelfImprovementHelperConclusion.averagedConstruction`. -/
  selectionDependentTransfer :
    ∀ {Outcome : Type*} [Fintype Outcome]
      (M : IdxSubMeas (Point params) Outcome ι)
      (S : AddInUSelection params Outcome),
    |addInULeftQuantity params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) S
        - addInURightQuantity params strategy M T.toSubMeas S|
      ≤ addInUError params eps delta

-- The paper-facing add-in-u statement combines the selected scalar chain, the
-- local-variance transport theorem, and the global-variance sum transfer.
/-- Proves the selection-dependent transfer inequality of `lem:add-in-u`:
for any auxiliary sub-measurement family `M = {M^u_o}` and selection rule
`S : Point → Set (Outcome × Polynomial)`, the two indexed expectations agree
to within `4 √ζ_variance` (the bound `addInUError params eps delta`), given
strategy self-consistency in the `IsGood eps delta gamma` standing context.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 247–343
(proof of `\label{lem:add-in-u}`). The paper's proof is a Cauchy–Schwarz
chain through the four intermediate quantities `Q_0, Q_1, Q_2, Q_3, Q_4`
(formalized as `addInUCSChainQ0` … `addInUCSChainQ4` in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/`),
combining the self-consistency of `A` (giving `√(2δ)` bounds on the
"insertion" steps) with the global-variance bound (giving
`√globalVarianceDeviationSum` bounds on the "averaging" steps).

The reduced `addInU` lemma in `Bracketed.lean:584` records the specialization
of this chain to the variance-bound consequence used later.  The theorem below
formalizes the full universally quantified inequality.

The `gamma` parameter and `hgood : IsGood eps delta gamma` hypothesis carry
the paper's standing "good strategy" context; `gamma` does not appear in
`AddInUFullStatement`'s bound (which is `addInUError params eps delta`),
matching the paper's framing where `lem:add-in-u` is invoked inside a
`good`-strategy section. -/
theorem addInUFullStatement_of_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι) :
    AddInUFullStatement params strategy T eps delta := by
  refine ⟨?_⟩
  intro Outcome _instOutcome M S
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    constructor
    simpa [SymStrat.selfConsistencyFailureProbability] using
      hgood.selfConsistencyTest
  have hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta :=
    localVarianceDeviation_sum_le_localVarianceOfPointsError
      params strategy eps delta gamma hgood T.toSubMeas
  have hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        selfImprovementVarianceError params eps delta := by
    simpa [selfImprovementVarianceError] using
      globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T.toSubMeas hlocal
  let ηsc : Error := Real.sqrt (2 * delta)
  let ηgv : Error := Real.sqrt (selfImprovementVarianceError params eps delta)
  have h01 :
      |addInUSelectedCSChainQ0 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ1 params strategy M T.toSubMeas S| ≤ ηsc := by
    simpa [ηsc] using
      addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
        (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S)
        (delta := delta) hssc
  have h12 :
      |addInUSelectedCSChainQ1 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ2 params strategy M T.toSubMeas S| ≤ ηsc := by
    simpa [ηsc] using
      addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
        (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S)
        (delta := delta) hssc
  obtain ⟨hsteps3, hsteps4⟩ :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      (params := params) (strategy := strategy) (M := M) (T := T.toSubMeas) (S := S) hglobal
  have h23 :
      |addInUSelectedCSChainQ2 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ3 params strategy M T.toSubMeas S| ≤ ηgv := by
    simpa [ηgv] using hsteps3
  have h34 :
      |addInUSelectedCSChainQ3 params strategy M T.toSubMeas S -
        addInUSelectedCSChainQ4 params strategy M T.toSubMeas S| ≤ ηgv := by
    simpa [ηgv] using hsteps4
  have hsum : ηsc + ηsc + ηgv + ηgv ≤ addInUError params eps delta := by
    have h :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
    dsimp [ηsc, ηgv] at h ⊢
    linarith
  exact add_in_u_selected_transfer_of_cs_chain
    (params := params) (strategy := strategy) (eps := eps) (delta := delta)
    (M := M) (T := T.toSubMeas) (S := S)
    (η01 := ηsc) (η12 := ηsc) (η23 := ηgv) (η34 := ηgv)
    h01 h12 h23 h34 hsum

end MIPStarRE.LDT.SelfImprovement
