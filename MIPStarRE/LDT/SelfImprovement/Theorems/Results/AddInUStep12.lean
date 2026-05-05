import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs

/-!
# Add-in-u Cauchy–Schwarz Step 1/2 bounds and algebraic alignment

Algebraic operator-rewrites that align the add-in-u chain differences into
commutator-times-PSD form, and the raw Cauchy–Schwarz bounds
`|Q₀−Q₁| ≤ √(2δ)` and `|Q₁−Q₂| ≤ √(2δ)` from the paper.

## Contents

- **addInU_pointMeasurement_snd_selfConsistency** — point-measurement
  self-consistency on the second coordinate of the `(u, v)` product
  average, giving `SDD ≤ 2δ`.
- **addInU_filtered_sandwiched_tensor_sum_le_one** — grouped
  `h(v)=a` tensor mass is a contraction (`≤ 1`).
- **addInU_step1/step2/step3/step4_pointwise_op_eq** (private) — operator-level
  difference rewrites for the four scalar moves.
- **addInU_cs_chain_step1/step2/step3/step4_diff_eq** — algebraic alignment of
  the diagonal chain differences to commutator-times-PSD form.
- **addInU_selected_cs_chain_step1/step2/step3/step4_diff_eq** — the same
  algebraic alignments before specializing the add-in-u selection.
- **addInU_step1/step2_C_contraction** (private) — the summed Hermitian
  contraction side conditions for `closenessOfInnerProduct_right/left`.
- **addInU_cs_chain_step1/step2_abs_le_sqrt_two_delta** — the raw
  `√(2δ)` bounds for Step 1 and Step 2, proved via
  `closenessOfInnerProduct` and the above inputs.

## References

- `references/ldt-paper/self_improvement.tex` lines 255–297
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Algebraic CS-alignment for the add-in-u Step 1/2 differences

This section records pure operator-algebra rewrites that bring the differences
`addInUCSChainQ1 - addInUCSChainQ0` and `addInUCSChainQ2 - addInUCSChainQ1`
into the shapes required by the paper's Cauchy--Schwarz steps
`eq:move-one-cauchy-schwarz` and `eq:move-another-cauchy-schwarz`
(`references/ldt-paper/self_improvement.tex`, lines 261--266 and 285--289).
The reverse-difference companions give the downstream orientation
`Q₀ - Q₁` and `Q₁ - Q₂` without repeating subtraction bookkeeping.

They do **not** discharge the Cauchy--Schwarz estimate itself; they reduce the
raw `|Q₁ - Q₀| ≤ √(2δ)` and `|Q₁ - Q₂| ≤ √(2δ)` bounds to (a) a
sandwich-form Cauchy--Schwarz on the resulting `D · (M^u_h ⊗ T_h) · D'`-style
expression, plus (b) the two square-root inputs available via
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`.

Names are deliberately suffixed `_diff_eq` to keep them honest as intermediate
algebraic identities rather than as the final scalar bounds. -/

private lemma addInU_step1_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M) (Th * Av) - opTensor M (Av * Th * Av) =
      (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av) *
        (opTensor M Th * rightTensor (ι₁ := κ) Av) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  have hRight :
      rightTensor (ι₁ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor M (Av * Th * Av) := by
    change opTensor 1 Av * (opTensor M Th * opTensor 1 Av) =
        opTensor M (Av * Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  rw [sub_mul, hLeft, hRight]

private lemma addInU_step2_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M * Av) Th - opTensor (Av * M) (Th * Av) =
      leftTensor (ι₂ := κ) Av *
        (opTensor M Th * (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av)) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * leftTensor (ι₂ := κ) Av) =
        opTensor (Av * M * Av) Th := by
    change opTensor Av 1 * (opTensor M Th * opTensor Av 1) =
        opTensor (Av * M * Av) Th
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  have hRight :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  rw [mul_sub, mul_sub, hLeft, hRight]

/-- Operator algebra reduction for the `Q₂ → Q₃` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^v · H^u_h · A^v` and `A^u · H^u_h · A^v` (with shared right factor `T_h`)
factors as `(A^v − A^u) · H^u_h · A^v` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
private lemma addInU_step3_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Au Av Mh Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * Mh * Av) Th - opTensor (Au * Mh * Av) Th =
      opTensor ((Av - Au) * Mh * Av) Th := by
  rw [opTensor_sub_left]
  congr 1
  noncomm_ring

/-- Operator algebra reduction for the `Q₃ → Q₄` add-in-`u` step.

The operator difference of the bipartite-tensor expectations of
`A^u · H^u_h · A^v` and `A^u · H^u_h · A^u` (with shared right factor `T_h`)
factors as `A^u · H^u_h · (A^v − A^u)` on the left tensor factor, leaving the
right factor `T_h` untouched. -/
private lemma addInU_step4_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Au Av Mh Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Au * Mh * Av) Th - opTensor (Au * Mh * Au) Th =
      opTensor (Au * Mh * (Av - Au)) Th := by
  rw [opTensor_sub_left]
  congr 1
  rw [mul_sub]

/-- Algebraic CS-alignment for the `Q₀ → Q₁` step.

Rewrites the difference `addInUCSChainQ1 - addInUCSChainQ0` in the exact form
appearing on the LHS of `eq:move-one-cauchy-schwarz` (paper lines 261--266):
the inner-product of the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}` with `M^u_h ⊗ T_h · (I ⊗ A^v_{h(v)})`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency`. -/
lemma addInU_cs_chain_step1_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av))) := by
  classical
  unfold addInUCSChainQ0 addInUCSChainQ1
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step1_pointwise_op_eq Mh Av (T.outcome h)

/-- Algebraic CS-alignment for the `Q₁ → Q₂` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ1` in the exact form
appearing on the LHS of `eq:move-another-cauchy-schwarz` (paper lines 285--289):
the inner-product of `(A^v_{h(v)} · M^u_h) ⊗ T_h` with the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, averaged over `(u, v)` and summed over `h`.
The Lean statement keeps the equivalent factored form
`(A^v_{h(v)} ⊗ I) · (M^u_h ⊗ T_h)` before the commutator.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`. -/
lemma addInU_cs_chain_step2_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Mh (T.outcome h) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  classical
  unfold addInUCSChainQ1 addInUCSChainQ2
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step2_pointwise_op_eq Mh Av (T.outcome h)

/-- Reverse-orientation form of `addInU_cs_chain_step1_diff_eq`.

This is the same algebraic identity as the `Q₀ → Q₁` rewrite, stated in the
`Q₀ - Q₁` orientation used by the later absolute-value chain. -/
lemma addInU_cs_chain_step1_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av))) := by
  rw [← addInU_cs_chain_step1_diff_eq params strategy T]
  ring

/-- Reverse-orientation form of `addInU_cs_chain_step2_diff_eq`.

This is the same algebraic identity as the `Q₁ → Q₂` rewrite, stated in the
`Q₁ - Q₂` orientation used by the later absolute-value chain. -/
lemma addInU_cs_chain_step2_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Mh (T.outcome h) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  rw [← addInU_cs_chain_step2_diff_eq params strategy T]
  ring

/-- Algebraic CS-alignment for the `Q₂ → Q₃` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ3` in the exact form
appearing on the LHS of `eq:change-one-cauchy-schwarz` (paper lines 306--311):
the expectation of `((A^v_{h(v)} - A^u_{h(u)}) · H^u_h · A^v_{h(v)}) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

The paper writes the middle factor as the fiber operator `M^u_o`; in this
formalization the preceding `o`-sum has already been collapsed along
`o = h(u)`, so the same factor appears as
`H^u_h = (sandwichedPolynomialSubMeasAt params strategy T u).outcome h`.

This identity is purely algebraic; the operator Cauchy--Schwarz estimate is
proved downstream by `add_in_u_cs_chain_q2_q3_factored_cs`. -/
lemma addInU_cs_chain_step3_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (opTensor ((Av - Au) * Mh * Av) (T.outcome h))) := by
  classical
  unfold addInUCSChainQ2 addInUCSChainQ3
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step3_pointwise_op_eq Au Av Mh (T.outcome h)

/-! ### Selection-parametrized Step 1/2 algebraic identities -/

/-- Algebraic CS-alignment for the selected `Q₀ → Q₁` step.

This is the selection-parametrized form of `addInU_cs_chain_step1_diff_eq`.
It rewrites the scalar difference using the same commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, but sums only over the selected pairs
`(o,h) ∈ S_u` and leaves the arbitrary outcome operator `M^u_o` in place. -/
lemma addInU_selected_cs_chain_step1_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av))) := by
  classical
  unfold addInUSelectedCSChainQ0 addInUSelectedCSChainQ1
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step1_pointwise_op_eq Moh Av (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₁ → Q₂` step.

This is the selection-parametrized form of `addInU_cs_chain_step2_diff_eq`,
with the arbitrary selected outcome operator `M^u_o` in the left tensor factor. -/
lemma addInU_selected_cs_chain_step2_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Moh (T.outcome ah.2) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  classical
  unfold addInUSelectedCSChainQ1 addInUSelectedCSChainQ2
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step2_pointwise_op_eq Moh Av (T.outcome ah.2)

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step1_diff_eq`. -/
lemma addInU_selected_cs_chain_step1_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av))) := by
  rw [← addInU_selected_cs_chain_step1_diff_eq params strategy M T S]
  ring

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step2_diff_eq`. -/
lemma addInU_selected_cs_chain_step2_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Moh (T.outcome ah.2) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  rw [← addInU_selected_cs_chain_step2_diff_eq params strategy M T S]
  ring

/-- Algebraic CS-alignment for the selected `Q₂ → Q₃` step.

This rewrites the first point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the left copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
lemma addInU_selected_cs_chain_step3_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2))) := by
  classical
  unfold addInUSelectedCSChainQ2 addInUSelectedCSChainQ3
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step3_pointwise_op_eq Au Av Moh (T.outcome ah.2)

/-- Algebraic CS-alignment for the selected `Q₃ → Q₄` step.

This rewrites the second point-replacement move for an arbitrary selected
outcome family.  The only changed factor is the right copy of the point
projector, from `A^v_{h(v)}` to `A^u_{h(u)}`. -/
lemma addInU_selected_cs_chain_step4_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2))) := by
  classical
  unfold addInUSelectedCSChainQ3 addInUSelectedCSChainQ4
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro ah _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
  set Moh := (M uv.1).outcome ah.1
  rw [← ev_sub]
  congr 1
  exact addInU_step4_pointwise_op_eq Au Av Moh (T.outcome ah.2)

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step3_diff_eq`. -/
lemma addInU_selected_cs_chain_step3_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2))) := by
  rw [← addInU_selected_cs_chain_step3_diff_eq params strategy M T S]
  ring

/-- Reverse-orientation selected form of `addInU_selected_cs_chain_step4_diff_eq`. -/
lemma addInU_selected_cs_chain_step4_reverse_diff_eq
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    addInUSelectedCSChainQ4 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ ah ∈ addInUSelectionPairs params S uv.1,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2))) := by
  rw [← addInU_selected_cs_chain_step4_diff_eq params strategy M T S]
  ring

/-- The selected fiber tensor mass is a contraction.

For fixed points `u, v` and a value `a`, the selected sum over pairs
`(o,h) ∈ S_u` with `h(v)=a` is bounded by the full product
`M^u_{\mathrm{tot}} ⊗ T_{\mathrm{tot}}`, hence by the identity. -/
private lemma addInU_selected_filtered_tensor_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u v : Point params)
    (a : Fq params) :
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  calc
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2)
        ≤ ∑ ah : Outcome × Polynomial params,
            opTensor ((M u).outcome ah.1) (T.outcome ah.2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro ah hah
              exact Finset.mem_univ ah)
            (by
              intro ah _ _
              exact opTensor_nonneg ((M u).outcome_pos ah.1) (T.outcome_pos ah.2))
    _ = opTensor (M u).total T.total := by
          change (∑ oh ∈ (Finset.univ : Finset Outcome).product
                (Finset.univ : Finset (Polynomial params)),
              opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
            opTensor (M u).total T.total
          have hprod :
              (∑ oh ∈ (Finset.univ : Finset Outcome).product
                  (Finset.univ : Finset (Polynomial params)),
                opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
                ∑ o ∈ (Finset.univ : Finset Outcome),
                  ∑ h ∈ (Finset.univ : Finset (Polynomial params)),
                    opTensor ((M u).outcome o) (T.outcome h) := by
            simpa using
              (Finset.sum_product
                (s := (Finset.univ : Finset Outcome))
                (t := (Finset.univ : Finset (Polynomial params)))
                (f := fun oh : Outcome × Polynomial params =>
                  opTensor ((M u).outcome oh.1) (T.outcome oh.2)))
          rw [hprod]
          calc
            ∑ o : Outcome, ∑ h : Polynomial params,
                opTensor ((M u).outcome o) (T.outcome h)
                = ∑ o : Outcome, opTensor ((M u).outcome o) T.total := by
                  refine Finset.sum_congr rfl ?_
                  intro o _
                  rw [← T.sum_eq_total, opTensor_sum_right_univ]
            _ = opTensor (M u).total T.total := by
                  rw [← (M u).sum_eq_total, opTensor_sum_left_univ]
    _ ≤ leftTensor (ι₂ := ι) (M u).total := by
          exact opTensor_le_leftTensor (SubMeas.total_nonneg (M u)) T.total_le_one
    _ ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact leftTensor_le_one (ι₂ := ι) (M u).total_le_one

/-- Cauchy--Schwarz contraction side condition for selected Step 1.

For a fixed `(u, v)`, the selected fiber sum
`K_a = ∑_{(o,h) ∈ S_u, h(v)=a} M^u_o ⊗ T_h` is a contraction.  Sandwiching
by the right-register point projector `A^v_a` and summing over `a` is therefore
bounded by the identity. -/
private lemma addInU_selected_step1_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    rightTensor (ι₁ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) =
        K a * Pa a := by
    intro a
    rw [← Finset.sum_mul]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, rightTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_mul_rightTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a := by
    intro a
    have hexpand : (K a * Pa a)ᴴ * (K a * Pa a) = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [rightTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, rightTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))
        = ∑ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Cauchy--Schwarz contraction side condition for selected Step 2.

This is the left-register analogue of `addInU_selected_step1_C_contraction`:
for each fixed `(u,v)`, the operators
`C_a = A^v_a \otimes I · K_a`, with `K_a` the selected fiber tensor mass,
have `∑_a C_a C_aᴴ ≤ I`. -/
private lemma addInU_selected_step2_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    leftTensor (ι₂ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) =
        Pa a * K a := by
    intro a
    rw [← Finset.mul_sum]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, leftTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_mul_leftTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ ≤ Pa a := by
    intro a
    have hexpand : (Pa a * K a) * (Pa a * K a)ᴴ = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [leftTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, leftTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ
        = ∑ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw selected `|Q₀ - Q₁| ≤ √(2δ)` bound for the first add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step1_abs_le_sqrt_two_delta`.  It applies the weighted
Cauchy--Schwarz estimate to the selected pairs `(o,h) ∈ S_u`; the contraction
side condition is `addInU_selected_step1_C_contraction`. -/
lemma addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Outcome × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (Matrix.nonneg_iff_posSemidef.mp
      ((strategy.pointMeasurement v).toSubMeas.outcome_pos a)).isHermitian.eq
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ) (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  have hsum_C : ∀ (uv : Point params × Point params) (a : Fq params),
      (∑ ah : Outcome × Polynomial params, Cop uv a ah) =
        ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) := by
    intro uv a
    let s := (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a)
    let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    have hfilter :
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
          ∑ ah ∈ s, f ah := by
      calc
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
            = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                exact
                  (Finset.sum_subset (Finset.subset_univ s)
                    (fun ah _ hnot => by simp [hnot])).symm
        _ = ∑ ah ∈ s, f ah := by
              refine Finset.sum_congr rfl ?_
              intro ah hah
              simp [hah]
    simpa [Cop, s, f] using hfilter
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × Polynomial params, Cop uv a ah)ᴴ *
            (∑ ah : Outcome × Polynomial params, Cop uv a ah)) ≤ 1 := by
    intro uv
    simpa [hsum_C uv] using addInU_selected_step1_C_contraction params strategy M T S uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hcollapse :
      ∀ (uv : Point params × Point params)
        (D : (Point params × Point params) → Fq params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
            ev strategy.state (D uv a * Cop uv a ah)) =
          ∑ ah ∈ addInUSelectionPairs params S uv.1,
            ev strategy.state
              (D uv (ah.2 uv.2) *
                (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                  rightTensor (ι₁ := ι)
                    ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)))) := by
    intro uv D
    rw [Finset.sum_comm]
    let s := addInUSelectionPairs params S uv.1
    let f : Outcome × Polynomial params → Error := fun ah =>
      ev strategy.state
        (D uv (ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2))))
    have hinner : ∀ ah : Outcome × Polynomial params,
        (∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)) =
          if ah ∈ s then f ah else 0 := by
      intro ah
      by_cases hmem : ah ∈ s
      · rw [Finset.sum_eq_single (ah.2 uv.2)]
        · simp [Cop, s, f, hmem]
        · intro a _ ha
          have hnot : ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
            intro hf
            exact ha (Eq.symm (Finset.mem_filter.mp hf).2)
          have hCop_zero : Cop uv a ah = 0 := by
            have hnot' :
                ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
              intro hf
              exact hnot (Finset.mem_filter.mpr hf)
            simp [Cop, hnot']
          rw [hCop_zero, Matrix.mul_zero, ev_zero]
        · intro hmissing
          exact (hmissing (Finset.mem_univ _)).elim
      · have hzero : ∀ a : Fq params, ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
          intro a hf
          exact hmem ((Finset.mem_filter.mp hf).1)
        calc
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
              = ∑ a : Fq params, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  have hCop_zero : Cop uv a ah = 0 := by
                    have hnot' :
                        ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
                      intro hf
                      exact hzero a (Finset.mem_filter.mpr hf)
                    simp [Cop, hnot']
                  rw [hCop_zero, Matrix.mul_zero, ev_zero]
          _ = if ah ∈ s then f ah else 0 := by simp [hmem]
    calc
      ∑ ah : Outcome × Polynomial params,
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
          = ∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ah _
              exact hinner ah
      _ = ∑ ah ∈ s, f ah := by
            have hfilter :
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
                  ∑ ah ∈ s, f ah := by
              calc
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
                    = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                        exact
                          (Finset.sum_subset (Finset.subset_univ s)
                            (fun ah _ hnot => by simp [hnot])).symm
                _ = ∑ ah ∈ s, f ah := by
                      refine Finset.sum_congr rfl ?_
                      intro ah hah
                      simp [hah]
            exact hfilter
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
            (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av)) := by
    intro uv
    rw [hcollapse uv Aop, hcollapse uv Bop]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ah _
    rw [← ev_sub]
    congr 1
    change
      leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) -
        rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) =
        (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
          rightTensor (ι₁ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2))
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S := by
    rw [addInU_selected_cs_chain_step1_diff_eq params strategy M T S]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-- Raw selected `|Q₁ - Q₂| ≤ √(2δ)` bound for the second add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step2_abs_le_sqrt_two_delta`.  It uses the left-action
Cauchy--Schwarz estimate with the selected Step 2 contraction side condition. -/
lemma addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Outcome × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state (Aop uv) (Bop uv)) ≤ 2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rfl
  have hsum_C : ∀ (uv : Point params × Point params) (a : Fq params),
      (∑ ah : Outcome × Polynomial params, Cop uv a ah) =
        ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
          leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) := by
    intro uv a
    let s := (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a)
    let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
      leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
    have hfilter :
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
          ∑ ah ∈ s, f ah := by
      calc
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
            = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                exact
                  (Finset.sum_subset (Finset.subset_univ s)
                    (fun ah _ hnot => by simp [hnot])).symm
        _ = ∑ ah ∈ s, f ah := by
              refine Finset.sum_congr rfl ?_
              intro ah hah
              simp [hah]
    simpa [Cop, s, f] using hfilter
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × Polynomial params, Cop uv a ah) *
            (∑ ah : Outcome × Polynomial params, Cop uv a ah)ᴴ) ≤ 1 := by
    intro uv
    simpa [hsum_C uv] using addInU_selected_step2_C_contraction params strategy M T S uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_left
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hcollapse :
      ∀ (uv : Point params × Point params)
        (D : (Point params × Point params) → Fq params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
            ev strategy.state (Cop uv a ah * D uv a)) =
          ∑ ah ∈ addInUSelectionPairs params S uv.1,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                    ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)) *
                  opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
                D uv (ah.2 uv.2)) := by
    intro uv D
    rw [Finset.sum_comm]
    let s := addInUSelectionPairs params S uv.1
    let f : Outcome × Polynomial params → Error := fun ah =>
      ev strategy.state
        ((leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)) *
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          D uv (ah.2 uv.2))
    have hinner : ∀ ah : Outcome × Polynomial params,
        (∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)) =
          if ah ∈ s then f ah else 0 := by
      intro ah
      by_cases hmem : ah ∈ s
      · rw [Finset.sum_eq_single (ah.2 uv.2)]
        · simp [Cop, s, f, hmem]
        · intro a _ ha
          have hnot : ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
            intro hf
            exact ha (Eq.symm (Finset.mem_filter.mp hf).2)
          have hCop_zero : Cop uv a ah = 0 := by
            have hnot' :
                ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
              intro hf
              exact hnot (Finset.mem_filter.mpr hf)
            simp [Cop, hnot']
          rw [hCop_zero, Matrix.zero_mul, ev_zero]
        · intro hmissing
          exact (hmissing (Finset.mem_univ _)).elim
      · have hzero : ∀ a : Fq params, ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
          intro a hf
          exact hmem ((Finset.mem_filter.mp hf).1)
        calc
          ∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)
              = ∑ a : Fq params, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  have hCop_zero : Cop uv a ah = 0 := by
                    have hnot' :
                        ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
                      intro hf
                      exact hzero a (Finset.mem_filter.mpr hf)
                    simp [Cop, hnot']
                  rw [hCop_zero, Matrix.zero_mul, ev_zero]
          _ = if ah ∈ s then f ah else 0 := by simp [hmem]
    calc
      ∑ ah : Outcome × Polynomial params,
          ∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)
          = ∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ah _
              exact hinner ah
      _ = ∑ ah ∈ s, f ah := by
            have hfilter :
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
                  ∑ ah ∈ s, f ah := by
              calc
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
                    = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                        exact
                          (Finset.sum_subset (Finset.subset_univ s)
                            (fun ah _ hnot => by simp [hnot])).symm
                _ = ∑ ah ∈ s, f ah := by
                      refine Finset.sum_congr rfl ?_
                      intro ah hah
                      simp [hah]
            exact hfilter
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Aop uv a)) -
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Bop uv a)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (leftTensor (ι₂ := ι) Av *
            (opTensor Moh (T.outcome ah.2) *
              (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av))) := by
    intro uv
    rw [hcollapse uv Aop, hcollapse uv Bop]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ah _
    rw [← ev_sub]
    congr 1
    change
      (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
        (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          rightTensor (ι₁ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) =
        leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            (leftTensor (ι₂ := ι)
                (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
              rightTensor (ι₁ := ι)
                (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)))
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Aop uv a)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Bop uv a)) =
      addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S := by
    rw [addInU_selected_cs_chain_step2_diff_eq params strategy M T S]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-! ### Raw Cauchy--Schwarz bound for the add-in-u Step 1 difference

This section proves the raw `|Q₀ - Q₁| ≤ √(2δ)` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277 (`eq:move-one`).

The proof combines:
* `addInU_cs_chain_step1_diff_eq` (algebraic alignment to commutator-times-PSD),
* `addInU_pointMeasurement_snd_selfConsistency` (`A^v` self-consistency lifted
  to the `(u, v)` average),
* `addInU_filtered_sandwiched_tensor_sum_le_one` (filtered sandwich-tensor mass
  is a contraction),
* `Preliminaries.closenessOfInnerProduct_right` (the weighted Cauchy--Schwarz
  inner-product bound from `prop:closeness-of-ip`, `eq:closeness4`).

The analogous Step 2 bound (`|Q₁ - Q₂| ≤ √(2δ)`) is proved by the same
strategy with `closenessOfInnerProduct_left` and the `leftTensor`-sandwiched
analogue of the Step 1 contraction lemma. -/

/-- Cauchy--Schwarz contraction side condition for Step 1.

For a fixed `(u, v)`, the right-tensor-sandwiched sum
`Σ_a (rightTensor A^v_a · K_{u,v,a})ᴴ · (rightTensor A^v_a · K_{u,v,a}) ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_right` in the Step 1 raw bound proof. -/
private lemma addInU_step1_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))ᴴ *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  -- Notation: K(a) is the filtered sandwich-tensor mass at fiber `h v = a`,
  -- and Pa is the right-placed point projection `I ⊗ A^v_a`.
  set K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
      opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  set Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    rightTensor (ι₁ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  -- Step (a): rewrite each indexed `Σ_h …` as `K a * Pa a`
  have hsum_eq : ∀ a : Fq params,
      (∑ h : Polynomial params,
          (if h uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h) *
              rightTensor (ι₁ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
          else 0)) = K a * Pa a := by
    intro a
    have hfilter :
        (∑ h : Polynomial params,
          (if h uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h) *
              rightTensor (ι₁ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
          else 0)) =
            ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) := by
      rw [Finset.sum_filter]
    rw [hfilter, ← Finset.sum_mul]
  -- Step (b): K a is Hermitian (sum of Hermitian summands)
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hMh_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)).isHermitian.eq
    have hTh_herm : ∀ h : Polynomial params,
        (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hMh_herm, hTh_herm]
  -- Step (c): Pa a is Hermitian (rightTensor of a Hermitian projection)
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, rightTensor_conjTranspose, hOutcome_herm]
  -- Step (d): Pa a is a projection (Pa a * Pa a = Pa a)
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_mul_rightTensor, hproj]
  -- Step (e): K a is PSD and ≤ 1
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro h _
    exact opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)
      (T.outcome_pos h)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  -- Step (f): bound each summand `(K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a`
  have hterm_le : ∀ a : Fq params,
      (K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a := by
    intro a
    -- Expand: (K · Pa)ᴴ · (K · Pa) = Pa · K² · Pa
    have hexpand : (K a * Pa a)ᴴ * (K a * Pa a) = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  -- Step (g): sum the pointwise bounds and use `Σ_a Pa a = 1`
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [rightTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, rightTensor_one]
  -- Step (h): conclude
  calc
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))ᴴ *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))
        = ∑ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw `|Q₀ - Q₁| ≤ √(2δ)` bound for the add-in-u Step 1 Cauchy--Schwarz move.

Proves the paper's `eq:move-one` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277, as a no-sorry
producer.  The proof combines the algebraic alignment
`addInU_cs_chain_step1_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_right`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`.

The hypothesis is the bipartite SSC for the unlifted point measurement on the
single-point distribution; the lifted `2δ` bound is constructed inside the
proof via `addInU_pointMeasurement_snd_selfConsistency`. -/
lemma addInU_cs_chain_step1_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  -- Self-consistency input: SDD ≤ 2δ between left/right point-measurement lifts
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  -- Operator families for closenessOfInnerProduct_right
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a h =>
      if h uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  -- Hermitian-ness of A and B (from projection outcomes of pointMeasurement)
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (Matrix.nonneg_iff_posSemidef.mp
      ((strategy.pointMeasurement v).toSubMeas.outcome_pos a)).isHermitian.eq
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  -- Match qSDDCore on Hermitian-conjugates with qSDDCore directly
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ) (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  -- The C contraction side condition
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ h : Polynomial params, Cop uv a h)ᴴ *
            (∑ h : Polynomial params, Cop uv a h)) ≤ 1 :=
    fun uv => addInU_step1_C_contraction params strategy T uv
  -- Apply `closenessOfInnerProduct_right`
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  -- Match `Σ_a Σ_h ev(A · C - B · C)` to `addInUCSChainQ1 - addInUCSChainQ0`
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a h)) -
        (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a h)) =
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
            (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av)) := by
    intro uv
    -- Convert each `Σ_a Σ_h …` into a single `Σ_h …` via the fiber filter
    have hAvg : ∀ (X : Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a h, h uv.2 ≠ a → X a h = 0) →
        ∑ a : Fq params, ∑ h : Polynomial params, ev strategy.state (X a h) =
          ∑ h : Polynomial params, ev strategy.state (X (h uv.2) h) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro h _
      have hsingle : ∑ a : Fq params, ev strategy.state (X a h) =
          ev strategy.state (X (h uv.2) h) := by
        rw [Finset.sum_eq_single (h uv.2)]
        · intro a _ ha
          rw [hX a h (Ne.symm ha), ev_zero strategy.state]
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
      exact hsingle
    have hAC_zero : ∀ a h, h uv.2 ≠ a → Aop uv a * Cop uv a h = 0 := by
      intro a h ha
      simp [Cop, ha]
    have hBC_zero : ∀ a h, h uv.2 ≠ a → Bop uv a * Cop uv a h = 0 := by
      intro a h ha
      simp [Cop, ha]
    rw [hAvg (fun a h => Aop uv a * Cop uv a h) hAC_zero,
        hAvg (fun a h => Bop uv a * Cop uv a h) hBC_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _
    have hCop_at : Cop uv (h uv.2) h =
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)) := by
      simp [Cop]
    have hAop_at :
        Aop uv (h uv.2) = leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    have hBop_at :
        Bop uv (h uv.2) = rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    rw [hCop_at, hAop_at, hBop_at]
    rw [← ev_sub]
    congr 1
    noncomm_ring
  -- Average the pointwise identity, then conclude
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a h)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a h)) =
      addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T := by
    rw [addInU_cs_chain_step1_diff_eq params strategy T]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  -- Wrap up: use abs_sub_comm to reverse the subtraction order
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-- Cauchy--Schwarz contraction side condition for Step 2.

For a fixed `(u, v)`, the left-tensor-sandwiched sum
`Σ_a (leftTensor A^v_a · K_{u,v,a}) · (leftTensor A^v_a · K_{u,v,a})ᴴ ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_left` in the Step 2 raw bound proof. -/
private lemma addInU_step2_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  set K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
      opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  set Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    leftTensor (ι₂ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ h : Polynomial params,
          (if h uv.2 = a then
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h)
          else 0)) = Pa a * K a := by
    intro a
    have hfilter :
        (∑ h : Polynomial params,
          (if h uv.2 = a then
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h)
          else 0)) =
            ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) := by
      rw [Finset.sum_filter]
    rw [hfilter, ← Finset.mul_sum]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hMh_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)).isHermitian.eq
    have hTh_herm : ∀ h : Polynomial params,
        (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hMh_herm, hTh_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, leftTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_mul_leftTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro h _
    exact opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)
      (T.outcome_pos h)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params,
      (Pa a * K a) * (Pa a * K a)ᴴ ≤ Pa a := by
    intro a
    have hexpand : (Pa a * K a) * (Pa a * K a)ᴴ = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [leftTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, leftTensor_one]
  calc
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0))ᴴ
        = ∑ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw `|Q₁ - Q₂| ≤ √(2δ)` bound for the add-in-u Step 2 Cauchy--Schwarz move.

Proves the paper's `eq:move-another` bound from
`references/ldt-paper/self_improvement.tex`, lines 279--297, as a no-sorry
producer.  The proof combines the algebraic alignment
`addInU_cs_chain_step2_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_left`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`. -/
lemma addInU_cs_chain_step2_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a h =>
      if h uv.2 = a then
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state (Aop uv) (Bop uv)) ≤ 2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rfl
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ h : Polynomial params, Cop uv a h) *
            (∑ h : Polynomial params, Cop uv a h)ᴴ) ≤ 1 :=
    fun uv => addInU_step2_C_contraction params strategy T uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_left
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Aop uv a)) -
        (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Bop uv a)) =
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (leftTensor (ι₂ := ι) Av *
            (opTensor Mh (T.outcome h) *
              (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av))) := by
    intro uv
    have hAvg : ∀ (X : Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a h, h uv.2 ≠ a → X a h = 0) →
        ∑ a : Fq params, ∑ h : Polynomial params, ev strategy.state (X a h) =
          ∑ h : Polynomial params, ev strategy.state (X (h uv.2) h) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro h _
      have hsingle : ∑ a : Fq params, ev strategy.state (X a h) =
          ev strategy.state (X (h uv.2) h) := by
        rw [Finset.sum_eq_single (h uv.2)]
        · intro a _ ha
          rw [hX a h (Ne.symm ha)]
          exact ev_zero strategy.state
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
      exact hsingle
    have hCA_zero : ∀ a h, h uv.2 ≠ a → Cop uv a h * Aop uv a = 0 := by
      intro a h ha
      simp [Cop, ha]
    have hCB_zero : ∀ a h, h uv.2 ≠ a → Cop uv a h * Bop uv a = 0 := by
      intro a h ha
      simp [Cop, ha]
    rw [hAvg (fun a h => Cop uv a h * Aop uv a) hCA_zero,
        hAvg (fun a h => Cop uv a h * Bop uv a) hCB_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _
    have hCop_at : Cop uv (h uv.2) h =
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)) *
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) := by
      simp [Cop]
    have hAop_at :
        Aop uv (h uv.2) = leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    have hBop_at :
        Bop uv (h uv.2) = rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    rw [hCop_at, hAop_at, hBop_at]
    rw [← ev_sub]
    congr 1
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Aop uv a)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Bop uv a)) =
      addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T := by
    rw [addInU_cs_chain_step2_diff_eq params strategy T]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  -- Wrap up: use abs_sub_comm to reverse the subtraction order
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-- Algebraic CS-alignment for the `Q₃ → Q₄` step.

Rewrites the difference `addInUCSChainQ3 - addInUCSChainQ4` in the exact form
appearing on the LHS of `eq:change-another` (paper lines 326–332):
the expectation of `(A^u_{h(u)} · H^u_h · (A^v_{h(v)} − A^u_{h(u)})) ⊗ T_h`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual operator Cauchy--Schwarz step
is provided by `add_in_u_cs_chain_q3_q4_factored_cs`. -/
lemma addInU_cs_chain_step4_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (opTensor (Au * Mh * (Av - Au)) (T.outcome h))) := by
  classical
  unfold addInUCSChainQ3 addInUCSChainQ4
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step4_pointwise_op_eq Au Av Mh (T.outcome h)


end MIPStarRE.LDT.SelfImprovement
