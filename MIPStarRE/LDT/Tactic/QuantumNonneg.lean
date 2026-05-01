import MIPStarRE.LDT.Basic.SubMeasurementFamilies

/-!
# Conservative quantum nonnegativity tactic

This file provides the opt-in tactic `quantum_nonneg` for recurring LDT goals of
shape `0 ≤ ...` involving positive semidefinite effects, tensor placements, and
expectation values.  The tactic intentionally does **not** register any global
`@[positivity]` extensions: callers must import this module and invoke the tactic
at the proof sites where they want the controlled automation.

The search is deliberately shallow.  It tries the local wrappers used throughout
the LDT quantum layer, decomposes finite sums and nonnegative scalar multiples,
and leaves scalar side goals to `positivity`/`nlinarith`.  Tensor-placement
products are typically rewritten explicitly with
`leftTensor_mul_rightTensor_eq_opTensor` before invoking the tactic; keeping that
rewrite visible avoids broad backtracking in the tactic itself.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/--
`quantum_nonneg` proves small, canonical nonnegativity goals in the LDT quantum
layer.

It is meant for goals built from:
* positive semidefinite expectation lemmas (`ev_adjoint_self_nonneg`,
  `ev_nonneg_of_psd`),
* tensor positivity (`opTensor_nonneg`, `leftTensor_nonneg`,
  `rightTensor_nonneg`),
* Hermitian sandwich positivity (`MIPStarRE.Quantum.sandwich_nonneg`),
* finite sums and nonnegative scalar multiples, and
* scalar leaves discharged by `positivity`/`nlinarith`.

This is a conservative tactic macro rather than global automation; it should be
used explicitly at representative proof sites and extended only after measuring
performance on the affected files.  For goals containing
`leftTensor _ * rightTensor _`, first rewrite with
`leftTensor_mul_rightTensor_eq_opTensor`, then call `quantum_nonneg`.
-/
syntax (name := quantumNonneg) "quantum_nonneg" : tactic

macro_rules
  | `(tactic| quantum_nonneg) => `(tactic|
    first
    | assumption
    | apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; quantum_nonneg
    | exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _
    | exact star_mul_self_nonneg _
    | apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> quantum_nonneg
    | apply _root_.MIPStarRE.LDT.leftTensor_nonneg; quantum_nonneg
    | apply _root_.MIPStarRE.LDT.rightTensor_nonneg; quantum_nonneg
    | apply _root_.MIPStarRE.Quantum.sandwich_nonneg
      · quantum_nonneg
      · first
        | assumption
        | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _
        | simp [*]
    | apply Finset.sum_nonneg; intro _ _; quantum_nonneg
    | apply smul_nonneg <;> quantum_nonneg
    | exact zero_le_one
    | exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _
    | exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _
    | positivity
    | nlinarith)
