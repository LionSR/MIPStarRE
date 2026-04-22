import MIPStarRE.LDT.Commutativity.Transport.FullSlice

/-!
# Section 11 commutativity: auxiliary transport lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Paper `eq:evaluate-gcom-at-points` / `eq:gcom4-diff`
(`commutativity-G.tex` lines 339-354).

Schwartz-Zippel marginalization on the `x` variable: replacing the full
polynomial sum `∑_g G^x_g` by the point-evaluated sum `E_u ∑_a G^x_[g(u)=a]`
inside the ABA term costs at most `params.m · params.d / params.q`.

TODO(#361): the paper's `md/q` step is manifestly PSD on the tensor-form
comparison `BAB ⊗ A` (paper `eq:gcom4-diff`), but the current Lean stub is
phrased on the scalar `ABA ⊗ I` average.  So the direct positivity argument does
not apply verbatim here.  To close this theorem, we likely need either:
1. a bridge from `fullSliceABAAvg` / `evaluatedSliceABAAvg` to the paper's PSD
   tensor form; after that bridge, the old tactical step should still be to
   apply `polynomialAgreement_avg_le_mdq` (or directly
   `schwartzZippel_individualDegree`) to the off-diagonal collision term
   `1[g(u) = g'(u)]`, then bound the remaining fiber sum by the
   sub-measurement property of `G^x`, or
2. a genuinely new operator bound for the `ABA ⊗ I` difference.
-/
lemma fullSlice_scalar_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABAAvg params strategy family -
        evaluatedSliceABAAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Paper `eq:evaluate-gcom-at-points-part-dos`
(`commutativity-G.tex` lines 369-385).

Schwartz-Zippel marginalization on the `y` variable: replacing the full
polynomial sum `∑_h G^y_h` by the point-evaluated sum `E_v ∑_b G^y_[h(v)=b]`
inside the ABAB term costs at most `params.m · params.d / params.q`.  Symmetric
in structure to `fullSlice_scalar_marginalize_x`; the paper's difference-
expression label at line 379 is idiosyncratic, so we cite the enclosing
approximation statement.

TODO(#361): as for `fullSlice_scalar_marginalize_x`, the paper's
Schwartz-Zippel argument is manifestly PSD on the tensor-form `ABA ⊗ B`, while
this Lean stub is phrased on `ABAB ⊗ I`.  So the clean paper-faithful route is
to first bridge to the tensor form; after that bridge, one should again apply
`polynomialAgreement_avg_le_mdq` (or directly
`schwartzZippel_individualDegree`) to the off-diagonal collision term
`1[h(v) = h'(v)]`, then use the sub-measurement property of `G^y` to control
the remaining fiber sum.  Otherwise one needs a new large-fiber bound specific
to the scalar `ABAB ⊗ I` expression. -/
lemma fullSlice_scalar_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    |fullSliceABABAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q := by
  sorry

/-- Combined `closenessOfIP` chain on the evaluated side
(`commutativity-G.tex` lines 301, 334, 359-360, 394, 396).

Using `hEval` together with the six `closenessOfIP` steps in the paper:
two on the ABA side (line 301: `2√ζ`) and four on the ABAB side
(line 334: `√ζ`, lines 359-360: `2√ζ`, line 396: `√ζ`), plus the final
`closenessOfIP` with `hEval` as the `A≈B` input (line 394: `√ν_evaluation`),
the evaluated-slice scalar commutator is bounded by
`6√ζ + √(commDataProcessedGError)`.

The `hEval` hypothesis is bound into the fourth step via
`fullSlice_closenessOfIP_CAB_hEval` inputs; the first six steps use
`item:commuting-self-consistency` from `_hself`.

TODO(#361): two routes remain plausible here.
1. Finish the paper-faithful chain through a common tensor term, using
   evaluated-point self-consistency after evaluation, `switchSandwich`, and one
   final `closenessOfIP` application with `hEval`.
2. Use `evaluationSpecialization_sddErrorOp_eq` together with
   `evaluatedSliceCommutation_qSDDOp_avg_eq`, but then supply a robust large-`ν`
   trivial bound for the evaluated-slice products (for example an a priori
   estimate of the form `sddErrorOp ≤ 4`, equivalently
   `|evaluatedSliceABAAvg - evaluatedSliceABABAvg| ≤ 2`).
Either way, the missing bookkeeping is now concentrated in the evaluated-slice
layer, not in the pullback to full-slice questions. -/
lemma fullSlice_closenessOfIP_CAB_hEval
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hgamma_nonneg : 0 ≤ gamma) (_hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    |evaluatedSliceABAAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      6 * Real.sqrt zeta +
        Real.sqrt (commDataProcessedGError params gamma zeta) := by
  sorry


end MIPStarRE.LDT.Commutativity
