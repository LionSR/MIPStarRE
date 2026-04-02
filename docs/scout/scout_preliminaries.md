## consSubMeas_diagonalControl (line 260)
- Paper reference: `prop:cons-sub-meas`
- Paper proof strategy: This is the first approximation in `eq:closeness5`. The paper bounds `E_x Σ_a ||(A_a^x ⊗ I - A_a^x ⊗ B_a^x)|ψ>||^2` by replacing the square with the operator itself, rewriting it as the off-diagonal consistency mass, and then applying the hypothesis `A_a^x ⊗ I \simeq_γ I ⊗ B_a^x`.
- Key Mathlib lemmas needed: `avgOver_mono`, `sq_le_self`, `ev_mono`, `Measurement.outcome_le_one`, `SubMeas.outcome_le_one`, `sandwich_nonneg`, `sandwich_mono`
- Estimated difficulty: hard
- Estimated Lean proof lines: 45
- Blockers: The current Lean statement is only a surrogate for the paper step. `diagonalSandwichFamily` uses `A_a B_a A_a`, but the paper step is about `A_a ⊗ I` versus `A_a ⊗ B_a`. The present formalization has no explicit left/right tensor structure or commutation hypothesis connecting these, so the paper proof does not port directly.

## consSubMeas_sandwichControl (line 272)
- Paper reference: `prop:cons-sub-meas`
- Paper proof strategy: This is the second approximation in `eq:closeness5`. The paper compares `A_a^x ⊗ B_a^x` with `A^x ⊗ B_a^x` by expanding the difference as `((A^x - A_a^x) ⊗ B_a^x)|ψ>` and bounding it by the same consistency error.
- Key Mathlib lemmas needed: `avgOver_mono`, `sq_le_self`, `ev_mono`, `ev_sum`, `ev_sub`, `Measurement.total_eq_one`, `sandwich_nonneg`, `sandwich_mono`
- Estimated difficulty: hard
- Estimated Lean proof lines: 40
- Blockers: The same modeling mismatch appears here. `totalSandwichFamily` is `A_a (Σ_b B_b) A_a`, which reduces to `A_a^2` because `B` is a measurement, while the paper compares against `A^x ⊗ B_a^x`. Without restoring the bipartite/tensor formulation, the proof is not a direct transcription of the paper.

## switchSandwich_leftTransfer (line 327)
- Paper reference: `prop:switch-sandwich`
- Paper proof strategy: The paper proves the first approximation in two Cauchy-Schwarz steps. First it shifts the rightmost `A_a^x` from `A_a^x B A_a^x ⊗ I` to `A_a^x B ⊗ A_a^x`, then it uses projectivity again to replace that with `B ⊗ A_a^x`; each step costs `√δ`, giving `2√δ` total.
- Key Mathlib lemmas needed: `ev_cauchy_schwarz`, `Matrix.mul_kronecker_mul`, `leftTensor_finset_sum`, projectivity lemmas for `(A q).proj a`, absolute-value triangle inequality on `ℝ`
- Estimated difficulty: hard
- Estimated Lean proof lines: 70
- Blockers: The current hypothesis `BipartiteSDDRel ψ 𝒟 Alifted Alifted δ` is just a self-distance bound on one family and does not relate `Alifted` to `A` at all, so it cannot justify the switches used in the paper. Also, the current expectations are defined using `(A q).toSubMeas.total`, whereas the paper proposition is a sum over the individual projectors `A_a^x`; that is a second statement mismatch.

## switchSandwich_rightTransfer (line 341)
- Paper reference: `prop:switch-sandwich`
- Paper proof strategy: This is the second approximation in `eq:switch-sandwich`. The paper applies Cauchy-Schwarz once to compare `E_x Σ_a <ψ| B ⊗ A_a^x |ψ>` with `E_x Σ_a <ψ| BA_a^x ⊗ I |ψ>`, then uses projectivity to collapse the double sum and recover the `δ` bound under the square root.
- Key Mathlib lemmas needed: `ev_cauchy_schwarz`, `Matrix.mul_kronecker_mul`, `leftTensor_finset_sum`, `rightTensor_finset_sum`, projective-total identities like `A.total * A.outcome a = A.outcome a`
- Estimated difficulty: hard
- Estimated Lean proof lines: 60
- Blockers: The same two blockers as above remain: the hypothesis does not connect `Alifted` to `A`, and the current expectation definitions use total operators instead of the paper’s outcomewise sums. There are useful private lemmas in `MIPStarRE/LDT/Pasting/Sandwich.lean` about projective totals, but they are not currently reusable here.

## completenessTransfer_core (line 374)
- Paper reference: `prop:completeness-transfer-projective-P`
- Paper proof strategy: The paper rewrites the mass of `P` as a sum of squares using projectivity, then applies the “easy approx from approx-delta” argument twice to replace one `P_a^x` by `A_a^x` and then the other. Finally it uses `(A_a^x)^2 ≤ A_a^x` to bound the result by the mass of `A`.
- Key Mathlib lemmas needed: `ev_cauchy_schwarz` or a local helper formalizing `prop:easy-approx-from-approx-delta`, `avgOver_mono`, `ev_sum`, `ev_mono`, `sq_le_self`, `(P q).proj a`
- Estimated difficulty: medium
- Estimated Lean proof lines: 30
- Blockers: No fundamental statement mismatch. The main missing ingredient is a reusable local lemma matching paper Proposition `prop:easy-approx-from-approx-delta`; without it, the proof becomes a pair of ad hoc Cauchy-Schwarz calculations.

## closenessAfterCompletion_core (line 450)
- Paper reference: `prop:completing-to-measurement` (uses auxiliary `prop:cool-prop`)
- Paper proof strategy: The paper first compares `A` to the completion `C` by splitting through `B` and using the two-step vector-squared triangle inequality. The extra term comes from the residual `I - B`, and that residual is bounded by showing `Σ_a <ψ|B_a^2|ψ>` is close to `Σ_a <ψ|A_a^2|ψ>`, then invoking the auxiliary `prop:cool-prop` to lower-bound the latter by `1 - ζ`.
- Key Mathlib lemmas needed: `stateDependentDistanceRel_triangle`, `ev_cauchy_schwarz` or a local easy-approx lemma, `sq_le_self`, `ev_sum`, `completeAtOutcome` expansion, `avgOver` simplifications for `uniformDistribution Unit`
- Estimated difficulty: hard
- Estimated Lean proof lines: 55
- Blockers: The final proposition itself is aligned with the paper, but the proof depends on the auxiliary paper lemma `prop:cool-prop`, which is not formalized separately in Lean. There will also be some custom bookkeeping around `completeAtOutcome` and the residual operator `1 - B.total`. The `PermInvState` hypothesis is not a blocker here because it is currently an empty structure in this codebase.
