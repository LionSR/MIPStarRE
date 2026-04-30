---
title: "Preliminaries sorry-site scouting"
date: 2026-04-02
purpose: >
  Scouting report for preliminaries sorry sites and their paper proof strategies.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

## consSubMeas_diagonalControl (line 260)
- Paper reference: `prop:cons-sub-meas`
- Paper proof strategy: This is the first approximation in `eq:closeness5`. The paper bounds `E_x Σ_a ||(A_a^x ⊗ I - A_a^x ⊗ B_a^x)|ψ>||^2` by replacing the square with the operator itself, rewriting it as the off-diagonal consistency mass, and then applying the hypothesis `A_a^x ⊗ I \simeq_γ I ⊗ B_a^x`.
- Key Mathlib lemmas needed: `avgOver_mono`, `sq_le_self`, `ev_mono`, `Measurement.outcome_le_one`, `SubMeas.outcome_le_one`, `sandwich_nonneg`, `sandwich_mono`
- Estimated difficulty: hard
- Estimated Lean proof lines: 45
- Blockers: **RESOLVED (2026-04-30, #936).** The current `diagonalSandwichFamily A B` is `leftTensor(A_a) * rightTensor(B_a)` = `A_a ⊗ B_a`, which faithfully matches the paper's middle term. The tensor formulation has been fully integrated; see `MIPStarRE/LDT/Preliminaries/Defs.lean:68`. The proof in `MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean` uses the correct bipartite consistency reduction.

## consSubMeas_sandwichControl (line 272)
- Paper reference: `prop:cons-sub-meas`
- Paper proof strategy: This is the second approximation in `eq:closeness5`. The paper compares `A_a^x ⊗ B_a^x` with `A^x ⊗ B_a^x` by expanding the difference as `((A^x - A_a^x) ⊗ B_a^x)|ψ>` and bounding it by the same consistency error.
- Key Mathlib lemmas needed: `avgOver_mono`, `sq_le_self`, `ev_mono`, `ev_sum`, `ev_sub`, `Measurement.total_eq_one`, `sandwich_nonneg`, `sandwich_mono`
- Estimated difficulty: hard
- Estimated Lean proof lines: 40
- Blockers: **RESOLVED (2026-04-30, #936).** The current `totalSandwichFamily A B` is `leftTensor(A_total) * rightTensor(B_a)` = `A ⊗ B_a`, which faithfully matches the paper's right term. The tensor structure is fully in place; see `MIPStarRE/LDT/Preliminaries/Defs.lean:147`.

## switchSandwich_leftTransfer (line 327)
- Paper reference: `prop:switch-sandwich`
- Paper proof strategy: The paper proves the first approximation in two Cauchy-Schwarz steps. First it shifts the rightmost `A_a^x` from `A_a^x B A_a^x ⊗ I` to `A_a^x B ⊗ A_a^x`, then it uses projectivity again to replace that with `B ⊗ A_a^x`; each step costs `√δ`, giving `2√δ` total.
- Key Mathlib lemmas needed: `ev_cauchy_schwarz`, `Matrix.mul_kronecker_mul`, `leftTensor_finset_sum`, projectivity lemmas for `(A q).proj a`, absolute-value triangle inequality on `ℝ`
- Estimated difficulty: hard
- Estimated Lean proof lines: 70
- Blockers: **RESOLVED (2026-04-30, #936).** `BipartiteSDDRel` encodes `leftRightSquaredDistanceBound` which says `sddError ψ 𝒟 (liftLeft A) (liftRight A) ≤ δ`, i.e. `A_a^x ⊗ I ≈_δ I ⊗ A_a^x` — exactly the paper's hypothesis `eq:Aapproxd`. The `leftSandwichExpectation`, `middleSandwichExpectation`, and `rightSandwichExpectation` definitions use `leftTensor`/`rightTensor` per paper, and the proof uses outcomewise projectors via `A_q.outcome a`. See `MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/LeftTransfer.lean` (`switchSandwich_leftTransfer`).

## switchSandwich_rightTransfer (line 341)
- Paper reference: `prop:switch-sandwich`
- Paper proof strategy: This is the second approximation in `eq:switch-sandwich`. The paper applies Cauchy-Schwarz once to compare `E_x Σ_a <ψ| B ⊗ A_a^x |ψ>` with `E_x Σ_a <ψ| BA_a^x ⊗ I |ψ>`, then uses projectivity to collapse the double sum and recover the `δ` bound under the square root.
- Key Mathlib lemmas needed: `ev_cauchy_schwarz`, `Matrix.mul_kronecker_mul`, `leftTensor_finset_sum`, `rightTensor_finset_sum`, projective-total identities like `A.total * A.outcome a = A.outcome a`
- Estimated difficulty: hard
- Estimated Lean proof lines: 60
- Blockers: **RESOLVED (2026-04-30, #936).** `rightSandwichExpectation` correctly uses `leftTensor(B * A_q.outcome a)` = `B A_a^x ⊗ I`. The proof uses both outcomewise projectors and total-projector identities (`projSubMeas_total_proj`) that are now public lemmas in `MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean`. See `MIPStarRE/LDT/Preliminaries/SwitchSandwichMain/RightTransfer.lean` (`switchSandwich_rightTransfer`).

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
