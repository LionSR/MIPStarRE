# Issue #930 session 45 commutativity-points discrepancy audit

Audit date: 2026-05-01

Base commit: `60cdbd17` (`origin/main` when this worktree was created)

Branch: `gpt55/session45-930-commutativitypoints-audit`

## Executive summary

I audited the already-formalized commutativity-of-points slice:

- `MIPStarRE/LDT/CommutativityPoints/Defs.lean`, `Approximation.lean`, `SharedHelpers/Core.lean`, `SharedHelpers/SharedLine.lean`, `BridgeTheorems/LiftBridges.lean`, `BridgeTheorems/DropBridges.lean`, `BridgeTheorems.lean`, and `Theorem.lean`;
- the source paper section `references/ldt-paper/commutativity-points.tex:5-44`;
- the blueprint entry `blueprint/src/chapter/ch08_commutativity.tex:5-48`.

This scope intentionally avoids the previous #930 slices: expansion/hypercube graph and global variance from session 42, and preliminaries from session 44.  It also avoids the active #996 tactic files and the chapter tracker cleanup worktrees.

Verdict: I found no undocumented mathematical discrepancy in this slice, and I did not create a new `docs/paper-gaps/` note.  The Lean statement proves the paper's point-commutativity theorem with the same average over independent points and the same error `32 * gamma * m`.  The proof route follows the paper's four replacement steps through a shared diagonal-line measurement, with explicit formal bookkeeping for parameterized diagonal lines and raw operator-family products.

## Validation

Targeted Lean checks in this worktree succeeded:

```text
lake build MIPStarRE.LDT.CommutativityPoints.Theorem
lake env lean MIPStarRE/LDT/CommutativityPoints/Approximation.lean
lake env lean MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean
lake env lean MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean
lake env lean MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean
lake env lean MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean
lake env lean MIPStarRE/LDT/CommutativityPoints/Theorem.lean
```

A scratch `#check`/`#print axioms` file was run for the audited public route.  For `sampledDiagonalLineApproximation_pointWithDiagonalLine`, `orderedLiftToMixedBridge`, `orderedLiftToLineBridge`, and `commutativityPoints`, `#print axioms` reported only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no audited declaration reported `sorryAx`.

A grep over `MIPStarRE/LDT/CommutativityPoints/**/*.lean` found no `sorry`, `axiom`, or `admit` in the checked slice.

## Finding 1: the theorem statement matches the paper and blueprint

The paper's theorem `thm:commutativity-points` states that for an `(eps, delta, gamma)`-good symmetric strategy for the `(m,q,d)` low individual degree test, on average over independent uniformly random points `u,v in F_q^m`,

```text
(A^u_a A^v_b) \otimes I \approx_{32 gamma m} (A^v_b A^u_a) \otimes I.
```

This is repeated in the blueprint at `thm:commutativity-points` with Lean declaration `MIPStarRE.LDT.CommutativityPoints.commutativityPoints`.

The Lean theorem has the same mathematical content.  Its conclusion is an `SDDOpRel` over `uniformDistribution (PointPairQuestion params)`, where `PointPairQuestion params` is the ordered pair type for points.  The left family `pointMeasurementProductLeft` has outcome `(a,b)` equal to `(A^u_a A^v_b) \otimes I`, and the right family `pointMeasurementProductRight` has outcome `(a,b)` equal to `(A^v_b A^u_a) \otimes I`.  The error parameter is `commutativityPointsError params gamma`, defined as `32 * gamma * (params.m : Error)` in `MIPStarRE/LDT/CommutativityPoints/Defs.lean:337-339`.

The extra Lean parameters are formal ambient data rather than a changed theorem: `FieldModel params.q` supplies the finite field `F_q`, and the finite Hilbert-space assumptions `[Fintype ι] [DecidableEq ι]` are the repository's matrix model of finite-dimensional quantum strategies.

## Finding 2: the diagonal-line approximation has the paper's `2 gamma m` loss

The paper first uses the diagonal-lines test to get the restricted diagonal-lines consistency loss `gamma * m`, then applies the conversion from consistency to state-dependent distance to obtain

```text
A^u_a \otimes I \approx_{2 gamma m} I \otimes L^ell_{[f(u)=a]}.
```

Lean implements the same two-step loss.  The intermediate error `restrictedDiagonalLinesConsistencyError params gamma` is `gamma * m`, and `pointDiagonalLineApproxError params gamma` is twice that value (`MIPStarRE/LDT/CommutativityPoints/Defs.lean:329-335`).  The lemma `sampledDiagonalLineConsistency` bounds the final restricted diagonal slice by using the average diagonal-test bound `hgood.diagonalLineTest` and nonnegativity of the individual slice errors (`MIPStarRE/LDT/CommutativityPoints/Approximation.lean:210-254`).  The lemma `sampledDiagonalLineApproximation` then applies the project's consistency-to-distance theorem, and `sampledDiagonalLineApproximation_pointWithDiagonalLine` transports the result to the line-plus-parameter distribution used in the commutativity proof (`MIPStarRE/LDT/CommutativityPoints/Approximation.lean:262-462`).

This matches `references/ldt-paper/commutativity-points.tex:14-25` and `blueprint/src/chapter/ch08_commutativity.tex:30-37`.

## Finding 3: the shared-line coupling preserves the paper's required marginals

The paper couples two independent random points `u,v` with a line `ell` containing both points, then uses only the fact that the `(u,ell)` and `(v,ell)` marginals are the same as in the one-point diagonal-line approximation.

Lean makes this coupling explicit for parameterized diagonal lines.  The definition `pointPairSharedDiagonalLineDistribution` samples a uniform point pair `(u,v)` and a uniform parameter `t`, then packages the diagonal line whose direction is `v-u` and whose parameterization visits `u` at `t` and `v` at `t+1` (`MIPStarRE/LDT/CommutativityPoints/Defs.lean:198-224`).  This exact construction is also recorded in the blueprint definition `def:point-pair-shared-diagonal-line-distribution` (`blueprint/src/chapter/ch08_commutativity.tex:8-14`).

The formal route proves the three marginal facts needed downstream:

- `avgOver_pointPairSharedDiagonalLine_sampled_pair` reindexes the shared-line average back to the uniform point-pair average (`MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean:210-226`);
- `sampledDiagonalLineApproximation_ignore_first` gives the approximation for the second sampled point and line parameter (`MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean:327-382`);
- `sampledDiagonalLineApproximation_ignore_second` gives the approximation for the first sampled point and line parameter (`MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean:384-439`).

This is slightly more explicit than the paper's prose because Lean represents diagonal lines with concrete affine parameterizations and uses transport covariance for rebasing.  That design choice is documented in `docs/diagonal-line-refactor.md`, and the theorem statement has no line in its conclusion.  I therefore count this as faithful formal bookkeeping, not a paper discrepancy.

## Finding 4: the four bridge steps match the paper proof route

The paper's calculation routes

```text
(A^u_a A^v_b) \otimes I
  -> A^u_a \otimes L^ell_{[f(v)=b]}
  -> I \otimes (L^ell_{[f(v)=b]} L^ell_{[f(u)=a]})
  =  I \otimes (L^ell_{[f(u)=a]} L^ell_{[f(v)=b]})
  -> A^v_b \otimes L^ell_{[f(u)=a]}
  -> (A^v_b A^u_a) \otimes I.
```

Lean uses the same route, split into bridge lemmas over raw operator families:

- `orderedLiftToMixedBridge` proves the first replacement step (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean:23-130`);
- `orderedLiftToLineBridge` proves the second replacement step (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/LiftBridges.lean:133-255`);
- `diagonalLineProduct_outcome_swap` proves the exact middle swap using projectivity of the postprocessed diagonal-line measurement (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean:22-40`);
- `orderedDropFromLineBridge` and `reversedDropToPointsBridge` prove the two return steps (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean:161-294`).

The use of `SDDOpRel` rather than `SDDRel` is intentional and mathematically appropriate: products such as `A^u_a A^v_b` are arbitrary operator families and need not themselves be submeasurement effects before commutativity is proved.

## Finding 5: the final constant is the paper's `32 gamma m`

Each replacement step uses `delta = pointDiagonalLineApproxError params gamma = 2 gamma m`.  The project triangle inequality for state-dependent distance contributes a factor `2` when composing two bounds.  Lean therefore combines the first two steps into `2 * (delta + delta)`, combines the last two steps into the same bound, and then combines those two halves into

```text
2 * (2 * (delta + delta) + 2 * (delta + delta)) = 32 gamma m.
```

This balanced composition is implemented in `commutativityPoints` (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean:308-370`) and then reindexed from the shared-line distribution back to the independent point-pair distribution (`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean:371-396`).  The constant matches the paper theorem and the blueprint statement.

## Boundary of this audit

I did not re-audit downstream uses in `MIPStarRE/LDT/Commutativity/**`, the `commutativity-G.tex` section, the pasting chapter, active #996 tactic files, or the chapter tracker cleanup branches.  This negative finding is limited to the formalized `CommutativityPoints` slice and its direct paper/blueprint counterpart.
