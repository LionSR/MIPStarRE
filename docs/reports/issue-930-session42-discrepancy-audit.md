# Issue #930 session 42 discrepancy audit

Audit date: 2026-05-01

Base commit: `8ad516b7` (`origin/main` when the worktree was created)

Branch: `gpt55/session42-930-discrepancy-audit`

## Executive summary

I audited a non-overlapping slice of already-checked LDT statements in the
expansion and global-variance chapters:

- `MIPStarRE/LDT/ExpansionHypercubeGraph/**` against
  `references/ldt-paper/expansion.tex:5-267` and
  `blueprint/src/chapter/ch05_expansion.tex`;
- `MIPStarRE/LDT/GlobalVariance/**` against
  `references/ldt-paper/expansion.tex:269-353` and
  `blueprint/src/chapter/ch06_variance.tex`.

This scope avoids the active proof/refactor PRs around `MainTheorem`,
Distribution, commutativity/full-slice transport, orthonormalization, and
projectivization.

Verdict: I found no undocumented mathematical discrepancy in this slice that
requires a new `docs/paper-gaps/` note.  The checked Lean statements preserve the
paper's constants `md/q`, `24(ε + δ + md/q)`, `24m(ε + δ + md/q)`, and the
local-to-global factor `m`.  The two non-paper-literal aspects I found are
already visible in source comments or are proof-route hygiene rather than a
paper gap:

1. `laplacianRewrite` is intentionally not a formal proof of the paper's
   edge-difference formula; the blueprint explicitly withholds `\leanok` from
   `prop:laplacian-rewrite` and records this Lean-local gap.
2. `globalVarianceOfPoints` is a legacy wrapper with conclusion-shaped inputs,
   but the paper-faithful route is present through the stricter lemmas
   `localVarianceTransportChainBound` and
   `globalVarianceOfPointsFromTransportChainBound`.  This is a blueprint mapping
   hygiene point, not a new paper discrepancy.

No follow-up issue was opened: the only suspicious items were either confirmed as
already documented, already covered by active blueprint-sync work, or harmless
source typos such as `\F_q^n` where the surrounding statement says `\F_q^m`.

## Validation

Targeted Lean checks in the worktree succeeded:

```text
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean
lake env lean MIPStarRE/LDT/GlobalVariance/Theorems.lean
```

For the audited public routes, `#print axioms` reported only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`; no audited theorem
reported `sorryAx`.

A grep over the audited directories found no `sorry`, `axiom`, or `admit` in
`MIPStarRE/LDT/ExpansionHypercubeGraph/**` or `MIPStarRE/LDT/GlobalVariance/**`.

## Finding 1: the hypercube graph and variance statements match the paper

The paper defines the graph on `\F_q^m`, samples an edge by choosing
`u`, a coordinate `i`, and a field element `x`, and sets
`v = u + x e_i` (`references/ldt-paper/expansion.tex:5-10`).  The blueprint has
the same sampling rule in `def:rerandomize-coord` and `def:hypercube-graph`
(`blueprint/src/chapter/ch05_expansion.tex:8-22`).  Lean represents the same
sampler by `rerandomizeCoord` and the same edge predicate by `IsHypercubeEdge`.

The adjacency and Laplacian definitions also agree.  The paper sets
`K = E_{(u,v) \sim C} |u><v|` and `L = (1/M)I - K`, where `M = q^m`
(`references/ldt-paper/expansion.tex:16-25`).  Lean's concrete definitions use
`matrixAdjacencyOperator` and
`matrixLaplacianOperator = (hypercubeVertexCount params)⁻¹ • I - K`
(`MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean:167-197`).

The local and global variances match the paper's definitions, including the
factor `1/2` and the two distributions.  The paper explicitly allows the state
`|ψ>` to be not necessarily normalized in this section
(`references/ldt-paper/expansion.tex:113-127`).  Lean's `localVariance` averages
over `rerandomizeCoord`, and `globalVariance` averages over
`independentPointPair`, both with the same `1/2` factor
(`MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean:210-222`).  Thus this
slice has no hidden normalization strengthening.

## Finding 2: `laplacianRewrite` is a documented non-result, not a silent repair

The paper proves the edge-difference formula

```text
L = (1/2) E_{(u,v)~C} (|u> - |v>)(<u| - <v|)
```

in `references/ldt-paper/expansion.tex:27-46`.  The blueprint states this as
`prop:laplacian-rewrite`, but it deliberately does not mark it `\leanok`.
The local comment says that the current Lean declaration only proves the
trivial identity `laplacian = laplacianDifferenceForm`, because
`laplacianDifferenceForm` is currently a synonym for `laplacian`
(`blueprint/src/chapter/ch05_expansion.tex:39-47`).

Lean confirms this: `laplacianRewrite` is exactly

```lean
laplacian params = laplacianDifferenceForm params
```

and its proof is `rfl` (`MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean:248-251`).
This is not an undocumented mathematical discrepancy.  The blueprint already
prevents the dependency graph from claiming the paper's edge-difference formula
as checked.

The downstream formal proofs of `localRewrite`, `globalRewrite`, and
`localToGlobal` do not silently use this unproved formula.  They proceed through
matrix closed forms and the spectral-gap operator inequality
(`MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean:221-307`).  This is
an alternate formal route, but the public mathematical conclusions are the same
as the paper's `lem:local-rewrite`, `lem:global-rewrite`, and
`lem:local-to-global`.

## Finding 3: the local-to-global constant is unchanged

The paper proves

```text
Var_global(A, ψ) ≤ m · Var_local(A, ψ)
```

in `references/ldt-paper/expansion.tex:135-139` and
`references/ldt-paper/expansion.tex:241-267`.  The blueprint repeats exactly this
constant in `lem:local-to-global`
(`blueprint/src/chapter/ch05_expansion.tex:306-314`).

Lean's public theorem is

```lean
globalVariance params A ψ ≤ params.m * localVariance params A ψ
```

(`MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean:255-265`).  No
extra commutativity, normalization, or boundedness hypothesis is added at the
public theorem level.  The formal proof uses the matrix-level spectral-gap
inequality and closed-form trace identities; it does not widen the constant.

## Finding 4: the global-variance-of-points constants match, with a documented residual

The paper's three statements in the global-variance section are:

- `lem:generalize-b`, with error `md/q`
  (`references/ldt-paper/expansion.tex:273-290`);
- `lem:local-variance-of-points`, with error
  `24(ε + δ + md/q)` (`references/ldt-paper/expansion.tex:292-321`);
- `lem:global-variance-of-points`, with error
  `24m(ε + δ + md/q)` (`references/ldt-paper/expansion.tex:325-353`).

The blueprint states the same three constants in
`blueprint/src/chapter/ch06_variance.tex:8-70`.

Lean uses the corresponding scalar definitions:

```lean
generalizeBError params = (params.m * params.d) / params.q
localVarianceOfPointsError params eps delta =
  24 * (eps + delta + generalizeBError params)
globalVarianceOfPointsError params eps delta =
  24 * params.m * (eps + delta + generalizeBError params)
```

These are at `MIPStarRE/LDT/GlobalVariance/Defs/Families.lean:416-441`.

The formalization also records the exact post-triangle residual for the six-step
chain:

```lean
localVarianceTransportChainError params eps delta =
  6 * (4 * eps + 4 * delta + 2 * generalizeBError params)
```

The comments identify this as the result of applying the six-term triangle
inequality to the paper's errors `2δ`, `2ε`, `md/q`, `md/q`, `2ε`, and `2δ`
(`MIPStarRE/LDT/GlobalVariance/Defs/Families.lean:419-431`).  The scalar lemma
`localVarianceTransportChainError_le_localVarianceOfPointsError` then absorbs
this residual into the displayed `24(ε + δ + md/q)` slack using nonnegativity
from `strategy.IsGood`
(`MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain.lean:574-595`).

This is a useful formal bookkeeping refinement, not a widened paper constant.
The public displayed errors remain the paper's errors.

## Finding 5: `generalize-b` is internally discharged for the strategy state

The legacy theorem `generalizeB` accepts a pointwise norm bound as an explicit
input.  This is not the paper-faithful route by itself.  The formalization also
contains `generalizeBFromSchwartzZippel`, which discharges that pointwise bound
from the collision residual and the line-restriction Schwartz--Zippel estimate
(`MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean:596-645`).

The extra `FieldModel params.q` requirement in the Lean signatures is just the
formal version of the paper's ambient field `\F_q`.  The `strategy.IsGood`
hypothesis is retained in `generalizeBFromSchwartzZippel` to match the paper
context, although the algebraic estimate itself does not use `ε`, `δ`, or `γ`.
This is documented in the Lean comment
(`MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean:631-635`) and is
not a strengthened mathematical hypothesis.

## Finding 6: `globalVarianceOfPoints` is legacy API, but the stricter route is present

One mild blueprint-sync caveat remains.  The blueprint entry for
`lem:global-variance-of-points` links to `MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints`
(`blueprint/src/chapter/ch06_variance.tex:60-62`).  That declaration is a legacy
wrapper with explicit conclusion-shaped inputs for the local and global
pointwise bounds (`MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean:308-345`).

The stricter, strategy-state route is already present:

- `localVarianceTransportChainBound` proves the paper's six-step edge transport
  on the native hypercube-edge sampler
  (`MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain.lean:548-572`);
- `localVarianceOfPointsFromTransportChainBound` absorbs the residual into
  `24(ε + δ + md/q)`
  (`MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean:262-286`);
- `globalVarianceOfPointsFromTransportChainBound` applies the local-to-global
  transfer to obtain the global statement
  (`MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean:288-306`).

The blueprint already lists `globalVarianceOfPointsFromTransportChainBound` in
the `\lean{...}` block for `lem:local-variance-of-points`
(`blueprint/src/chapter/ch06_variance.tex:24-26`).  Thus the formal route exists,
but the declaration is attached to the preceding blueprint item rather than to
the global-variance item.  I treated this as blueprint mapping hygiene, not a
new issue #930 paper discrepancy, especially because the global-variance proof
block is not marked `\leanok` (`blueprint/src/chapter/ch06_variance.tex:72-104`)
and active blueprint-sync PRs are already open.

## Minor source typos observed

The paper proof of `lem:global-rewrite` and the proof of
`lem:global-variance-of-points` each have an apparent `\F_q^n` where the
surrounding section and theorem statement use `\F_q^m`
(`references/ldt-paper/expansion.tex:211` and
`references/ldt-paper/expansion.tex:345`).  The blueprint and Lean use `m`.
This is a harmless notation typo, not a change in hypotheses, constants, or
conclusions.

## Conclusion

This audit did not find a confirmed undocumented paper discrepancy in the
non-overlapping expansion/global-variance slice.  The main formal deviations are
visible and local:

- the paper-faithful Laplacian edge-difference formula is not yet formalized and
  is not claimed as `\leanok`;
- the variance proofs use closed-form matrix identities instead of that formula;
- the global-variance API still carries some legacy wrappers, but the stricter
  paper-route lemmas are present and checked.

No Lean statements were edited, and no paper-gap note was added.
