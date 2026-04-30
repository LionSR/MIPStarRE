# Decision Record: Scalar-vs-Tensor Architecture for `fullSliceCommutation`

- **Issue**: [#713](https://github.com/LionSR/MIPStarRE/issues/713)
- **Date**: 2026-04-29
- **Status**: Accepted (Option 3 — Hybrid)

## Context

The `fullSliceCommutation` step inside `thm:com-main` (the main commutativity theorem
for $G$) requires comparing full-polynomial measurement families with their
evaluated-at-points counterparts.  The paper's proof (commutativity-G.tex,
lines~332–401) uses three kinds of mathematical object:

1. **Scalar quarkic expectations** like
   $\mathbb{E}_{\mathbf{x},\mathbf{y}} \sum_{g,h}
     \langle\psi|\, G^{\mathbf{x}}_g G^{\mathbf{y}}_h G^{\mathbf{x}}_g G^{\mathbf{y}}_h
     \otimes I \,|\psi\rangle$.
   These are the endpoints that appear in the commutation-difference expansion
   (paper `eq:gcomterms`).

2. **Manifestly-PSD tensor expectations** like
   $\mathbb{E}_{\mathbf{x},\mathbf{y}} \sum_{g,h}
     \langle\psi|\, G^{\mathbf{y}}_h G^{\mathbf{x}}_g G^{\mathbf{y}}_h \otimes
     G^{\mathbf{x}}_g \,|\psi\rangle$.
   These appear inside the proof at `eq:gcom4` and are needed because the
   Schwartz–Zippel collision argument (postprocessing a polynomial family by a
   random evaluation point) requires a positive-semidefinite tensor form to bound
   the residual by $md/q$.

3. **Operator-level SDD relations** (`SDDOpRel` / `SDDRel`) that carry an explicit
   error bound at each step, used by `closenessOfIP` (paper
   `prop:closeness-of-ip`) to transport approximation guarantees between
   different operational forms.

The question: how should the formalization expose these objects in the public API?

## Options Considered

### Option 1 — Pure Scalar

Keep **all** public API as scalar expectations.  The commutation difference would
be expressed as
```
|fullSliceABABAvg - evaluatedSliceABABAvg| ≤ ...
```
where `fullSliceABABAvg` and `evaluatedSliceABABAvg` are real numbers (type
`Error`).  Internally one would still need tensor forms for
`closenessOfIP` and Schwartz–Zippel, but they would be reconstructed on-the-fly.

**Pro**: The paper's displayed endpoint equations (e.g. `eq:gcomterms`) are
scalar, so the public API matches the paper's display exactly.
**Con**: Every call to `closenessOfIP` and every Schwartz–Zippel step would
require an ad-hoc lift from scalar to tensor, duplicating the same bridge
reasoning.  The scalar form loses the PSD structure that makes the
Schwartz–Zippel bound mathematically valid, so the proof would need to constantly
switch representations.

### Option 2 — Pure Tensor (Operator-level SDD)

Keep **all** public API as `SDDOpRel` relations on operator families.  The
commutation difference would be
```
SDDOpRel state dist familyA familyB error
```
where `familyA` and `familyB` carry the full bipartite operator structure
(left-×-right register).

**Pro**: The `closenessOfIP` machinery and Schwartz–Zippel PSD argument apply
directly; no scalar/tensor bridges needed.
**Con**: The public API no longer matches the paper's displayed scalar equations.
The final `comMain` theorem would need to produce an operator-level conclusion and
then translate it back to a scalar bound for the wider soundness cascade, which
adds a top-level translation step that isn't in the paper.  The operator-level API
is also more verbose for downstream consumers that only need the scalar estimate.

### Option 3 — Hybrid (Scalar Public API + Internal Tensor Machinery)

Keep **public** endpoints as scalar averages but use **private** tensor-form
intermediates for the load-bearing internal steps (`closenessOfIP`,
Schwartz–Zippel PSD, collision marginalization).  The public lemmas are pure
scalar inequalities:
```
|fullSliceABAAvg - evaluatedSliceABAAvg| ≤ 4·√ζ
|fullSliceABABAvg - evaluatedSliceABABAvg| ≤ 2·md/q + 4·√ζ
```
Internally, a chain of scalar-to-tensor bridges (each costing `√ζ`) moves from
the scalar endpoints to the tensor forms, runs the heavy operator-level
arguments, and then moves back.

**Pro**: The public API remains a faithful scalar counterpart of the paper's
`eq:gcomterms` expansion.  The tensor machinery is encapsulated as private
lemmas, so maintainers of downstream theorems see only scalar inequalities.  The
extra `2√ζ` overhead from the scalar/tensor bridges is bounded by the existing
error parameters (a constant-factor change in `ζ` does not affect the asymptotic
soundness cascade).

**Con**: The private tensor layer is substantial (~1000 lines in
`Transport/FullSlice.lean` for collision marginalization alone, plus ~700 lines
in `Main/Auxiliary.lean` for the bridge chain).  A contributor reading only the
public lemmas may be surprised that the proof pays an extra `2√ζ` beyond what the
paper's inline computation suggests; this overhead is documented in
[docs/paper-gaps/issue-713-scalar-tensor-decision.tex](../paper-gaps/issue-713-scalar-tensor-decision.tex).

## Decision

**Option 3 (Hybrid)** was chosen.  The scalar public API keeps the
`thm:com-main` interface paper-faithful, while the private tensor layer contains
the mathematically delicate operator-level arguments and keeps them out of the
downstream dependency surface.

## Architecture Map: Scalar Public API

| Quantity | Lean Declaration | Location | Paper Anchor |
|---|---|---|---|
| Full-slice ABA scalar average | `fullSliceABAAvg` | `Transport/FullSlice.lean` | `eq:gcomterms` first term |
| Full-slice ABAB scalar average | `fullSliceABABAvg` | `Transport/FullSlice.lean` | `eq:gcomterms` second term |
| Evaluated-slice ABA scalar average | `evaluatedSliceABAAvg` | `Transport/FullSlice.lean` | evaluated analogue |
| Evaluated-slice ABAB scalar average | `evaluatedSliceABABAvg` | `Transport/FullSlice.lean` | evaluated analogue |
| First-term scalar transport | `fullSlice_scalar_marginalize_x` | `Main/Auxiliary.lean` | paper lines 295–305 |
| Second-term scalar transport | `fullSlice_scalar_marginalize_y` | `Main/Auxiliary.lean` | paper lines 332–401 |

## Architecture Map: Internal Tensor Machinery

| Quantity | Lean Declaration | Location | Paper Anchor |
|---|---|---|---|
| Full BAB⊗A tensor average | `fullSliceBABAtensorAvg` (private) | `Transport/FullSlice.lean` | `eq:gcom4` RHS |
| Full ABA⊗B tensor average | `fullSliceABABtensorAvg` (private) | `Transport/FullSlice.lean` | paper line 387 |
| X-eval BAB⊗A tensor avg | `xEvaluatedSliceBABAtensorAvg` | `Transport/FullSlice.lean` | line 359 bridge |
| X-eval ABA⊗B tensor avg | `xEvaluatedFullSliceABABtensorAvg` | `Transport/FullSlice.lean` | line 360 bridge |
| Eval ABA⊗B tensor avg | `evaluatedSliceABABtensorAvg` | `Transport/FullSlice.lean` | `eq:evaluate-gcom...-dos` |

## Architecture Map: Scalar↔Tensor Bridge Chain

The chain in `Main/Auxiliary.lean` proves the two public scalar transport lemmas
by composing the following bridges:

```
fullSliceABABAvg                                 (scalar)
  → fullSliceBABAtensorAvg          (tensor, √ζ)   [eq:gcom4]
  → xEvaluatedSliceBABAtensorAvg    (tensor, md/q)  [eq:gcom4-diff]
  → xEvaluatedFullSliceABABAvg      (scalar, √ζ)    [line 359]
  → xEvaluatedFullSliceABABtensorAvg(tensor, √ζ)    [line 360]
  → evaluatedSliceABABtensorAvg     (tensor, md/q)  [y-collision tail]
  → evaluatedSliceABABAvg           (scalar, √ζ)    [y-eval bridge]
```

The first-term (ABA, cubic) does not use Schwartz–Zippel; both full and evaluated
cubic endpoints are compared to a common `G ⊗ G` switch-sandwich center, costing
`2√ζ` on each side for a total of `4√ζ`.

## Implications for Contributors

1. **New lemmas that only need scalar conclusions** should work with the public
   scalar averages (`fullSliceABAAvg`, etc.) and apply the public transport lemmas
   (`fullSlice_scalar_marginalize_x` / `fullSlice_scalar_marginalize_y`).

2. **New lemmas that need operator-level PSD arguments** (Schwartz–Zippel,
   `closenessOfIP`) should add private tensor intermediate definitions in
   `Transport/FullSlice.lean` and connect them to the public scalar API via
   bridge lemmas with explicit `√ζ` error terms.

3. **The extra `2√ζ` overhead** in the second-term transport (`4√ζ` total, rather
   than the paper's `2√ζ`) is a consequence of this architecture and is explained
   in detail in `docs/paper-gaps/issue-713-scalar-tensor-decision.tex`.

4. **Do not expose private tensor intermediates** as public API without updating
   this decision record.  Any change that makes a tensor-form average public
   should first discuss whether the scalar API should be downgraded or whether a
   new public tensor endpoint is justified by a downstream consumer that genuinely
   needs the operator structure.

## Cross-References

- Paper: `references/ldt-paper/commutativity-G.tex`, lines 332–401
- Paper-gap note: `docs/paper-gaps/issue-713-scalar-tensor-decision.tex`
- Source: `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean`
- Source: `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean`
- Source: `MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean`
- Source: `MIPStarRE/LDT/Commutativity/Main/Results.lean` (`comMain`)
