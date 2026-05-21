# Issue #1697: Naimark tensor-product statement

## Source comparison

The source theorem is `thm:naimark` in
`references/ldt-paper/orthonormalization.tex`, lines 36-80.  It starts with a
state on `H_A tensor H_B` and submeasurements `A^x` and `B^y` on the two local
Hilbert spaces.  It concludes that there are auxiliary Hilbert spaces, a product
auxiliary state, and projective submeasurements on the enlarged local Hilbert
spaces preserving every bipartite correlation

```text
<psi | A^x_a tensor B^y_b | psi>
  =
<psi_hat | Ahat^x_a tensor Bhat^y_b | psi_hat>.
```

The paper proof at lines 161-187 applies the one-measurement Naimark helper to
each question and tensors the resulting auxiliary registers.  The helper at
lines 121-159 produces a projective submeasurement on the original outcomes:
the missing mass is represented by the additional `⊥` outcome of the auxiliary
construction.  Thus a complete projective measurement on the original outcome
type is not the standard theorem for arbitrary submeasurements.

## Lean status

The formalization now separates the following declarations.

- `oneMeasNaimark`: the one-measurement helper corresponding to
  `lem:naimark-helper`; proved.
- `OneMeasNaimarkData.toProjSubMeas`: the restriction of the completed
  `Option`-outcome dilation to the original outcomes; proved.
- `questionwiseNaimark`: the Lean-only interface for per-question marginal
  preservation; proved.
- `NaimarkProductRegisterProjectorData`: the Lean-only object recording the
  product-register projective submeasurements and the four-index correlation
  identity; stated.
- `naimarkTensorProductCorrelationData_of_productRegisterProjectors`: the
  assembly of the full Naimark witness data from the product-register object;
  proved.
- `naimarkTensorProductCorrelation_of_productSubmeasurements`: the internal
  reduction from product-register projective submeasurements and the four-index
  correlation identity to the source-shaped theorem; proved.
- `naimarkTensorProductCorrelationDataConstruction`: the named construction
  target for the universe-polymorphic source statement; proof obligation.  The
  new product-register data structure identifies its missing mathematical
  content as the lifted questionwise projectors and their correlation identity.
- `naimarkTensorProductCorrelation`: the source-shaped tensor-product
  correlation theorem; proved from the named proof obligation.

The source-shaped statement is deliberately not marked `\leanok` in the
blueprint.  Its Lean proof still factors through the named construction target
`naimarkTensorProductCorrelationDataConstruction`, but that construction target
now has a proved same-universe reduction from the concrete product-register
object `NaimarkProductRegisterProjectorData`.

## Statement integrity audit

Paper assumptions:

- finite-dimensional local Hilbert spaces `H_A` and `H_B`;
- a normalized state on `H_A tensor H_B`;
- question-indexed submeasurements `A^x` and `B^y`.

Lean assumptions:

- finite Hilbert-space carriers `HA` and `HB`;
- an explicit normalization hypothesis `psi.IsNormalized`;
- question-indexed submeasurements on `HA.carrier` and `HB.carrier`.

Paper conclusion:

- auxiliary Hilbert spaces on Alice's and Bob's sides;
- a normalized auxiliary product state;
- a dilated state `psi_hat = psi tensor aux`;
- projective submeasurements on the two enlarged local spaces;
- preservation of all four-index bipartite correlations.

Lean conclusion:

- finite auxiliary Hilbert-space carriers;
- normalized auxiliary product-state data;
- a normalized dilated state whose density is the register-reordered tensor
  product of the source state and the auxiliary state;
- indexed projective submeasurements on the enlarged local spaces;
- the same four-index correlation identity, expressed with `opTensor`.

Verdict: exact source-facing theorem header with faithful boundary hypotheses
and a documented local correction.  The explicit finite carriers and
normalization fields are Lean encodings of the paper's finite-dimensional state
convention.  The projective-submeasurement conclusion is the form supplied by
the paper's helper lemma; the stronger complete-measurement conclusion on the
original outcome type is false for arbitrary submeasurements.  The local
passage from completed `Option`-outcome
measurements to original-outcome projective submeasurements is proved by
`OneMeasNaimarkData.toProjSubMeas`.  The auxiliary-state and dilated-state part
of the final assembly is packaged by
`naimarkTensorProductCorrelationData_of_productRegisterProjectors` and
`naimarkTensorProductCorrelation_of_productSubmeasurements`.  The remaining
proof obligation is still the source-shaped declaration
`naimarkTensorProductCorrelationDataConstruction`; within the concrete
same-universe product-register setting, the unconstructed object has been
isolated as `NaimarkProductRegisterProjectorData`.

## Current non-green dependency nodes

| Blueprint node | Lean declarations | Status |
| --- | --- | --- |
| `thm:naimark` | `NaimarkTensorProductCorrelationStatement`, `naimarkTensorProductCorrelation` | Source-shaped statement; not marked `\leanok` because the proof still depends on `naimarkTensorProductCorrelationDataConstruction`. |
| `rem:lean-naimark-auxiliary-declarations` | Auxiliary-state declarations, `NaimarkProductRegisterProjectorData`, `naimarkTensorProductCorrelationData_of_productRegisterProjectors`, `naimarkTensorProductCorrelationDataConstruction`, `naimarkTensorProductCorrelation_of_productSubmeasurements` | Internal decomposition of the tensor assembly; not marked `\leanok` because the product-register projector construction remains a proof obligation. |
| `rem:lean-questionwise-naimark` | `questionwiseNaimark`, `OneMeasNaimarkData.toProjSubMeas`, and related one-measurement declarations | Proved questionwise interface; this is not the full bipartite theorem. |
