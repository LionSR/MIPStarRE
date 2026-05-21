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
- `naimarkTensorProductCorrelation_of_productSubmeasurements`: the internal
  reduction from product-register projective submeasurements and the four-index
  correlation identity to the source-shaped theorem; proved.
- `naimarkTensorProductCorrelationDataObligation`: the named construction target
  for the auxiliary spaces, product auxiliary state, product-register projective
  submeasurements, and four-index correlation identity; proof obligation.
- `naimarkTensorProductCorrelation`: the source-shaped tensor-product
  correlation theorem; proved from the named proof obligation.

The source-shaped statement is deliberately not marked `\leanok` in the
blueprint.  Its Lean proof now factors through the named construction target
`naimarkTensorProductCorrelationDataObligation`, so the declaration records the
source statement without claiming that the tensor assembly has been fully
formalized.

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

Verdict: faithful boundary hypotheses with a documented local correction.  The
explicit finite carriers and normalization fields are Lean encodings of the
paper's finite-dimensional state convention.  The projective-submeasurement
conclusion is the form supplied by the paper's helper lemma; the stronger
complete-measurement conclusion on the original outcome type is false for
arbitrary submeasurements.  The local passage from completed `Option`-outcome
measurements to original-outcome projective submeasurements is proved by
`OneMeasNaimarkData.toProjSubMeas`.  The auxiliary-state and dilated-state part
of the final assembly is packaged by
`naimarkTensorProductCorrelation_of_productSubmeasurements`.  The remaining
proof obligation is now the single named theorem
`naimarkTensorProductCorrelationDataObligation`: construct the auxiliary
spaces, product auxiliary state, product-register projective submeasurements,
and four-index correlation identity from the questionwise one-measurement
Naimark dilations.
