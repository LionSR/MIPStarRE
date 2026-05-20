# Issue #1697: Naimark tensor-product statement

## Source comparison

The source theorem is `thm:naimark` in
`references/ldt-paper/orthonormalization.tex`, lines 36-80.  It starts with a
state on `H_A tensor H_B` and submeasurements `A^x` and `B^y` on the two local
Hilbert spaces.  It concludes that there are auxiliary Hilbert spaces, a product
auxiliary state, and projective measurements on the enlarged local Hilbert
spaces preserving every bipartite correlation

```text
<psi | A^x_a tensor B^y_b | psi>
  =
<psi_hat | Ahat^x_a tensor Bhat^y_b | psi_hat>.
```

The paper proof at lines 161-187 applies the one-measurement Naimark helper to
each question and tensors the resulting auxiliary registers.

## Lean status

The formalization now separates three declarations.

| Declaration | Role | Status |
| --- | --- | --- |
| `oneMeasNaimark` | one-measurement helper corresponding to `lem:naimark-helper` | proved |
| `questionwiseNaimark` | Lean-only interface for per-question marginal preservation | proved |
| `naimarkTensorProductCorrelation` | source-shaped tensor-product correlation theorem | stated, proof obligation |

The new statement is deliberately not marked `\leanok` in the blueprint.  It
records the missing mathematical object without claiming that the tensor
assembly has been formalized.

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
- projective measurements on the two enlarged local spaces;
- preservation of all four-index bipartite correlations.

Lean conclusion:

- finite auxiliary Hilbert-space carriers;
- normalized auxiliary product-state data;
- a dilated state whose density is the register-reordered tensor product of
  the source state and the auxiliary state;
- indexed projective measurements on the enlarged local spaces;
- the same four-index correlation identity, expressed with `leftTensor` and
  `rightTensor`.

Verdict: faithful boundary hypotheses.  The explicit finite carriers and
normalization fields are Lean encodings of the paper's finite-dimensional
state convention.  The proof is still absent and remains the tensor-register
assembly tracked by issue #1697 and `docs/paper-gaps/naimark.tex`.
