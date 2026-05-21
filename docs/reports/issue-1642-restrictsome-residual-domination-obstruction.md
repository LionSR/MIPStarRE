# Issue #1642 — RestrictSome Residual-Domination Obstruction

Date: 2026-05-18

Scope: `MIPStarRE/LDT/MakingMeasurementsProjective/` and the downstream
`SelfImprovement` monotone-total route.

---

## Executive Summary

The current issue-#1642 route is not blocked by a missing two-line bridge.
It is blocked by a mathematical gap in the proposed implication.

The existing Lean algebra proves only the construction-level statement

```text
Q_none ≤ P_none
```

for the QXP layer, under extra coisometry hypotheses on the sigma-space matrix
`X`.  The `RestrictSome` lemmas needed by the monotone-total route consume the
strictly stronger source-facing hypothesis

```text
(optionCompletion A).outcome none ≤ P.outcome none.
```

The missing comparison

```text
(optionCompletion A).outcome none ≤ Q_none
```

is not supplied anywhere in the current rank-reduction or positive-Gram
construction.  More importantly, it is not true in general for the present
orthonormalization pipeline.

Accordingly, the right repair is not to keep searching for a small bridge from
`Q_none ≤ P_none` to source residual domination.  The route must be narrowed to
a stronger special case, or replaced by a different downstream argument.

---

## The live Lean chain

The current formal development establishes the following.

1. In
   `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean`,
   the lemmas
   `fresh_outcome_le_of_xHatA_eq_xa` and
   `q_outcome_none_le_p_outcome_none_of_x_coisometry`
   prove that preserving the fresh `none` row block yields
   `data.qLayer.q.outcome none ≤ Pa data none`.

2. In
   `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/RestrictSome.lean`,
   the lemmas
   `restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le` and
   `restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le`
   consume the stronger hypothesis
   `(optionCompletion A).outcome none ≤ P.outcome none`.
   The theorems
   `restrictSomeProjSubMeas_total_not_le_obstruction` and
   `optionCompletion_outcome_none_not_le_obstruction` formalize the two
   one-dimensional failures obtained by omitting this hypothesis from the generic
   restriction lemma.  The combined existential theorem
   `restrictSomeProjSubMeas_total_le_requires_residual_hypothesis` packages the
   same example: a zero one-outcome source submeasurement and a completed
   projective submeasurement with all mass on the original outcome give
   `P_total = I` and `A_total = 0`.

3. In
   `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean`,
   the theorem
   `pQApprox_ofRankReductionSigmaRangePositiveGram_with_x_coisometry`
   records the extra hypothesis needed to deduce `Q_none ≤ P_none`, namely the
   coisometry of the sigma-space embedding.  This theorem itself requires the
   subnormalization input `∑ q_a ≤ 1`, which is stronger than the current
   `RankReductionWitness.total_le` bound.

Thus the present code isolates a QXP-internal fresh-outcome comparison, but it
does not prove the source-facing residual comparison required by `RestrictSome`.

---

## A scalar obstruction

The missing source-to-`Q_none` bridge fails already in the one-dimensional
scalar model.

Let the ambient Hilbert space be `ℂ`, and let the original submeasurement have a
single outcome `some` with

```text
A_some = 0.99 · I.
```

Then the option completion has fresh residual outcome

```text
A_none = I - A_some = 0.01 · I.
```

The completed family is a measurement, and its diagonal self-consistency defect
on the normalized one-dimensional state is

```text
1 - (0.99^2 + 0.01^2) = 0.0198.
```

So this is a perfectly legitimate small-error input to the current Section 5
pipeline.  In the spectral-truncation step, any threshold with `1 - δ > 0.01`
and `1 - δ ≤ 0.99` produces

```text
R_some = I,
R_none = 0.
```

For the one-dimensional rank-bound branch, the rank-reduction witness may keep
`Q = R`, so already at the `Q` layer one has

```text
Q_none = 0
```

while the source residual remains

```text
A_none = 0.01 · I.
```

Hence the desired source-facing inequality fails:

```text
A_none ≤ Q_none
```

is false.  Therefore no theorem which derives source residual domination from
the current `Q_none ≤ P_none` route alone can be valid in this generality.

The problem is not merely that the current Lean proof is missing.  The route is
mathematically too strong unless extra hypotheses are added or the construction
is specialized.

The Lean theorems `restrictSomeProjSubMeas_total_not_le_obstruction` and
`optionCompletion_outcome_none_not_le_obstruction` record the two smaller formal
obstructions directly at the `RestrictSome` interface.  They do not attempt to
model the spectral-truncation construction above; instead they show that the
generic restriction lemma itself cannot drop the residual hypothesis.  In the
example, the source total is zero, the restricted projective total is the
identity, and the completed source residual is also the identity, so each
failed inequality would force `I ≤ 0`.  The theorem
`restrictSomeProjSubMeas_total_le_requires_residual_hypothesis` packages both
negations as a single existential witness.

---

## Consequences for the repository

1. The conditional `RestrictSome` lemmas are still mathematically useful and
   should remain as conditional order-theoretic statements.

2. The current comments claiming that the monotone-total route is reduced merely
   to proving `XHat_none = X_none` are too strong.  That proof yields the QXP
   comparison `Q_none ≤ P_none`, but an additional source-to-`Q` comparison is
   still needed, and it is not available in general.

3. The currently proved downstream `SelfImprovement` route follows the paper's
   expectation-level total-difference transport.  The sharper operator-total
   target remains a narrower Lean-only strengthening for the specific
   helper-output construction, not a replacement for the source proof.

4. Any future replacement for issue #1642 should be stated as one of the
   following, and not as generic residual domination for the present Section 5
   output:
   - a theorem under additional hypotheses that really imply
     `(optionCompletion A).outcome none ≤ P.outcome none`, or
   - a helper-output-specific theorem for the Section 9 averaged measurement, or
   - a different downstream point-consistency transport that avoids this source
     residual comparison altogether.

5. The deleted residual-domination bridge modules from the Section 9 history do
   not change this verdict.  Their constructors accepted the missing comparison
   as an extra input, usually in a form such as
   ```text
   (optionCompletion Hhat).outcome none ≤
     (qxpProjSubMeas ((hqxp hssc hSpectral).data)).outcome none.
   ```
   They were useful packaging around a stronger hypothesis, but they were not a
   proof of that hypothesis from the current helper-output construction.

6. A possible helper-specific route would have to pass through a stronger SDP
   witness carrying the auxiliary dominance fact \(I \le Z\), together with a
   proof that this dominance is transported to the particular helper-output
   residual comparison.  The relevant dominance-carrying interfaces are
   `MatrixSdpStatementWithSlacknessAndDominance` in
   `MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Witness.lean`
   and the bridge theorem
   `toMatrixSdpStatementWithSlacknessAndDominance` in
   `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`;
   related constructors include
   `matrixSdpOptimalWitnessWithDominance_of_canonicalComplementarySlackness`
   and
   `matrixSdpOptimalWitnessWithDominance_of_canonicalFeasibleComplementarySlackness`.
   These declarations are Lean-only dominance-carrying refinements, not the
   abstract paper-facing SDP statement.

   This does not contradict the scalar obstruction above.  The scalar example
   rules out a generic theorem deriving
   `(optionCompletion A).outcome none ≤ P.outcome none` from the present
   Section 5 output alone.  The additional hypothesis \(I \le Z\) could only be
   useful in a theorem which is specific to the Section 9 helper construction
   and which proves that the same dual witness \(Z\), after the saturation and
   helper-output translations, controls the actual fresh outcome of the
   projective measurement being used.  That transport theorem is exactly the
   remaining issue-`#1642` frontier.

   The former SDP slackness obligation has been discharged: the declaration
   `MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness` is audited by
   `assert_sdp_slackness_axioms` in
   `MIPStarRE/LDT/Test/AxiomAudit.lean` and prints only the standard Lean
   axioms.  Thus the remaining frontier is the helper-output-specific residual
   domination needed by issue `#1642`, not the former SDP slackness obligation.

---

## Verdict

The current issue-#1642 route should be treated as an obstruction note, not as a
small missing bridge.  The repository already contains the strongest valid
generic QXP statement currently justified by the code:

```text
Q_none ≤ P_none.
```

What fails is the extra step from the completed source residual to `Q_none`.
Until a narrower theorem is identified and proved, the honest status is that the
monotone-total route is not available in general for the present orthonormalization
construction.
