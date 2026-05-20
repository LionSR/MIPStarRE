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

---

## Consequences for the repository

1. The conditional `RestrictSome` lemmas are still mathematically useful and
   should remain as conditional order-theoretic statements.

2. The current comments claiming that the monotone-total route is reduced merely
   to proving `XHat_none = X_none` are too strong.  That proof yields the QXP
   comparison `Q_none ≤ P_none`, but an additional source-to-`Q` comparison is
   still needed, and it is not available in general.

3. The downstream `SelfImprovement` theorem should continue to use the existing
   total-difference route unless a narrower, genuinely valid source-residual
   theorem is proved for the specific helper-output construction.

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
