# Proof Guide: `bridge-lemmas-sorry-elim`

## Scope

- Branch: `bridge-lemmas-sorry-elim`
- Target: `MIPStarRE/LDT/Pasting/BridgeLemmas.lean`
- Paper source: `references/ldt-paper/ld-pasting.tex`
- Blueprint source: `blueprint/src/chapter/ch09_pasting.tex`

## Active Paper Fragment

The current target file corresponds to the Section 12 chain from the paper:

1. `lem:commute-g-half-sandwich` (lines 871-914)
2. `lem:ld-sandwich-line-one-point` (lines 917-1036)
3. `lem:h-b-consistency` (lines 1041-1091)
4. `lem:over-all-outcomes` (lines 1140-1289)

## TeX Fragment: `lem:commute-g-half-sandwich`

```tex
\begin{lemma}[Commuting past multiple $\widehat{G}$'s]
\label{lem:commute-g-half-sandwich}
For all $k \geq 2$,
  \[ \widehat{G}^{x_1}_{g_1} \widehat{G}^{x_2}_{g_2} \cdots \widehat{G}^{x_k}_{g_k} \ot I \approx_{\nu_4}
    \widehat{G}^{x_2}_{g_2} \cdots \widehat{G}^{x_k}_{g_k} \widehat{G}^{x_1}_{g_1} \ot I, \]
where
\[
\nu_4 = 426 k^2 m \cdot \left(\gamma^{1/16} +\zeta^{1/16} +  (d/q)^{1/16}\right).
\]
\end{lemma}

\begin{proof}
This proof will consist of multiple applications of \Cref{eq:gselfconall,eq:gcomall};
for each line, we will specify which equation to apply.
Each line will also involve an application of \Cref{prop:cab-approx-delta},
which we will specify only implicitly.
...
In total, we have $(k-2) + (k-2) \leq 2k$ applications of
\Cref{eq:gselfconall} with error $2\zeta$ each
and $(k-1) \leq k$ applications of \Cref{eq:gcomall}$ with error $\nu_3$ each.
By \Cref{prop:triangle-inequality-for-approx_delta}, this implies
\[
G^{x_1}_{g_1} G^{x_2}_{g_2} \cdots G^{x_k}_{g_k} \ot I
\approx_{3k \cdot (4k \zeta + k\nu_3)}
G^{x_2}_{g_2}\cdots G^{x_k}_{g_k} G^{x_1}_{g_1} \ot I.
\]
\end{proof}
```

### Informal Lean Reconstruction

The current monolithic file now contains the full flat-chain reconstruction of this proof.

The Lean proof spine is:

1. Split the point-tuple question space into a distinguished head slice and a tail:
   - `commuteGHalfSandwich_split_iff`
   - `commuteGHalfSandwich_split_succ_iff`

2. Build the repeated self-consistency move chain that sends the tail from Alice to Bob:
   - `commuteGHalfSandwich_moveChainLiftFamily`
   - `commuteGHalfSandwich_moveChain_step`
   - `commuteGHalfSandwich_move_chain`

3. Insert the single pairwise commutation step at the head:
   - `commuteGHalfSandwich_step_commute`

4. Build the post-commutation transport chain that moves the tail back while preserving the
   rotated-head form:
   - `commuteGHalfSandwich_secondSliceLift`
   - `commuteGHalfSandwich_moveBackChain_step`
   - `commuteGHalfSandwich_postMoveFlatStep`

5. Flatten the whole staged process into one `sddOpRel_chain` input:
   - `commuteGHalfSandwich_postMoveFlatFamily`
   - `commuteGHalfSandwich_flatChainFamily`
   - `commuteGHalfSandwich_flatChainStep`
   - `commuteGHalfSandwich_flatChainError_sum`

6. Convert the chain endpoints back to the original theorem statement and apply the displayed
   error bound:
   - `commuteGHalfSandwich_flatChainFamily_zero`
   - `commuteGHalfSandwich_flatChainFamily_last`
   - `commuteGHalfSandwich_error_bound`
   - `commuteGHalfSandwich_core`

The key design choice is that the Lean proof does not recursively chain the final theorem.
That would square the chain length and destroy the paper constant. Instead it recursively builds
the family-valued chain itself and applies `Preliminaries.sddOpRel_chain` only once at the end,
exactly matching the paper's `3k * (4k zeta + k nu_3)` bookkeeping.

## TeX Fragment: `lem:ld-sandwich-line-one-point`

```tex
\begin{lemma}[Consistency of $\widehat{H}$ with $B$]
\label{lem:ld-sandwich-line-one-point}
For any $1 \leq i \leq k$,
\[
\E_{\bu}  \E_{\bx_1, \dots, \bx_k} \sum_{g_1, \dots, g_k: g_i \neq \bot}
\sum_{a \neq g_i(\bu)}
\bra{\psi} \widehat{H}^{\bx_1, \dots, \bx_k}_{g_1, \dots, g_k} \ot
B^{\bu}_{[f(\bx_i)=a]} \ket{\psi}
\leq \nu_5.
\]
\end{lemma}

\begin{proof}
First sum out $g_{i+1},\dots,g_k$ using completeness and projectivity.
Then apply two Cauchy-Schwarz steps around `lem:commute-g-half-sandwich` to commute the
distinguished completed slice past the prefix.
Finally collapse
\[
\sum_{g_1,\dots,g_{i-1}} \widehat G^{x_{<i}}_{g_{<i}} (\widehat G^{x_{<i}}_{g_{<i}})^\dagger = I
\]
and finish with `eq:ld-gbcon`.
\end{proof}
```

### Remaining Lean Work

This is the main remaining blocker in the target file.

The intended Lean route is now more concrete.

#### Step A: exact prefix deletion

First prove an identity that removes coordinates `> i` from the sandwiched family by repeated
measurement completeness/projectivity. This should be a literal operator equality, not an
inequality. The target shape is the paper's equation
`eq:delete-extraneous-coordinates`.

Recommended local declarations:

1. `pointTuplePrefixEquiv` / `gHatTupleOutcomePrefixEquiv`
2. `gHatSandwichFamily_prefix_outcome`
3. `ldSandwichLineOnePoint_deleteExtraneousCoordinates`

The proof should only use:

- `gHatSandwichFamily.sum_eq_total`
- `gHatIdxMeas.sum_eq_total`
- `gHatIdxMeas_proj`
- `gHatHalfProductTotalOperator_eq_one`

#### Step B: move the distinguished slice into the commute theorem shape

Do not reverse the whole tuple. The right transport is a cyclic last-to-front reindex of the
prefix of length `i + 1`, so that the distinguished slice becomes the head slot and the already
proved theorem `commuteGHalfSandwich` applies through `commuteGHalfSandwich_split_iff`.

Recommended local declarations:

1. `pointTupleLastConsEquiv`
2. `gHatTupleOutcomeLastConsEquiv`
3. `ldSandwichLineOnePoint_commute_input_family`

This keeps the prefix order intact and avoids a mathematically false reversal statement.

#### Step C: package the two paper Cauchy-Schwarz steps

The two displayed `\sqrt{\nu_4}` moves should become two separate local scalar lemmas.

Recommended local declarations:

1. `ldSandwichLineOnePoint_firstCS`
   - use `Preliminaries.closenessOfInnerProduct_right`
   - this corresponds to `eq:gonna-need-a-bigger-cauchy-schwarz`
2. `ldSandwichLineOnePoint_secondCS`
   - use `Preliminaries.closenessOfInnerProduct_left`
   - this corresponds to `eq:even-bigger-CS`

The needed average `qSDDCore` hypothesis should come from:

- `hcomm (i + 1) (by omega)`
- `commuteGHalfSandwich_split_iff`
- reindexing by the last-to-front equivalence from Step B

#### Step D: contraction side conditions for the CS steps

The switcheroo files already contain the right proof pattern. The side conditions should be built
from small operator families rather than giant expanded expressions.

Reusable ingredients already available in the repo:

- `gHatHalfProduct_sum_adjoint_mul_le_one`
- `gHatReverseHalfProduct_sum_adjoint_mul_le_one`
- `projSubMeas_sandwich_sum_le_one`
- `switcherooAggregateFourthTerm_once_commuted_contraction_left`
- `switcherooAggregateFourthTerm_once_commuted_contraction_right`
- `switcherooLeftFront_close_firstSplitCore`

Likely new local declarations:

1. `ldSandwichLineOnePoint_firstCS_contraction`
2. `ldSandwichLineOnePoint_secondCS_contraction`

#### Step E: collapse the prefix sandwich and finish with `ldGbcon`

After the second Cauchy-Schwarz step, the remaining sum over the prefix should collapse to `I`.
It is worth making that collapse a named lemma rather than hiding it in one `simp` block.

Recommended local declarations:

1. `gHatPrefixSandwich_sum_eq_one`
2. `ldSandwichLineOnePoint_finish_to_ldGbcon`

The final scalar inequality should then reduce directly to `Pasting.ldGbcon` plus the already
proved analytic bound in `ldSandwichLineOnePointError`.

The endpoint-reduction scaffolding is now restored in the monolith:

- `postprocessMeasurement`
- `sandwichedLineQuestionOneEquiv`
- `ldSandwichLineOnePointRightEndpointMeasurement`
- `ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas`
- `ldSandwichLineOnePoint_endpoint_ldGbcon`
- `ldSandwichLineOnePoint_oneQuestion_ldGbcon`

These are intended to keep the eventual `k = 1` / endpoint `ldGbcon` collapse out of the main
one-point theorem body.

## TeX Fragment: `lem:h-b-consistency`

```tex
\begin{lemma}[Consistency of~$H$ with~$B$]\label{lem:h-b-consistency}
\[
H_{[h|_u =f]} \otimes I \simeq_{\nu_6} I \otimes B^u_f,
\]
where
\[
\nu_6 = 44 k^2m \cdot \left(\eps^{1/32} + \delta^{1/32} + \gamma^{1/32} + \zeta^{1/32} + (d/q)^{1/32}\right).
\]
\end{lemma}
```

### Remaining Lean Work

Once `ldSandwichLineOnePoint` is available, the remaining Lean work is mostly transport and
averaging:

1. Expand `constructedPastedSubMeas` through the distinct-tuple average.
2. Use the interpolation-support correctness lemmas to show that a globally consistent eligible
   tuple disagrees with a line polynomial only if some active coordinate violates the one-point
   predicate.
3. Pay the `ldDnoteq` cost to pass from distinct to uniform tuples.
4. Union-bound over coordinates and use `hline`.

The historical split helper stack worth porting is now more specific.

#### Already restored in the current monolith

- `interpolationSupportSubset`, `interpolationSupportSubset_subset`,
  `interpolationSupportSubset_card`
- `restrictToAxisParallelLine_apply`
- `restrictToVerticalLine_eval_eq_restrictAtHeight_eval`
- `interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem`
- `interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset`
- `tupleInterpolatedVerticalLine`

#### Still to port before `hBConsistency_core`

- `BadLineEvent` and the bad-mass transport lemmas
- option-lift / average transport lemmas for converting fixed-`u` defects into the
  final averaged `ConsRel`

#### Expected final proof spine for `hBConsistency_core`

1. Prove `pastedInterpolation_verticalLine_defect_le_badMass` for a fixed `u` and `xs`.
2. Prove `hBConsistency_fixed_u_defect_le_avgOver_distinct` by averaging over distinct tuples.
3. Expand `hBConsistencyBadMass` and dominate it by the coordinatewise mismatch mass.
4. Apply the abstract hypothesis `hline i hi` on each coordinate term.
5. Use `ldDnoteq` to absorb the distinct-vs-uniform gap.
6. Close the arithmetic with `hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add`.

## TeX Fragment: `lem:over-all-outcomes`

```tex
\begin{lemma}\label{lem:over-all-outcomes}
\[
\bra{\psi} H \otimes I \ket{\psi}
\approx_{\nu_7}
\E_{\bx_1, \ldots, \bx_k}
\sum_{\tau:|\tau| \ge d+1}
\sum_{(g_1,\ldots,g_k) \in \mathsf{Outcomes}_\tau}
\bra{\psi} \widehat H^{\bx_1,\ldots,\bx_k}_{g_1,\ldots,g_k} \otimes I \ket{\psi}.
\]
\end{lemma}
```

### Remaining Lean Work

This proof should follow the paper decomposition literally:

1. Expand the constructed pasted submeasurement over distinct tuples and globally consistent
   eligible outcomes.
2. Introduce `B^u` by completeness of the line measurement.
3. Insert the consistency indicator and control the discarded mass by the already-proved
   one-point lemma.
4. Use interpolation correctness plus Schwartz-Zippel to bound the nonglobal remainder by `md/q`.
5. Pay the final distinct-to-uniform `ldDnoteq` transport.

At the current branch state, this theorem is downstream of the remaining one-point theorem and the
bad-mass/interpolation helper stack, not of the half-sandwich commutation theorem anymore.

#### Concrete plan for `overAllOutcomes`

1. Re-express `constructedPastedMeasurementTotal` through the distinct-tuple average and the
   `pastedInterpolationFamily` support filter.
2. Split the distinct average into globally consistent and nonglobal tuples using
   `globallyConsistentOutcomesByType` / `nonglobalOutcomesByType`.
3. Reuse the same fixed-`u` bad-event machinery from `hBConsistency_core` to insert the line
   consistency indicator and bound the discarded mass by `k * nu_5 + k^2 / q`.
4. Apply the interpolation-support correctness lemmas to identify the candidate interpolant on the
   support subset and derive the Schwartz-Zippel witness polynomial used in lines 1235-1265 of the
   paper.
5. Finish with the existing `ldDnoteq` and the displayed arithmetic bound for
   `overAllOutcomesError`.
