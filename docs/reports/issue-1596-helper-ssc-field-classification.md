# Issue #1596: Helper SSC Field Classification

Date: 2026-05-20.

## Scope

This note classifies the fields of
`MIPStarRE.LDT.SelfImprovement.HelperStrongSelfConsistencyObligations`, the
internal record used in the proof of the strong self-consistency item for the
self-improvement helper.

The paper source is `references/ldt-paper/self_improvement.tex`, in the proof
of `lem:self-improvement-helper`, from the add-in-`u` lemma through
`item:self-improvement-self`.  The relevant named equations are
`eq:move-one`, `eq:move-another`, `eq:change-one`, `eq:change-another`,
`eq:swapped-u-for-v`, `eq:swapped-u-for-v-this-time-it's-personal`, and
`eq:move-over-v`.

The blueprint source is `blueprint/src/chapter/ch07_self_improvement.tex`,
around the proof of `item:self-improvement-self`.

## Classification

`step01Bound` records the paper's `Q_0 -> Q_1` transport
(`eq:move-one`).  It is a point-measurement strong self-consistency estimate.
Lean derives it by
`addInU_cs_chain_step1_abs_le_sqrt_two_delta` from
`BipartiteSSCRel strategy.state ... delta`.

`step12Bound` records the paper's `Q_1 -> Q_2` transport
(`eq:move-another`).  It is again a point-measurement strong self-consistency
estimate, derived by `addInU_cs_chain_step2_abs_le_sqrt_two_delta` from the
same point self-consistency hypothesis.

`step23Bound` records the first variance transport (`eq:change-one`).  It is a
global-variance consequence of the local-variance sum bound.  Lean obtains it
through
`add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds`.

`step34Bound` records the second variance transport (`eq:change-another`).  It
has the same status as `step23Bound`: it is derived from the local-variance sum
bound by the same global-variance constructor.

`residualLowerBound` records the lower bound on the released right-hand side
after the off-diagonal expansion in the paper's strong self-consistency proof.
This is the only field that is not one of the four add-in-`u` chain moves.  It
is assembled in Lean from the off-diagonal variance swaps, the two
post-`delete-an-A` transports, the complementary-slackness relation
`T_h A_h = T_h Z`, and the point-consistency add-in-`u` transfer.  The
constructor
`helper_ssc_obligations_of_scalarTransports_pointTransfer` performs this
assembly.

## Current Lean Boundary

The record is not a hypothesis of `lem:self-improvement-helper`,
`thm:self-improvement`, or any source-labelled theorem.  In the current Lean
route, the source-facing self-improvement theorem constructs the record
internally from:

- point self-consistency of the strategy;
- the local-variance estimate supplied by `strategy.IsGood`;
- the SDP complementary-slackness equation from the helper output with
  slackness;
- the point-consistency add-in-`u` transfer.

The final application is
`helper_strong_self_consistency_of_helper_conclusion`, which consumes the
record and proves the helper-stage `BipartiteSSCRel`.

## Verdict

`HelperStrongSelfConsistencyObligations` is a grounded internal assembly
record.  Its first four fields are exact scalar transport estimates matching
named paper equations.  Its final field is a residual-side scalar bound that is
assembled from already named Lean estimates rather than assumed by a
source-facing theorem.

No source-labelled theorem currently exposes this record as a non-paper
hypothesis.  No blueprint proof-level `\leanok` overclaim is associated with
this obligation record.  The remaining work under #1596 should therefore move
away from this record and toward the other open bundle sites: residual
domination in `RestrictSome` and any projectivization boundary that still
appears as a live construction hypothesis.  The former
`SpectralTruncationInput` consumer rewire has been completed by replacing the
wrapper with direct `SpectralTruncationStatement` construction theorems.
