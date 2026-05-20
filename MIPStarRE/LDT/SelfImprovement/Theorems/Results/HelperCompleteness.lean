import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed

/-!
# Helper completeness and SDP bridge

This compatibility module re-exports the helper-completeness development.  The
proof is split into input-consistency and SDP bridge lemmas, fiber-operator
bounds, linearized SDP rewrites, and bracketed mass identities.

## Contents

### Input consistency and the SDP bridge

- `input_consistency_match_mass_lower_bound` records the incoming `ConsRel`
  lower bound for the input matching mass.
- `input_match_mass_eq_sdp_overlap` reindexes the averaged overlap as the SDP
  primal-dual overlap.
- `sdp_overlap_le_dual_mass` bounds the SDP overlap by the dual mass.
- `input_consistency_dual_mass_lower_bound` combines these inequalities.
- `sdp_complementary_slackness_sum_eq_dual_mass` converts the averaged point
  sum to the dual mass under complementary slackness.

### Fiber operators and Cauchy--Schwarz estimates

- `helperFiberOperator` is the grouped operator `T_[h(u)=a]`.
- `helperFiberOperator_nonneg`, `helperFiberOperator_le_one`, and
  `helperFiberOperator_sum_eq_total` give its elementary order properties.
- `helper_first_move_second_factor_le_one` and
  `helper_second_move_first_factor_le_one` are the identity-factor bounds.
- `helper_second_move_second_factor_le_delta` is the self-consistency factor
  bound.
- `helper_linearized_completeness_quantity_eq_fiber_sum` gives the fiberwise
  expression for the linearized quantity.
- `helper_second_move_abs_sub_first_moved_le_sqrt_delta` is the second
  Cauchy--Schwarz move.

### Linearized and bracketed assemblies

- `helper_linearized_completeness_eq_dual_mass_of_complementary_slackness` and
  `helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness`
  identify the linearized quantity with the dual mass.
- `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta` is the first
  Cauchy--Schwarz move.
- `helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness` assembles
  the scalar estimates with complementary slackness.
- `helper_completeness_of_input_consistency` and
  `helper_completeness_of_cauchy_schwarz_input_consistency` turn these estimates
  into the helper-completeness lower bound.
- `helper_mass_eq_avg_pointwise_sandwich_sum`,
  `helper_pointwise_sandwich_sum_eq_bracketed`, and
  `helper_mass_eq_avg_pointwise_bracketed_sum` give the exact bracketed
  reindexing of the helper mass.
- `helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness`
  is the paper-shaped bracketed assembly.

### Strengthened helper wrappers

- `helper_completeness_of_self_consistency_complementary_slackness_input_consistency`
  packages self-consistency, complementary slackness, and input consistency.
- `helper_sdp_optimal_pair_with_slackness` reconstructs the slackness-carrying
  SDP pair from the strengthened helper hypothesis.
- `helper_hhat_vs_z_of_self_consistency_and_helper_slackness` and
  `helper_completeness_of_self_consistency_helper_slackness_input_consistency`
  use the strengthened helper conclusion directly.
- `sdp` and `addInU` are the reduced Section 9 statements used by the
  surrounding self-improvement theorem.
- `sdp_statement_with_slackness` is the formalized Section 9 strong-duality
  statement carrying complementary slackness.

## References

- `references/ldt-paper/self_improvement.tex` lines 354--468
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/
