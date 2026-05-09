# Blueprint coverage analysis for #1329 helper deduplication

PR #1399 moves/reorganizes several private helper lemmas to eliminate
duplication. The blueprint reverse-coverage CI flagged 11 declarations as
"changed but lacking `\lean{}` tags". This documents why each does not (and
should not) receive a blueprint traceability node.

## Declarations without blueprint nodes

| Declaration | Module | Reason no blueprint tag |
|-------------|--------|------------------------|
| `swapDensity` | `Test/StrategyCore` | Internal matrix-reindexing definition (SWAP on `ι × ι`); no paper theorem asserts its properties directly. |
| `swapDensity_eq_reindex` | `Test/StrategyCore` | Proof that `swapDensity` equals a product-commutation reindex. Internal algebraic infrastructure. |
| `swapDensity_swapDensity` | `Test/StrategyCore` | Involution property of `swapDensity`. Purely internal algebra. |
| `swapDensity_add` | `Test/StrategyCore` | Additivity of `swapDensity`. Purely internal algebra. |
| `swapDensity_smul` | `Test/StrategyCore` | Homogeneity of `swapDensity`. Purely internal algebra. |
| `conjTranspose_mul_mono` | `Preliminaries/ComparisonCore` | Loewner-order monotonicity of `Zᴴ·X·Z`. Internal matrix inequality bridging PSD lemmas with order reasoning; no paper statement. |
| `qSDDOp_symm` | `Preliminaries/ComparisonCore` | Symmetry of the squared-distance operator sum. Internal infrastructure lemma; moved from `CommutativityPoints/SharedHelpers/Core` (where it also lacked a `\lean{}` tag). |
| `sddOpRel_symm` | `CommutativityPoints/SharedHelpers/Core` | Symmetry wrapper for `SDDOpRel`. Only the proof body was updated (qualified reference to `qSDDOp_symm`); the statement is unchanged. No new paper content. |

## False positives (line-number drift)

| Declaration | Module | Explanation |
|-------------|--------|-------------|
| `stateDependentDistanceOpRel_mono` | `Preliminaries/DistanceBounds` | NOT changed by this PR. Line number shifted because private lemmas were removed above it. The blueprint sync tool flagged it on line-number proximity. |
| `consRel_uniform_equiv` | `Preliminaries/ComparisonCore` | NOT changed by this PR. Line number shifted from adding new lemmas above it. |

## Conclusion

All 11 blueprint warnings are either (a) internal infrastructure without paper
counterparts, or (b) false positives from line-number drift. No `\lean{}` tag
additions are warranted. No paper-facing public API was created or altered.
