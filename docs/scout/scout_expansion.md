## matrixLocalToGlobal (line 34)
- Paper reference: `lem:local-to-global`
- Paper proof strategy: Rewrite the local variance as a trace against the hypercube Laplacian using `lem:local-rewrite`, rewrite the global variance as the norm of the orthogonal-to-constant component using `lem:global-rewrite`, then apply the spectral gap lower bound `L >= (1 / (mM)) P_perp` on the nonconstant subspace.
- Key Mathlib lemmas needed: `laplacianSpectralGap`, `Matrix.mul_kronecker_mul`, `Matrix.conjTranspose_kronecker`, `Matrix.trace_kronecker`, `MIPStarRE.Quantum.normalizedTrace_mul_comm`, `Matrix.PosSemidef.kronecker`, `MIPStarRE.Quantum.sandwich_mono`
- Estimated difficulty: hard
- Estimated Lean proof lines: 140
- Blockers: no matrix-level spectral inequality has been proved relating `matrixLaplacianOperator` to `orthogonalModeProjectorMatrix`; `matrixCombinedColumnOperator` is only a placeholder and loses the cross terms the paper argument uses; there will also be nontrivial normalization bookkeeping because the code uses normalized traces on product spaces

## matrixLocalRewrite (line 40)
- Paper reference: `lem:local-rewrite`
- Paper proof strategy: Expand the combined column operator against the Laplacian difference form, compute `((⟨u| - ⟨v|) ⊗ ⟨ψ|) A_combine)` as the row operator for `(A^u - A^v)`, and then take traces to identify the result with the edge-averaged squared difference.
- Key Mathlib lemmas needed: `Matrix.mul_kronecker_mul`, `Matrix.conjTranspose_kronecker`, `Matrix.trace_kronecker`, `Matrix.trace_mul_comm`, `MIPStarRE.Quantum.normalizedTrace_mul_comm`, `Fintype.sum_prod_type'`, `Finset.sum_congr`
- Estimated difficulty: hard
- Estimated Lean proof lines: 80
- Blockers: the file explicitly notes that `matrixCombinedColumnOperator` is not the paper's rectangular column operator, so the current witness misses off-diagonal `|u⟩⟨v|` terms and the stated equality is likely not provable until that representation is fixed; normalized-trace scaling on the tensor space also needs to be checked carefully

## matrixGlobalRewrite (line 46)
- Paper reference: `lem:global-rewrite`
- Paper proof strategy: Split the combined operator into constant and orthogonal Fourier modes, identify the orthogonal part with the centered family `A^u - A_avg`, and rewrite the centered second moment as `1/2` times the average pairwise squared difference.
- Key Mathlib lemmas needed: `Matrix.mul_kronecker_mul`, `Matrix.conjTranspose_kronecker`, `Matrix.trace_kronecker`, `MIPStarRE.Quantum.normalizedTrace_mul_comm`, `Fintype.sum_prod_type'`, `Finset.sum_add_distrib`, `Finset.mul_sum`
- Estimated difficulty: hard
- Estimated Lean proof lines: 110
- Blockers: the same column-operator issue from `matrixLocalRewrite`; there are no supporting lemmas yet showing that `constantModeProjectorMatrix` and `orthogonalModeProjectorMatrix` implement the paper's `φ_0/φ_perp` decomposition at the trace level; the trace normalization factors are easy to get wrong here

## localToGlobal (line 59)
- Paper reference: `lem:local-to-global`
- Paper proof strategy: Use the two rewrite lemmas to convert local/global variances into Laplacian and orthogonal-projector trace expressions, then compare them using the hypercube spectral gap.
- Key Mathlib lemmas needed: `matrixLocalToGlobal`, bridge lemmas from abstract operators/states to `MatrixOperatorFamilyRealization`, `avgOver_congr`, `avgOver_mono`, `ev_nonneg_of_psd`
- Estimated difficulty: hard
- Estimated Lean proof lines: 30
- Blockers: the bridge from the abstract `A, ψ` world to the matrix realization layer does not exist yet; `rerandomizeCoord` and `independentPointPair` are both currently `uniformDistribution (Point × Point)`, so the abstract local/global variances do not match the paper; the abstract trace witnesses are still placeholder non-tensor constructions

## localRewrite (line 66)
- Paper reference: `lem:local-rewrite`
- Paper proof strategy: Introduce the combined operator, use the Laplacian difference-form identity, and expand the trace sandwich so that only the edgewise squared differences remain.
- Key Mathlib lemmas needed: `matrixLocalRewrite`, bridge lemmas to matrix realizations, `MIPStarRE.Quantum.normalizedTrace_mul_comm`, `Matrix.mul_kronecker_mul`, `Matrix.trace_kronecker`
- Estimated difficulty: hard
- Estimated Lean proof lines: 20
- Blockers: `combinedOperator` is currently just `∑ u, A u` on the strategy space rather than `∑_u |u⟩ ⊗ A^u ⊗ I`; `localVarianceTraceWitness` omits the Laplacian and tensor factors from the paper entirely; this theorem is therefore blocked on replacing the placeholder abstract definitions, not just on filling in a proof

## globalRewrite (line 73)
- Paper reference: `lem:global-rewrite`
- Paper proof strategy: Decompose the combined operator into average and orthogonal pieces, rewrite the orthogonal piece as `A^u - A_avg`, and convert the centered second moment into the global pairwise variance formula.
- Key Mathlib lemmas needed: `matrixGlobalRewrite`, bridge lemmas to matrix realizations, `Fintype.sum_prod_type'`, `Finset.sum_add_distrib`, `MIPStarRE.Quantum.normalizedTrace_mul_comm`
- Estimated difficulty: hard
- Estimated Lean proof lines: 25
- Blockers: `GlobalVarianceDecomposition` is only a placeholder container and does not assert the identities the paper uses; `globalVarianceTraceWitness` ignores the point-register orthogonal vector structure; as with `localRewrite`, the abstract theorem needs a real tensor/column-operator bridge before a faithful proof is possible
