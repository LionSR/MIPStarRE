# Issue 2386: Reusable finite SDP duality theorem design

Date: 2026-06-19

## Summary

Issue #2386 asks whether the proof of
`MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalStrongDuality` can be
separated from the particular canonical block SDP used in Section 9.  The
answer is yes, but only after separating two mathematical layers.

The first layer is a real conic-duality theorem.  It concerns a proper cone
`K` in a real topological vector space, a continuous linear constraint map
`A`, a continuous linear objective `c`, and a constraint value `b`.  The proof
is the separation argument already visible in
`MatrixRealization/Canonical/StrongDuality/Separation.lean`: form the closed
image cone of positive primal variables under `x |-> (A x, c x)`, separate a
point above the optimal identity fiber, normalize the separator, and obtain a
dual feasible functional with a smaller value, contradicting dual optimality.

The second layer is matrix-specific.  It represents the dual functional by a
Hermitian matrix under the real trace pairing, converts nonnegativity on the
positive semidefinite primal cone into positive semidefiniteness of the dual
slack, and converts zero trace pairing into the product equation used for
complementary slackness.  This layer is necessary to recover the paper's
operator \(Z\) and the equations \(T_g Z = T_g A_g\).

The present canonical proof should therefore not be replaced by a generic
theorem in one step.  A reusable theorem should first reproduce the functional
zero-gap conclusion.  A later matrix specialization can recover the exact
Section 9 witness.

## Current canonical proof

The current proof of `matrixSdpCanonicalStrongDuality` has the following
mathematical structure.

1. The primal feasible set is compact and nonempty.  The proof uses
   `matrixSdpCanonicalPrimalFeasible_isCompact` and obtains a primal maximizer
   by `exists_isMaxOn`.

2. The dual feasible sublevel set is compact and nonempty.  The proof uses the
   strict witness \(Z = 2I\), the closedness of the dual feasible set, and the
   norm bound obtained from positivity and the trace.  This gives a dual
   minimizer.

3. The image cone
   `matrixSdpCanonicalPrimalImageCone` is a `ProperCone.map` of the positive
   semidefinite cone under the constraint-objective map
   \(X \mapsto (D(X), \operatorname{Re}\operatorname{Tr}(CX))\).

4. On the identity constraint fiber, membership in this image cone is
   equivalent to the existence of a feasible canonical primal matrix with the
   prescribed objective value.  This is the content of
   `matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective`.

5. If the dual optimum were strictly larger than the primal optimum, the point
   \((I,(p+d)/2)\) would lie outside the image cone.  Hyperplane separation
   gives a continuous real-linear functional on the product space.

6. Product decomposition of the separator gives a constraint-coordinate
   functional and an objective-coordinate coefficient.  The coefficient is
   negative, so the constraint functional can be normalized.

7. The normalized functional is represented by a Hermitian matrix under the real
   trace pairing.  This matrix is dual feasible and has objective value below
   \((p+d)/2\), contradicting minimality of the chosen dual optimum.

Steps 1--6 are conic-duality arguments.  Step 7 is the matrix specialization.

## Proposed reusable theorem

The natural reusable theorem is not initially a theorem about matrices.  It is a
finite-dimensional conic zero-gap theorem for a closed image cone.

A Lean theorem of the following shape would isolate the reusable part.  This is
schematic notation, not a proposed final declaration header.

```lean
theorem conic_zero_gap_of_closed_image_fiber
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [CompleteSpace E] [CompleteSpace F]
    (K : ProperCone Real E)
    (A : E ->L[Real] F)
    (c : E ->L[Real] Real)
    (b : F)
    (hFiber :
      forall t,
        (b, t) in K.map (A.prod c) <->
          exists x, x in K.toPointedCone /\ A x = b /\ c x = t)
    (hPrimalMax :
      exists x, x in K.toPointedCone /\ A x = b /\
        forall y, y in K.toPointedCone -> A y = b -> c y <= c x)
    (hDualMin :
      exists phi : StrongDual Real F,
        (forall x, x in K.toPointedCone -> c x <= phi (A x)) /\
        forall psi : StrongDual Real F,
          (forall x, x in K.toPointedCone -> c x <= psi (A x)) ->
          phi b <= psi b) :
    exists x phi,
      x in K.toPointedCone /\
      A x = b /\
      (forall y, y in K.toPointedCone -> A y = b -> c y <= c x) /\
      (forall y, y in K.toPointedCone -> c y <= phi (A y)) /\
      c x = phi b /\
      (phi.comp A - c) x = 0
```

The statement above deliberately asks for the identity-fiber characterization
as a hypothesis.  In the current canonical proof this is a nontrivial compact
subsequence argument, not a formal consequence of the abstract cone data alone.
Keeping it as a hypothesis makes the theorem reusable without concealing the
closed-image issue.

The compactness and attainment hypotheses may later be replaced by strict
feasibility assumptions if a finite-dimensional Slater theorem is developed.
That would be a stronger theorem-design task.  The present Section 9 proof
already has compact attainment, so it does not need that stronger abstraction.

## Matrix specialization needed for Section 9

The conic theorem would produce a continuous real-linear functional
\(\varphi\) on the constraint space.  For the Section 9 SDP, the constraint
space is the finite matrix space `MatrixOperator model.space`.  To recover the
paper dual variable, one must then use the existing quantum finite-matrix API:

- `MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM`;
- `MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian`;
- `MIPStarRE.Quantum.nonneg_of_trace_mul_nonneg_of_isHermitian`;
- `MIPStarRE.Quantum.mul_eq_zero_of_nonneg_of_trace_mul_eq_zero`.

These results turn the functional dual feasibility condition
\[
  c(X) \leq \varphi(A(X)) \qquad (X \in K)
\]
into the matrix inequality
\[
  D(Z)-C \succeq 0.
\]
They also turn the zero value of the dual slack functional on an optimal primal
point into the product equation
\[
  X(D(Z)-C)=0.
\]
After diagonal-block extraction and saturation of the slack block, this is the
paper-form complementary slackness equation
\[
  T_g Z = T_g A_g.
\]

Thus a reusable theorem sufficient for `lem:sdp` is really a two-stage theorem:

1. a conic zero-gap theorem returning a functional dual optimum and functional
   complementary slackness;
2. a finite-matrix specialization returning a Hermitian matrix dual optimum and
   matrix complementary slackness.

## Why the theorem should not replace the canonical proof yet

The paper-facing Section 9 output is stronger than equality of optimal values.
It needs a complete measurement \(\{T_g\}\), a dual operator \(Z\), dual
feasibility \(Z \succeq A_g\), and the equations \(T_gZ=T_gA_g\).  The
canonical Lean construction also records saturation of the slack block, so that
\(\sum_g T_g=I\) rather than merely \(\sum_gT_g \preceq I\).

A functional conic theorem alone does not give this saturated matrix witness.
It supplies the zero-gap and functional slackness part.  The canonical
block-SDP extraction and the saturation theorem remain project-specific:

- `MatrixSdpCanonicalOptimalPair.ofFeasibleStrongDualitySaturateSlackBlock`;
- `matrixSdpCanonicalSaturateSlackBlockMatrix`;
- `matrixSdpPointRealization_canonicalOptimalPair`;
- `sdp_statement_with_slackness`.

Consequently the current canonical proof should remain in place until the
general theorem and its matrix specialization can recover a
`MatrixSdpCanonicalOptimalPair` without adding dominance, residual, bridge, or
auxiliary hypotheses to the paper-facing statement.

## Recommended implementation sequence

1. Add a new internal module for functional conic duality, probably under
   `MIPStarRE/Quantum/FiniteConicDuality.lean` or under the Section 9
   strong-duality directory if the theorem is still too tailored to the
   canonical SDP.

2. First prove the product-separator lemmas generically: product functional
   decomposition, negativity of the objective coefficient, normalization of the
   constraint functional, and the contradiction with a dual minimizer.

3. State the conic zero-gap theorem with an explicit identity-fiber hypothesis.
   This mirrors the present use of
   `matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective`
   and avoids pretending that closed-image fiber recovery is automatic.

4. Specialize the theorem back to the canonical matrix SDP, obtaining the same
   conclusion as `matrixSdpCanonicalStrongDuality`.

5. Only after that specialization is proved, replace the body of
   `matrixSdpCanonicalStrongDuality`.  The public statement of
   `matrixSdpCanonicalStrongDuality`, `MatrixSdpCanonicalOptimalPair`, and
   `sdp_statement_with_slackness` should remain unchanged.

## Verdict

The reusable theorem is feasible, but the correct reusable unit is conic
zero-gap plus a matrix trace-pairing specialization, not a monolithic
paper-form SDP theorem.  The first Lean theorem should expose the functional
dual object and prove equality of primal and dual optima.  The Section 9
matrix witness and slack-block saturation should remain in the canonical
matrix-realization layer until a specialization theorem recovers the existing
paper-facing output exactly.
