# LDT Paper Summary

This summary covers all requested files in `references/ldt-paper/`:

- `introduction.tex`
- `preliminaries.tex`
- `orthonormalization.tex`
- `expansion.tex`
- `self_improvement.tex`
- `commutativity-points.tex`
- `commutativity-G.tex`
- `ld-pasting.tex`
- `inductive_step.tex`
- `multilinearity.tex`

It focuses on the mathematics that already maps, or is clearly intended to map, to `MIPStarRE/LDT/`.

Note: several chapters use the notion of an `(\epsilon,\delta,\gamma)`-good symmetric strategy for the low individual degree test. That test-level setup is defined outside the requested list, in `test_definition.tex`, and corresponds Lean-side to `MIPStarRE/LDT/Test/*`.

## Global proof architecture

The paper proves quantum soundness of the low individual degree test by induction on the ambient dimension `m`.

The proof pipeline is:

1. Restrict an `(m+1)`-dimensional strategy to each slice `x in F_q`, obtaining `m`-dimensional slice measurements `G^x`.
2. Use self-improvement to replace each slice measurement by a projective submeasurement with very small consistency error and controlled incompleteness.
3. Use commutativity results to show the slice measurements can be sequentially combined.
4. Use pasting/interpolation to turn the family `(G^x)_x` into a global measurement `H` on degree-`d` polynomials in `m+1` variables.
5. Track completeness and consistency through explicit polynomial-in-`m,k` error bounds.

The most Lean-relevant chapters are:

- `preliminaries.tex`
- `orthonormalization.tex`
- `expansion.tex`
- `self_improvement.tex`
- `commutativity-points.tex`
- `commutativity-G.tex`
- `ld-pasting.tex`
- `inductive_step.tex`

These align directly with the existing folders:

- `MIPStarRE/LDT/Preliminaries`
- `MIPStarRE/LDT/MakingMeasurementsProjective`
- `MIPStarRE/LDT/ExpansionHypercubeGraph`
- `MIPStarRE/LDT/GlobalVariance`
- `MIPStarRE/LDT/SelfImprovement`
- `MIPStarRE/LDT/CommutativityPoints`
- `MIPStarRE/LDT/Commutativity`
- `MIPStarRE/LDT/Pasting`
- `MIPStarRE/LDT/MainInductionStep`

## `introduction.tex`

**Lean relevance**

- High-level motivation for `MIPStarRE/LDT/MainInductionStep/*` and `MIPStarRE/LDT/Test/*`.
- No local formal definitions here beyond informal problem statements and theorem roadmaps.

**Key mathematical objects**

- Low total degree polynomial `g : F_q^m -> F_q`.
- Low individual degree polynomial `g : F_q^m -> F_q`.
- Surface-vs-point low degree test.
- Low individual degree test (axis-parallel lines).
- Quantum strategy with shared state `|psi>` and point measurements `A^u = {A^u_a}`.
- A global polynomial measurement `G = {G_g}` independent of the queried point.

**Key statements**

- Raz-Safra theorem:
  if provers pass the `k=2` surface-vs-point low degree test with probability `1 - epsilon`, then there exists a degree-`d` polynomial `g` with
  `Pr_u[g(u)=a_u] >= 1 - epsilon - poly(m) poly(d/q)`.

- Polishchuk-Spielman theorem:
  if provers pass the low individual degree test with probability `1 - epsilon`, then there exists an individual-degree-`d` polynomial `g` with
  `Pr_u[g(u)=a_u] >= 1 - poly(m)(poly(epsilon) + poly(d/q))`.

- Main theorem, informal:
  if the two-prover degree-`d` low individual degree test is passed with probability `1-epsilon`, then there exists a projective measurement `G = {G_g}` over individual-degree-`d` polynomials such that
  `E_u sum_a sum_{g:g(u)=a} <psi| A^u_a \otimes G_g |psi> >= 1 - poly(m)(poly(epsilon)+poly(d/q))`.

- Bad-example lower bound:
  the strategy based on `h(x_1,...,x_m)=x_1^{d+1}` passes with error `epsilon = 1/m`, yet any degree-`d` polynomial agrees with the point answers on at most
  `1 - m epsilon + (d+1)/q`.
  This shows the unavoidable `poly(m) poly(epsilon)` flavor of soundness for the individual-degree test.

**Proof strategy discussed**

- Start from the classical BFL induction: build measurements on larger and larger axis-aligned subspaces by interpolation.
- In the quantum setting, replace deterministic/randomized objects by submeasurements.
- Separate:
  consistency error = wrong answer when an answer is produced,
  completeness error = the submeasurement produces no answer.
- Use self-improvement to reset consistency to a universal small error `zeta`, at the cost of incompleteness.
- Use a diagonal-lines subtest to enforce approximate commutativity of point measurements.
- Run an induction on `m`, where each step is:
  slice restriction -> self-improvement -> pasting.

**Key bounds**

- Informal soundness error is `poly(m)(poly(epsilon)+poly(d/q))`.
- The introduction explains why the low individual degree test naturally accumulates `m`-dependent error, unlike the hoped-for low total degree bound.

## `preliminaries.tex`

**Lean mapping**

- `MIPStarRE/LDT/Preliminaries/Defs.lean`
- `MIPStarRE/LDT/Preliminaries/Theorems.lean`

Important Lean theorem names already scaffolded:

- `simeqForMeasurements`
- `simeqToApprox`
- `simeqDataProcessing`
- `consSubMeas`
- `switchSandwich`
- `completenessTransferProjectiveP`
- `twoNotionsOfSelfConsistency`
- `completingToMeasurement`

**Key definitions**

- Finite field trace:
  `tr[x] = sum_{ell=0}^{t-1} x^{p^ell}` for `F_q/F_p`.

- Low individual degree polynomials:
  `P(m,q,d)` = polynomials `F_q^m -> F_q` of individual degree at most `d`.

- Submeasurement:
  Hermitian PSD family `A = {A_a}` with `sum_a A_a <= I`.

- Projective submeasurement:
  `(A_a)^2 = A_a` for all `a`.

- Measurement:
  `sum_a A_a = I`.

- Polynomial submeasurements/measurements:
  `PolySub(m,q,d)`, `PolyMeas(m,q,d)`.

- Post-processing:
  `A_[f(a)=b] = sum_{a:f(a)=b} A_a`.

- Completion of a submeasurement:
  add an extra outcome `bot` with operator `I-A`.

- Consistency:
  `A^x_a \ot I \simeq_delta I \ot B^x_a` means
  `E_x sum_{a != b} <psi| A^x_a \ot B^x_b |psi> <= delta`.

- State-dependent distance:
  `A^x_a \approx_delta B^x_a` means
  `E_x sum_a ||(A^x_a - B^x_a)|psi>||^2 <= delta`.

- Strong self-consistency:
  `E_x sum_a <psi| A^x_a \ot A^x_a |psi> >= <psi|A \ot I|psi> - delta`.

**Key statements**

- Fourier orthogonality over `F_q`:
  `E_x omega^{tr[xa]} = 1` if `a=0`, else `0`.
  Vector version:
  `E_u omega^{tr[u·v]} = 1` if `v=0`, else `0`.

- Schwartz–Zippel:
  for distinct total-degree-`d` polynomials `g,h`,
  `Pr_x[g(x)=h(x)] <= d/q`.

- Individual-degree corollary:
  if `g,h in P(m,q,d)` are distinct, then
  `Pr_x[g(x)=h(x)] <= md/q`.

- Consistency for measurements:
  for measurements `A,B`,
  `A \simeq_delta B` iff
  `E_x sum_a <psi| A^x_a \ot B^x_a |psi> >= 1-delta`.

- Transfering consistency through `approx`:
  if `A \simeq_delta C` and `A \approx_eps B`, then
  `B \simeq_{delta + sqrt(eps)} C`.

- For measurements, `simeq` implies `approx`:
  `A \simeq_delta B => A \approx_{2 delta} B`.
  If both are projective, the implication is an equivalence.

- Generic inner-product transfer (`prop:closeness-of-ip`):
  if `A \approx_gamma B`, then weighted bilinear expressions involving `A` and `B` differ by at most `sqrt(gamma)` under a normalization hypothesis on the weights `C^x_{a,b}`.

- Simplified transfer:
  if `A,B,C` are submeasurements and `A \approx_delta B`, then
  `E_x sum_a <psi| A^x_a C^x_a |psi> approx_{sqrt(delta)} E_x sum_a <psi| B^x_a C^x_a |psi>`.

- Triangle inequalities:
  `approx`:
  chaining `k` steps incurs `k (delta_1+...+delta_k)`.
  `simeq`:
  if `A \simeq_eps B`, `C \simeq_delta B`, `C \simeq_gamma D`, then
  `A \simeq_{eps + 2 sqrt(delta+gamma)} D`.

- Data processing for `simeq`:
  post-processing preserves the same inconsistency bound.

- `prop:cons-sub-meas`:
  if `A` is a submeasurement and `B` is a measurement with `A \simeq_gamma B`, then
  `A^x_a \approx_gamma A^x_a B^x_a`,
  `A^x_a B^x_a \approx_gamma A^x B^x_a`,
  hence `A^x_a \approx_{4 gamma} A^x B^x_a`.

- Switch-sandwich:
  if projective `A` satisfies `A^x_a \ot I \approx_delta I \ot A^x_a`, then for `0 <= B <= I`,
  `E_x sum_a <psi| A^x_a B A^x_a \ot I |psi>`
  is within `2 sqrt(delta)` of
  `E_x sum_a <psi| B \ot A^x_a |psi>`
  and within `sqrt(delta)` of
  `E_x sum_a <psi| B A^x_a \ot I |psi>`.

- Completeness transfer to a projective approximation:
  if `A \approx_eps P` and `P` is projective, then
  `<psi|A \ot I|psi> >= <psi|P \ot I|psi> - 2 sqrt(eps)`.

- Strong self-consistency implies:
  `A \simeq_delta A`,
  `A \approx_{2 delta} A`,
  and post-processed versions inherit `approx_{2 delta}`.

- If `A` is strongly self-consistent and `A \approx_eps B`, then
  `<psi|B \ot I|psi> >= <psi|A \ot I|psi> - delta - 2 sqrt(eps)`.

- If strongly self-consistent `A` is approximated by projective `P`, then post-processing gives
  `P_[f(a)=b] \approx_{8 delta + 8 sqrt(eps)} A_[f(a)=b]`.

- Completing a near-measurement:
  if measurement `A` is strongly self-consistent and `B` is close to `A`,
  then adding `I-B` into one distinguished outcome yields a full measurement `C` with
  `A \approx_{2 delta + 4 sqrt(delta) + 2 zeta} C`.

**Proof strategy**

- Repeated Cauchy-Schwarz on bipartite expectation values.
- Convert inconsistency into matched-answer correlation and into squared-distance bounds.
- Use projectivity to turn quadratic expressions into linear ones.
- Post-processing is treated as a controlled functorial operation on measurements.

**Key bounds**

- `Schwartz–Zippel`: `d/q` and `md/q`.
- `simeq -> approx`: factor `2`.
- `A \simeq_delta C` plus `A \approx_eps B` gives `B \simeq_{delta+sqrt(eps)} C`.
- Strong self-consistency -> self-distance bound `2 delta`.
- Completion bound: `2 delta + 4 sqrt(delta) + 2 zeta`.

## `orthonormalization.tex`

**Lean mapping**

- `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`

Key Lean theorem names:

- `oneMeasNaimark`
- `naimark`
- `orthonormalization`
- `orthonormalizationMainLemma`
- `consistencyToAlmostProjective`
- `spectralTruncationStatement_of_sourceAlmostProjective`
- `leftLiftedProjectivizationRepair`

**Key definitions**

- Naimark dilation setup: enlarge the Hilbert spaces with local auxiliary registers and replace POVMs by projective measurements preserving outcome probabilities.
- Matrix decomposition for the orthogonalization proof:
  `Q_a = sum_i |v_{a,i}><v_{a,i}|`,
  `X_a = sum_i |a,i><v_{a,i}|`,
  `X = sum_a X_a`,
  `T_a = sum_i |a,i><a,i|`,
  SVD `X = U Sigma V^dagger`,
  idealized matrix `Xhat = U I V^dagger`,
  final projectors `P_a = Xhat_a^dagger Xhat_a`.

**Key statements**

- Naimark dilation:
  given submeasurements `A^x_a`, `B^y_b`, there exist enlarged projective measurements `Ahat`, `Bhat` and an auxiliary product state such that
  `<psi| A^x_a \ot B^y_b |psi> = <psihat| Ahat^x_a \ot Bhat^y_b |psihat>`.

- Orthogonalization theorem:
  if `A={A_a}` is strongly self-consistent with error `zeta`, then there exists a projective submeasurement `P={P_a}` such that
  `A_a \ot I \approx_{100 zeta^(1/4)} P_a \ot I`.

- Measurement-case orthogonalization lemma:
  if measurements `A,B` satisfy `A_a \ot I \simeq_zeta I \ot B_a`, then there exists projective submeasurement `P` with
  `A_a \ot I \approx_{84 zeta^(1/4)} P_a \ot I`.

- Rounding to projectors:
  from
  `sum_a <psi| (A_a - A_a^2) \ot I |psi> <= 2 zeta`,
  threshold eigenvalues at `1-delta` to obtain projectors `R_a` with
  `A_a \approx_{2 zeta / delta} R_a`
  and
  `R := sum_a R_a <= (1+2 delta) I`.
  Choosing `delta = sqrt(zeta)` yields
  `A_a \approx_{2 sqrt(zeta)} R_a`.

- Rank reduction:
  there exist projectors `Q_a` with
  `A_a \approx_{12 sqrt(zeta)} Q_a`,
  `Q := sum_a Q_a <= (1+2 sqrt(zeta)) I`,
  and `sum_a rank(Q_a) <= d`.

- Completeness of `Q`:
  `<psi|Q \ot I|psi> >= 1 - 11 zeta^(1/4)`.

- Completeness of `sqrt(Q)`:
  `<psi|sqrt(Q) \ot I|psi> >= 1 - 12 zeta^(1/4)`.

- `Q` almost projective:
  `sum_a (Q_a Q Q_a - Q_a) <= 4 sqrt(zeta) I`.

- `P` projective and close to `Q`:
  `Q_a \ot I \approx_{30 zeta^(1/4)} P_a \ot I`.

- Final combination:
  `A_a \approx_{12 sqrt(zeta)} Q_a` and `Q_a \approx_{30 zeta^(1/4)} P_a`
  imply
  `A_a \approx_{84 zeta^(1/4)} P_a`.

**Proof strategy**

- First show `A` is almost projective in average quadratic defect.
- Spectrally round each `A_a` to a projector `R_a`.
- Remove low-overlap eigendirections to control total rank and obtain `Q_a`.
- Encode the family `(Q_a)_a` into a rectangular matrix `X`, then compare `X` to the idealized partial isometry `Xhat`.
- Define `P_a` from `Xhat`; this repairs the overlap defects among the `Q_a`.

**Key bounds**

- Assume `zeta <= 1/4`.
- `A` looks projective:
  `sum_a <psi| (A_a - A_a^2) \ot I |psi> <= 2 zeta`.
- `R <= (1+2 sqrt(zeta)) I`.
- `sum_small overlaps <= 4 sqrt(zeta)`.
- `Q` completeness `>= 1 - 11 zeta^(1/4)`.
- `sqrt(Q)` completeness `>= 1 - 12 zeta^(1/4)`.
- `Q_a -> P_a` error `30 zeta^(1/4)`.
- final measurement-case orthogonalization error `84 zeta^(1/4)`, rounded in theorem statement to `100 zeta^(1/4)` for submeasurements.

## `expansion.tex`

**Lean mapping**

- `MIPStarRE/LDT/ExpansionHypercubeGraph/*`
- `MIPStarRE/LDT/GlobalVariance/*`

Key Lean theorem names:

- `laplacianRewrite`
- `eigenvectors`
- `laplacianSpectralGap`
- `localToGlobal`
- `localRewrite`
- `globalRewrite`

**Key definitions**

- Hypercube graph `C=(V,E)` with `V=F_q^m`; vertices are adjacent when they differ in at most one coordinate.
- Normalized adjacency matrix:
  `K = E_{(u,v)~C} |u><v|`.
- Laplacian:
  `L = (1/M) I - K`, where `M=q^m`.
- Local variance:
  `Var_local(A,psi) = (1/2) E_{(u,v)~C} <psi| (A^u-A^v)^2 \ot I |psi>`.
- Global variance:
  `Var_global(A,psi) = (1/2) E_{u,v} <psi| (A^u-A^v)^2 \ot I |psi>`.

**Key statements**

- Laplacian rewrite:
  `L = (1/2) E_{(u,v)~C} (|u>-|v>)(<u|-<v|)`.

- Fourier eigenbasis:
  `|phi_alpha> = M^{-1/2} sum_u omega^{tr[u·alpha]} |u>`.
  These form an orthonormal basis, and
  `K |phi_alpha> = (1/M) ((m-|alpha|)/m) |phi_alpha>`.

- Spectral gap:
  if `lambda_1 <= lambda_2 <= ...` are eigenvalues of `L`, then
  `lambda_1 = 0`, `lambda_2 = 1/(mM)`.

- Local-to-global variance:
  `Var_global(A,psi) <= m Var_local(A,psi)`.

- Generalize lines-to-points:
  for `G in PolySub(m,q,d)`,
  `B^ell_[f(u)=g(u)] \ot G_g^{1/2} approx_{md/q} B^ell_{g|_ell} \ot G_g^{1/2}`.

- Local variance of points:
  for `G in PolySub(m,q,d)`,
  `A^u_{g(u)} \ot G_g^{1/2} approx_{24 (epsilon + delta + md/q)} A^v_{g(v)} \ot G_g^{1/2}`
  on `(u,v)~C`.

- Global variance of points:
  same expression with independent `u,v`, but error
  `24 m (epsilon + delta + md/q)`.

**Proof strategy**

- Diagonalize the graph operator by finite-field Fourier characters.
- Rewrite variances as trace expressions against the Laplacian and the orthogonal complement to the constant eigenvector.
- Use the spectral gap `1/(mM)` to compare local and global variance.
- Use Schwartz–Zippel to replace a line polynomial answer by the evaluation of a global polynomial `g`.

**Key bounds**

- Spectral gap: `1/(m q^m)`.
- Local points variance:
  `24 (epsilon + delta + md/q)`.
- Global points variance:
  `24 m (epsilon + delta + md/q)`.

## `self_improvement.tex`

**Lean mapping**

- `MIPStarRE/LDT/SelfImprovement/Defs.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems.lean`

Key Lean theorem names:

- `sdp`
- `addInU`
- `selfImprovementHelper`
- `selfImprovement`

**Key definitions**

- Averaged point operator for a polynomial `g`:
  `A_g = E_u A^u_{g(u)}`.

- SDP primal:
  maximize `sum_g Tr(T_g A_g)`
  subject to `T_g >= 0`, `sum_g T_g <= I`.

- SDP dual:
  minimize `Tr(Z)`
  subject to `Z >= A_g` for all `g`.

- Complementary slackness at optimum:
  `T_g Z = T_g A_g`.

- Sandwiched submeasurement:
  `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`,
  then average:
  `H_h = E_u H^u_h`.

**Key statements**

- Self-improvement helper (non-projective output):
  if `G in PolyMeas(m,q,d)` satisfies
  `A^u_a \ot I \simeq_nu I \ot G_[g(u)=a]`,
  and
  `zeta = 100 m (epsilon^(1/2) + delta^(1/2) + (d/q)^(1/2))`,
  then there exists `H in PolySub(m,q,d)` such that:
  - completeness:
    `<psi|H \ot I|psi> >= (1-nu) - zeta`,
  - point consistency:
    `A^u_a \ot I \simeq_zeta I \ot H_[h(u)=a]`,
  - strong self-consistency:
    `sum_h <psi| H_h \ot H_h |psi> >= <psi|H \ot I|psi> - zeta`,
  - boundedness:
    there exists PSD `Z` with
    `<psi| Z \ot I |psi> - E_u sum_a <psi| A^u_a \ot H_[h(u)=a] |psi> <= zeta`
    and `Z >= E_u A^u_{h(u)}` for every polynomial `h`.

- SDP lemma:
  primal and dual are dual; there exists an optimal pair with `sum_g T_g = I` and `T_g Z = T_g A_g`.

- Add-in-u lemma:
  for any auxiliary submeasurement `M` and any family of selected pairs `S_u`,
  the average quantity with `M^u_o \ot H_h`
  is within `4 sqrt(zeta_variance)` of the quantity with
  `(A^u_{h(u)} M^u_o A^u_{h(u)}) \ot T_h`,
  where
  `zeta_variance = 24 m (epsilon + delta + md/q)`.

- Projective self-improvement theorem:
  if `G` is as above and
  `zeta = 3000 m (epsilon^(1/32) + delta^(1/32) + (d/q)^(1/32))`,
  then there exists a projective `H in PolySub(m,q,d)` such that:
  - completeness:
    `<psi|H \ot I|psi> >= (1-nu) - zeta`,
  - point consistency:
    `A^u_a \ot I \simeq_zeta I \ot H_[h(u)=a]`,
  - strong self-consistency:
    `H_h \ot I \approx_zeta I \ot H_h`,
  - boundedness:
    there exists PSD `Z` with
    `<psi| Z \ot (I-H) |psi> <= zeta`
    and `Z >= E_u A^u_{h(u)}`.

**Proof strategy**

- Solve the SDP to find an optimal measurement `T` and dominating operator `Z`.
- Define `H` by sandwiching `T_h` with the point projector `A^u_{h(u)}`.
- The `add-in-u` lemma is the key transport device: it lets one replace averaged `H_h` expressions by point-localized `A^u_{h(u)} T_h A^u_{h(u)}` expressions.
- Use the global variance bound from the hypercube chapter whenever `u` must be swapped with `v`.
- Finally, apply the orthogonalization lemma to turn `Hhat` into a projective submeasurement, then transfer completeness/consistency/boundedness through the approximation lemmas from preliminaries.

**Key bounds**

- `zeta_variance = 24 m (epsilon + delta + md/q)`.
- Helper-stage error:
  `100 m (epsilon^(1/2) + delta^(1/2) + (d/q)^(1/2))`.
- Projective-stage error:
  `3000 m (epsilon^(1/32) + delta^(1/32) + (d/q)^(1/32))`.
- Orthogonalization intermediary:
  `zhat_ortho = 100 zhat^(1/4)`.
- Data-processing intermediary:
  `zhat_dataprocess = 8 zhat + 8 sqrt(zhat_ortho)`.

## `commutativity-points.tex`

**Lean mapping**

- `MIPStarRE/LDT/CommutativityPoints/Defs.lean`
- `MIPStarRE/LDT/CommutativityPoints/Theorem.lean`

Key Lean theorem name:

- `commutativityPoints`

**Key mathematical object**

- Point measurements `A^u_a` at two independent points `u,v in F_q^m`.
- Diagonal-line measurement `L^ell`.

**Key statement**

- Commutativity of point measurements:
  on average over independent uniform `u,v`,
  `(A^u_a A^v_b) \ot I \approx_{32 gamma m} (A^v_b A^u_a) \ot I`.

**Proof strategy**

- The diagonal-lines test says point measurements are both approximately consistent with the same diagonal-line measurement.
- Convert those consistencies into `approx` bounds.
- Route the product `A^u_a A^v_b` through the projective line measurement `L^ell`, swap order there exactly, then transport back.

**Key bound**

- Final commutator error:
  `32 gamma m`.

## `commutativity-G.tex`

**Lean mapping**

- `MIPStarRE/LDT/Commutativity/Defs.lean`
- `MIPStarRE/LDT/Commutativity/Theorems.lean`

Key Lean theorem names:

- `commDataProcessedG`
- `comMain`
- `normalizationCondition`

**Key definitions**

- Evaluated slice outcome:
  `G^{u,x}_a := G^x_[g(u)=a]`.
- Families `Z^x` witnessing boundedness:
  `Z^x >= E_u A^{u,x}_{g(u)}` and
  `E_x <psi| (I-G^x) \ot Z^x |psi> <= zeta`.

**Key statements**

- Commutativity after evaluation:
  if the family `G^x` is point-consistent, strongly self-consistent, and bounded, then with
  `nu = 48 m (gamma^(1/2) + zeta^(1/2))`,
  one has
  `G^x_[g(u)=a] G^y_[h(v)=b] \ot I approx_nu G^y_[h(v)=b] G^x_[g(u)=a] \ot I`.

- Full commutativity of `G`:
  under the same hypotheses,
  `G^x_g G^y_h \ot I approx_nu G^y_h G^x_g \ot I`
  with
  `nu = 30 m (gamma^(1/4) + zeta^(1/4) + (d/q)^(1/4))`.

- Normalization condition:
  for a sandwiched family `C_{a,b} = Q_b P_a Q_b`, the sum of the square operators is bounded by `I`.
  This is the normalization hypothesis needed for repeated applications of `prop:closeness-of-ip`.

**Proof strategy**

- For evaluated commutativity:
  expand the commutator square into two main terms.
  Show the second term is close to the first by repeatedly:
  - replacing evaluated `G` by `G^x \ot A^{u,x}_a`,
  - commuting the point operators using `commutativity-points`,
  - using boundedness to control terms containing `(I-G^x)`.

- For full `G` commutativity:
  specialize the full-slice operators at random points `u,v`,
  compare with the evaluated commutator statement,
  then remove the evaluation using Schwartz–Zippel:
  distinct polynomials agree at a random point with probability at most `md/q`.

**Key bounds**

- Evaluated commutation:
  `48 m (gamma^(1/2) + zeta^(1/2))`.
- Full commutation:
  `30 m (gamma^(1/4) + zeta^(1/4) + (d/q)^(1/4))`.
- Schwartz–Zippel losses appear as `dm/q`.

## `ld-pasting.tex`

**Lean mapping**

- `MIPStarRE/LDT/Pasting/Defs.lean`
- `MIPStarRE/LDT/Pasting/Theorems.lean`
- `MIPStarRE/LDT/Pasting/Statements.lean`
- `MIPStarRE/LDT/Pasting/Sandwich.lean`

Key Lean theorem names:

- `ldPasting`
- `ldPastingSubMeas`
- `ldDnoteq`
- `looksEasyButTookMeAWhile`
- `gCompleteSelfConsistency`
- `gBotSelfConsistency`
- `commutativitySwitcheroo`
- `commutingWithGComplete`
- `commutingWithGIncomplete`
- `gHatFacts`
- `commuteGHalfSandwich`
- `ldSandwichLineOnePoint`
- `hBConsistency`
- `overAllOutcomes`
- `fromHToG`
- `chernoffBernoulliMatrix`
- `ldPastingNCompleteness`

**Key definitions**

- Distinct tuples:
  `Distinct_k = {(x_1,...,x_k) : x_i != x_j for i != j}`.

- Complete and incomplete parts:
  `G^x = sum_g G^x_g`,
  `G^x_bot = I - G^x`,
  `Ghat^x` is the completed measurement with outcomes `Poly(m,q,d) union {bot}`.

- Type `tau in {0,1}^k`:
  `tau_i = 1` means the `i`-th completed measurement returned a genuine polynomial, `0` means `bot`.

- First pasting construction:
  sandwich exactly `d+1` slice measurements and interpolate.

- Second pasting construction:
  sandwich `k` completed measurements `Ghat^{x_i}`,
  keep only tuples with type weight `|tau| >= d+1`,
  and interpolate only on the coordinates where `tau_i = 1`.

- Sandwiched measurement:
  `Hhat^{x_1,...,x_k}_{g_1,...,g_k} = Ghat^{x_1}_{g_1} ... Ghat^{x_k}_{g_k} ... Ghat^{x_1}_{g_1}`.

- Pasted submeasurement:
  `H_h = E_{(x_1,...,x_k) in Distinct_k} sum_{w:|w|>=d+1} Hhat_{h_w}^{x_1,...,x_k}`.

- Bernoulli-tail operator:
  `F(X) = sum_{r=d+1}^k binom(k,r) X^r (I-X)^{k-r}`.

**Key statements**

- Main pasting theorem:
  if slice submeasurements `G^x` are complete up to `kappa`, point-consistent with error `zeta`, strongly self-consistent, and bounded, and if
  `nu = 100 k^2 m (epsilon^(1/32)+delta^(1/32)+gamma^(1/32)+zeta^(1/32)+(d/q)^(1/32))`,
  `sigma = kappa (1 + 1/(100m)) + 2 nu + exp(-k/(80000 m^2))`,
  then there exists `H in PolyMeas(m+1,q,d)` with
  `A^u_a \ot I \simeq_sigma I \ot H_[h(u)=a]`.

- Intermediate submeasurement version:
  there exists `H in PolySub(m+1,q,d)` with
  point consistency error `nu` and completeness
  `>= 1 - kappa (1 + 1/(100m)) - nu - exp(-k/(80000 m^2))`.

- Distributional comparison:
  `d_TV(Uniform(F_q^k), Distinct_k) <= k^2/q`.

- Scalar interpolation inequality:
  for `0 <= lambda <= 1`,
  `lambda (1-lambda^d) <= 2 (lambda^{d+1}(1-lambda))^{1/(d+1)}`.

- `G` complete-part self-consistency:
  `G^x \ot I approx_zeta I \ot G^x`.

- `G_bot` self-consistency:
  `G^x_bot \ot I approx_zeta I \ot G^x_bot`.

- Switcheroo lemma:
  if `M` commutes with each `G^x_g`, then `M` commutes with `G^x` itself, with explicit error
  `6 sqrt(zeta) + 6 sqrt(omega) + 4 sqrt(chi)`.

- Commutativity of complete and incomplete parts:
  `G^x_g G^y approx ... G^y G^x_g`,
  `G^x G^y approx ... G^y G^x`,
  and corresponding `bot` versions.

- Combined `Ghat` facts:
  `Ghat^x_g \approx_{2 zeta} Ghat^x_g` across tensor factors and
  `Ghat^x_g Ghat^y_h approx_{nu_3} Ghat^y_h Ghat^x_g`
  with
  `nu_3 = 138 m (zeta^(1/16)+gamma^(1/16)+(d/q)^(1/16))`.

- Commute past multiple `Ghat`s:
  moving the first factor to the far right in a product of length `k` costs
  `nu_4 = 426 k^2 m (gamma^(1/16)+zeta^(1/16)+(d/q)^(1/16))`.

- Sandwich consistency with lines:
  for each coordinate `i`,
  the `i`-th non-`bot` output of `Hhat` is consistent with the line measurement `B` up to
  `nu_5 = 43 k m (epsilon^(1/32)+delta^(1/32)+gamma^(1/32)+zeta^(1/32)+(d/q)^(1/32))`.

- `H` consistent with `B`:
  `H_[h|_u=f] \ot I \simeq_{nu_6} I \ot B^u_f`
  with
  `nu_6 = 44 k^2 m (...)`.

- Therefore `H` consistent with points:
  `H_[h(u,x)=a] \ot I \simeq_nu I \ot A^{u,x}_a`.

- Completeness reduction to Bernoulli tail:
  `overAllOutcomes` and `fromHToG` show
  `<psi|H \ot I|psi>` is close to `<psi|F(G) \ot I|psi>`.

- Matrix Chernoff/Bernoulli lemma:
  if `0 <= X <= I`, `k >= 2d/theta`, and `<psi|X \ot I|psi> >= 1-kappa`, then
  `<psi|F(X) \ot I|psi> >= 1 - kappa/(1-theta) - exp(-theta^2 k/2)`.

- Final completeness corollary:
  taking `theta = 1/(200m)` and `k >= 400md` yields
  `<psi|H \ot I|psi> >= 1 - kappa(1 + 1/(100m)) - nu - exp(-k/(80000 m^2))`.

**Proof strategy**

- The first construction is conceptually natural but completeness is hard to control.
- The second construction introduces `bot` and uses many samples `k`, so completeness becomes a binomial-tail problem.
- Establish self-consistency and commutation for the completed family `Ghat`.
- Show each coordinate of the sandwiched object is line-consistent, then aggregate to get `H` vs `B`.
- Use line consistency plus preliminaries to recover `H` vs `A`.
- For completeness, reduce the sum over all successful interpolatable tuples to an operator-valued Bernoulli tail `F(G)` and apply a matrix Chernoff bound.

**Key bounds**

- TV loss: `k^2/q`.
- `nu_1 = zeta + sqrt(8 m epsilon + 4 delta)`.
- `nu_com = 30 m (gamma^(1/4)+zeta^(1/4)+(d/q)^(1/4))`.
- `nu_2 = 36 m (gamma^(1/16)+zeta^(1/16)+(d/q)^(1/16))`.
- `nu_3 = 138 m (gamma^(1/16)+zeta^(1/16)+(d/q)^(1/16))`.
- `nu_4 = 426 k^2 m (gamma^(1/16)+zeta^(1/16)+(d/q)^(1/16))`.
- `nu_5 = 43 k m (...)`.
- `nu_6 = 44 k^2 m (...)`.
- `nu_7 = 46 k^2 m (...)`.
- `nu_8 = 46 k m (...)`.
- final completeness:
  `1 - kappa (1 + 1/(100m)) - nu - exp(-k/(80000 m^2))`.

## `inductive_step.tex`

**Lean mapping**

- `MIPStarRE/LDT/MainInductionStep/Defs.lean`
- `MIPStarRE/LDT/MainInductionStep/Statements.lean`
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`

Key Lean theorem names:

- `mainInduction`
- `selfImprovementInInductionSection`
- `ldPastingInInductionSection`
- `restrictedProbabilities`

**Key definitions**

- Main induction hypothesis:
  for an `(m,q,d)` strategy there exists a global polynomial measurement `G`.

- `append_x(ell)`:
  embeds a line `ell subset F_q^m` into the slice `{(u,x)}` in `F_q^{m+1}`.

- `x`-restricted strategy:
  fix the last coordinate to `x` and induce an `(m,q,d)` strategy on the slice.

- Restricted failure probabilities:
  `epsilon_x`, `delta_x`, `gamma_x` for the restricted strategy at slice `x`.

**Key statements**

- Main induction theorem:
  the paper states that if `(psi,A,B,L)` is `(epsilon,delta,gamma)`-good for
  `(m,q,d)` and `k >= md`, then there exists
  `G in PolyMeas(m,q,d)` such that
  `A^u_a \ot I \simeq_sigma I \ot G_[g(u)=a]`,
  where
  `sigma = m^2 (nu + exp(-k/(80000 m^2)))`,
  `nu = 1000 k^2 m^2 (epsilon^(1/1024)+delta^(1/1024)+gamma^(1/1024)+(d/q)^(1/1024))`.
  Issue #906 records that the proof later invokes pasting with the stronger
  side condition `k >= 400md`; the current blueprint/Lean public statement uses
  this stronger formal hypothesis rather than treating the intermediate range as
  proved.

- Section-level self-improvement theorem:
  restates the chapter-9 projective self-improvement theorem in the induction notation.

- Section-level pasting theorem:
  restates the chapter-12 pasting theorem in the induction notation.

- Restricted probabilities lemma:
  averaging slice errors over `x`,
  `E_x epsilon_x <= ((m+1)/m) epsilon`,
  `E_x delta_x <= delta`,
  `E_x gamma_x <= ((m+1)/m) gamma`.

**Proof strategy**

- Induct on `m`.
- Base case `m=1`: the unique line measurement already gives the global measurement.
- Induction step from `m` to `m+1`:
  - restrict to each slice `x`,
  - apply the induction hypothesis to get `G^x`,
  - self-improve each `G^x` to a projective submeasurement `Ghat^x`,
  - average the slice error parameters using concavity of `t -> t^c`,
  - apply the pasting theorem to the family `(Ghat^x)_x`.

- The opening part of the chapter also explains how to pass from the symmetric induction statement to the full two-prover main theorem:
  symmetrize the original strategy using a role register, apply the induction theorem, unsymmetrize, then orthogonalize and complete the resulting measurements.

**Key bounds**

- Induction hypothesis:
  `nu = 1000 k^2 m^2 (epsilon^(1/1024)+delta^(1/1024)+gamma^(1/1024)+(d/q)^(1/1024))`.
- `sigma = m^2 (nu + exp(-k/(80000 m^2)))`.
- Slice-averaged self-improvement error:
  `zeta = 3000 (m+1) (epsilon^(1/32)+delta^(1/32)+(d/q)^(1/32))`.
- The chapter proves `zeta <= nu` under the regime used in the induction.
- After pasting:
  `sigma* <= (m+1)^2 (nu + exp(-k/(80000 (m+1)^2)))`,
  which closes the induction with the same form of bound.

## `multilinearity.tex`

**Lean relevance**

- This is the master TeX file for the paper rather than a mathematical chapter.
- It includes the requested chapter files and also `test_definition.tex`, which was not part of the requested read list.

**Mathematical content**

- The abstract states the headline result:
  the two-player low individual degree test is quantum sound, sufficient to recover applications that previously used the now-invalid low-degree analysis, including `MIP* = RE`.
- No new lemmas, definitions, or proofs appear here beyond the abstract and chapter inclusions.

## Most important Lean-facing takeaways

1. The formal core is not the high-level soundness statement; it is the chain of quantitative operator lemmas:
   preliminaries -> projectivization -> variance/expansion -> self-improvement -> commutativity -> pasting -> main induction.

2. The central reusable objects are:
   `ConsRel`/`SDDRel`-style closeness notions,
   strong self-consistency,
   polynomial submeasurements,
   averaged point-evaluation operators `E_u A^u_{h(u)}`,
   slice-indexed families `G^x`,
   completed families `Ghat^x`,
   and Bernoulli-tail operators `F(G)`.

3. The key error-propagation pattern is:
   local test error -> `zeta` via self-improvement -> `nu` via pasting -> `sigma` via induction.
   Every chapter is set up to keep those transformations explicit.

4. The heaviest formalization pressure points are:
   repeated Cauchy-Schwarz transfers,
   converting `simeq` to `approx` and back,
   operator monotonicity/positivity in sandwich arguments,
   Schwartz–Zippel applications for removing evaluation,
   and the matrix-valued Chernoff/Bernoulli tail estimate in pasting.
