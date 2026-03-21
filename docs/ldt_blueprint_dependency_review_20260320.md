# Structural strengths

- The rebuilt blueprint is much closer to the **actual proof-dependency order** than the TeX input order in `references/ldt-paper/multilinearity.tex`. For this paper that is a real advantage, because `inductive_step.tex` states `thm:main-induction`, `thm:self-improvement-in-induction-section`, and `thm:ld-pasting-in-induction-section` before the later files `expansion.tex`, `self_improvement.tex`, `commutativity-points.tex`, `commutativity-G.tex`, and `ld-pasting.tex` supply the machinery needed to justify them.

- The major theorem ownership is mostly good:
  - `ch04_projective.tex` owns `thm:naimark`, `lem:orthonormalization-main-lemma`, and `thm:orthonormalization`, matching `orthonormalization.tex`.
  - `ch05_expansion.tex` and `ch06_variance.tex` split `expansion.tex` exactly along its own internal section boundary: the hypercube/spectral material first, then `lem:generalize-b`, `lem:local-variance-of-points`, and `lem:global-variance-of-points`.
  - `ch08_commutativity.tex` correctly merges the two commutativity source files while preserving ownership of `thm:commutativity-points` (from `commutativity-points.tex`) and `lem:comm-data-processed-g`, `lem:normalization-condition`, `thm:com-main` (from `commutativity-G.tex`).
  - `ch09_pasting.tex` correctly centralizes the `ld-pasting.tex` chain.
  - `ch10_induction.tex` correctly leaves `thm:main-induction` in the induction chapter rather than pretending it is proved where it is first stated in source order.

- The source-map note `docs/ldt_source_map_20260320.md` is largely borne out by the blueprint: the visible route is
  `preliminaries -> projectivization -> expansion/variance -> self-improvement -> point commutativity -> slice commutativity -> pasting -> induction`.
  That is the right high-level picture for proof filling.

- The `ld-pasting` duplication was handled well. Comparing `thm:ld-pasting-in-induction-section` in `inductive_step.tex` with `thm:ld-pasting` in `ld-pasting.tex`, the statements are textually the same up to labels and formatting, so a single blueprint node for the mathematical statement is defensible here.

- The rebuilt pasting chapter exposes many of the real internal dependencies rather than treating `thm:ld-pasting` as a black box. In particular, `lem:g-complete-self-consistency`, `cor:g-bot-self-consistency`, `cor:G-hat-facts`, `lem:commute-g-half-sandwich`, `lem:h-b-consistency`, `lem:over-all-outcomes`, `lem:from-H-to-G`, `lem:chernoff-bernoulli-matrix`, and `cor:ld-pasting-N-completeness` make the critical path substantially more honest.

- The Bernoulli-tail exponent in `ch09_pasting.tex` is mathematically consistent: `F(X) = \sum_{r=d+1}^k \binom{k}{r} X^r (I-X)^{k-r}`. This avoids propagating the mirrored source typo in `references/ldt-paper/ld-pasting.tex` line 1674.

# Potential structural mismatches

- The blueprint is **not** a faithful mirror of the source-file order, despite the sentence in `ch01_overview.tex` that it “follows the source tree.” It follows theorem ownership and proof dependency much more than TeX input order. Concretely:
  - `inductive_step.tex` appears fifth in `multilinearity.tex`, but its main content is deferred to `ch10_induction.tex`.
  - `expansion.tex` is split into `ch05_expansion.tex` and `ch06_variance.tex`.
  - `commutativity-points.tex` and `commutativity-G.tex` are merged into `ch08_commutativity.tex`.
  - `introduction.tex` is compressed to `ch01_overview.tex`, and the classical context results `thm:raz-safra` and `thm:classical-test-soundness` are omitted entirely.

- The most serious mismatch is the merged `thm:self-improvement` node.
  - In `references/ldt-paper/inductive_step.tex`, `thm:self-improvement-in-induction-section` assumes
    `G \in \polysub{m}{q}{d}`.
  - In `references/ldt-paper/self_improvement.tex`, `thm:self-improvement` assumes
    `G \in \polymeas{m}{q}{d}`.
  - The blueprint node in `blueprint/src/chapter/ch07_self_improvement.tex` uses the **measurement** hypothesis, but its `\lean{...}` field points to both `Section6MainInductionStep.selfImprovementInInductionSection` and `Section9SelfImprovement.selfImprovement`.

  This is not merely a duplicate-label situation: the section-6 theorem is stronger on the input side. The source-map claim that a single node is used “even when the paper states it twice” is literally safe for `thm:ld-pasting`, but not for `thm:self-improvement`.

- Chapter 4 substantially understates the real dependency burden of `orthonormalization.tex`. The blueprint exposes only:
  - `thm:naimark`,
  - `lem:orthonormalization-main-lemma`,
  - `thm:orthonormalization`.

  But the source proof of `lem:orthonormalization-main-lemma` runs through a long internal chain including `lem:projective-non-measurement`, `lem:trunc-inequality`, `lem:projective-low-rank-sum`, `lem:Q-completeness`, `lem:sqrt-Q-completeness`, `lem:q-almost-projective`, and the SVD-based sequence `lem:qa-restated`, `lem:X-squared`, `lem:X-expression-to-Q-expression`, `lem:pa-restated`, `lem:X-hat-squared`, `lem:X-times-X-hat`, `lem:squared-difference`, `lem:P-projectivity`, `lem:P-Q-approx`. For dependency estimation, the current blueprint makes this chapter look cheaper than it is.

- There are a few likely missing or too-implicit dependency edges in the rebuilt blueprint:
  - The proof of `thm:main-formal` in `ch10_induction.tex` explicitly says that Schwartz--Zippel is used to turn pointwise agreement into self-consistency of the global measurements, but its `\uses{...}` list omits `lem:schwartz-zippel-individual`.
  - The proof paragraph for `lem:over-all-outcomes` in `ch09_pasting.tex` cites `lem:h-b-consistency` in prose, but the direct dependency list only names lower-level ingredients. This may be intentional, but it means the text-level and graph-level ownership are not perfectly aligned.

- Several blueprint nodes are blueprint-owned helper abstractions rather than paper-labeled results:
  - `lem:good-strategy-characterization` comes from `rem:good-strat-characterization` in `test_definition.tex`.
  - `def:rerandomize-coord` is extracted from the edge-sampling description in `expansion.tex`.
  - `def:adjacency-laplacian` merges two adjacent definitions.
  - `lem:ld-gbcon` promotes the displayed equation `eq:ld-gbcon` in `ld-pasting.tex` to a named dependency node.

  These are reasonable additions, but they should be treated as blueprint-local ownership, not as paper-labeled ownership.

- `blueprint/src/references.bib` is too small for the real dependency surface. It contains `Ji2020LowIndividualDegree`, `KV11`, `Sch80`, and `Zip79`, but not the external ingredients that the proof plan still depends on conceptually: the NW19-style measurement-comparison background used throughout `preliminaries.tex`, the scalar Chernoff source cited in `ld-pasting.tex`, and a standard convex-optimization source for the SDP duality/complementary-slackness step in `self_improvement.tex`.

# Dependency audit by chapter

## `blueprint/src/chapter/ch01_overview.tex`

- This is a selective overview, not a source-faithful mirror of `introduction.tex`.
- Dependency burden is low.
- The omitted introduction results are contextual only; I do not think they block formalization, but the chapter should be read as a compressed router, not a full source reconstruction.

## `blueprint/src/chapter/ch02_test.tex`

- The formal theorem node `thm:main-formal` is structurally in the right place.
- Likely existing support:
  - finite products, finite functions, tuples, `Fin`, basic combinatorics from Mathlib;
  - once one works over an honest finite field type, standard field/finite-type infrastructure.
- Likely local wrappers:
  - the paper-specific strategy structures (symmetric vs general projective strategies);
  - question distributions for the three subtests;
  - the packaging of point/line/diagonal-line answers and their evaluation relations.
- Substantial local development still needed:
  - the current `Paper2009LDT/Section3Test.lean` uses placeholder `QuantumState`, `Operator`, `Distribution`, and measurement structures, so the present Lean declaration is only a name scaffold.
- Genuinely external ingredients: none yet, apart from the overall theorem being a target for the rest of the paper.

## `blueprint/src/chapter/ch03_preliminaries.tex`

- This chapter is mathematically central. Almost every later chapter depends on its measurement language.
- Likely existing in Mathlib already:
  - finite-field infrastructure in `Mathlib.FieldTheory.Finite.Basic` and `Mathlib.FieldTheory.Finite.Trace`;
  - additive-character infrastructure in `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`;
  - multivariate polynomial infrastructure and a strong vanishing theorem in `Mathlib.Combinatorics.Nullstellensatz`;
  - matrix trace/Hermitian/PSD basics in `Mathlib.LinearAlgebra.Matrix.Trace`, `Mathlib.LinearAlgebra.Matrix.PosDef`, `Mathlib.Analysis.Matrix.Order`.
- Likely thin local wrappers:
  - the exact `\simeq_\delta`, `\approx_\delta`, and strong-self-consistency relations used in the paper;
  - postprocessing and completion of measurement families indexed by questions;
  - paper-specific overlap bookkeeping lemmas such as `prop:simeq-data-processing`, `prop:cons-sub-meas`, `prop:switch-sandwich`, `prop:completing-to-measurement`.
- Likely substantial new local development:
  - the quantum-information semantics of submeasurements on a bipartite state;
  - the comparison lemmas between `\simeq` and `\approx` in exactly the paper’s operator language.
- External/non-Mathlib ingredients:
  - the exact Schwartz--Zippel estimate used in the paper is not something I would expect to import verbatim; likely a short local proof or wrapper, possibly assisted by `Nullstellensatz`, but still not a one-line reuse.

## `blueprint/src/chapter/ch04_projective.tex`

- The blueprint ownership is correct, but the true proof burden is much larger than the visible graph suggests.
- Likely existing in Mathlib already:
  - Hermitian matrices, PSD order, trace positivity;
  - unitary diagonalization and eigenvalue API via `Mathlib.Analysis.Matrix.Spectrum`;
  - positive square roots and related CFC infrastructure via `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`, `Mathlib.Analysis.Matrix.Order`, and `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`;
  - the factorization `0 \le A \iff A = B^\* B` in matrix/C\*-algebra form.
- Likely thin local wrappers:
  - projectors as measurement outcomes;
  - complements `I-P`, completeness transfer lemmas, and the paper’s measurement-specific closeness predicates;
  - reusing the spectral theorem/CFC to define `A^{1/2}`, `|A|`, and other operator functions in paper notation.
- Likely substantial new local development:
  - the discontinuous spectral truncation in `lem:projective-non-measurement` (hard threshold at `1-\delta`) is not directly covered by continuous functional calculus;
  - the rank-reduction argument selecting the top overlaps;
  - the rectangular-matrix/SVD chain in the proof of `lem:orthonormalization-main-lemma`.
- Genuinely external/non-Mathlib ingredients:
  - textbook Naimark dilation for POVMs;
  - the Kempe--Vidick orthogonalization argument (`KV11`) as a proof template;
  - there is no ready-made POVM/Naimark API in Mathlib.

## `blueprint/src/chapter/ch05_expansion.tex`

- Structurally this chapter matches the first part of `expansion.tex` well.
- Likely existing in Mathlib already:
  - finite-field cardinality/Frobenius/trace support;
  - additive characters and vanishing of nontrivial character sums (`AddChar.sum_eq_zero_of_ne_one`, `AddChar.sum_mulShift`);
  - generic graph adjacency matrices and Laplacians for simple graphs (`Mathlib.Combinatorics.SimpleGraph.AdjMatrix`, `...LapMatrix`);
  - generic matrix spectral theory.
- Likely thin local wrappers:
  - the specific normalized random-walk adjacency operator `K = \mathbb E_{(u,v)\sim C} |u\rangle\langle v|`;
  - the Fourier basis on `\F_q^m` specialized to the paper’s normalization;
  - the local/global variance quadratic forms.
- Likely substantial new local development:
  - the explicit eigenvalue computation `\frac{1}{q^m}\frac{m-|\alpha|}{m}` for this weighted looped hypercube;
  - the exact local-to-global inequality `lem:local-to-global` in the paper’s normalization.
- External/non-Mathlib ingredients:
  - none in principle; this looks localizable from finite-field Fourier analysis plus Mathlib matrix support.

## `blueprint/src/chapter/ch06_variance.tex`

- This chapter matches the second section of `expansion.tex` and is structurally sound.
- Likely existing in Mathlib already:
  - matrix square roots (`CFC.sqrt`) once the effects are realized as PSD matrices;
  - finite sums and probability/expectation over finite types.
- Likely thin local wrappers:
  - evaluating a polynomial-valued submeasurement at a point and restricting to a line;
  - specialized uses of Schwartz--Zippel to compare `B^\ell_{[f(u)=g(u)]}` with `B^\ell_{g|_\ell}`.
- Likely substantial new local development:
  - the measurement-specific local variance estimate `lem:local-variance-of-points`;
  - the packaging of `A^u_{g(u)} \otimes (G_g)^{1/2}` as an honest state-dependent distance statement.
- External/non-Mathlib ingredients:
  - no new external theorem beyond Schwartz--Zippel.

## `blueprint/src/chapter/ch07_self_improvement.tex`

- This chapter is one of the highest-risk dependency nodes.
- Likely existing in Mathlib already:
  - matrix order, PSD comparison, trace identities, square roots, spectral calculus;
  - some convex-cone infrastructure, but not a ready SDP package.
- Likely thin local wrappers:
  - the finite-dimensional primal and dual semidefinite programs as operator-valued optimization problems;
  - the operator `A_g = \mathbb E_u A^u_{g(u)}` and the sandwiched family `H_h = \mathbb E_u A^u_{h(u)} T_h A^u_{h(u)}`;
  - boundedness statements of the form `Z \ge \mathbb E_u A^u_{h(u)}`.
- Likely substantial new local development:
  - actual duality and complementary slackness for the specific SDP in `lem:sdp`;
  - the repeated Cauchy--Schwarz / averaging manipulations in `lem:add-in-u`;
  - the transport of completeness, boundedness, and consistency through orthonormalization.
- Genuinely external/non-Mathlib ingredients:
  - finite-dimensional SDP duality, Slater-type conditions, and complementary slackness are not currently packaged in Mathlib in a reusable way;
  - this is literature-driven convex optimization, not just a thin wrapper.
- Structural warning:
  - this is also where the merged `thm:self-improvement` node hides the `\polysub` vs `\polymeas` discrepancy.

## `blueprint/src/chapter/ch08_commutativity.tex`

- The chapter split/merge is sensible and theorem ownership is correct.
- Likely existing in Mathlib already:
  - matrix multiplication, Hermitian conjugation, trace cyclicity, positivity, finite sums;
  - enough linear algebra to prove `lem:normalization-condition` once submeasurement semantics are honest.
- Likely thin local wrappers:
  - the evaluated slice measurements `G^{u,x}_a` and the paper’s consistency/boundedness hypotheses;
  - repeated use of state-dependent distance lemmas in a measurement-specific setting.
- Likely substantial new local development:
  - the approximate commutation estimates themselves (`thm:commutativity-points`, `lem:comm-data-processed-g`, `thm:com-main`);
  - the quartic-expression bookkeeping and the evaluation/removal steps via Schwartz--Zippel.
- External/non-Mathlib ingredients:
  - no obvious external black box beyond the paper’s own argument.

## `blueprint/src/chapter/ch09_pasting.tex`

- This is the single heaviest chapter in the blueprint, and the audit should treat it as such.
- Likely existing in Mathlib already:
  - binomial coefficients and finite combinatorics;
  - scalar binomial distributions via `Mathlib.Probability.ProbabilityMassFunction.Binomial`;
  - scalar Chernoff bounds via `Mathlib.Probability.Moments.Basic`;
  - PSD matrix order, positive square roots, operator functional calculus.
- Likely thin local wrappers:
  - the distinct-tuple distribution and its comparison with the uniform product distribution;
  - the completed measurement `\widehat G`, the sandwiched family `\widehat H`, and the outcome-type bookkeeping;
  - the operator polynomial `F(G) = \sum_{r=d+1}^k \binom{k}{r} G^r (I-G)^{k-r}`.
- Likely substantial new local development:
  - `lem:commutativity-switcheroo`, `lem:commute-g-half-sandwich`, and the whole repeated-commutation/sandwich framework;
  - the consistency route `\widehat H \to B \to A` (`lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`);
  - the recurrence in `lem:from-H-to-G` over types and sandwiched products;
  - the lift from scalar Chernoff to the matrix/operator statement `lem:chernoff-bernoulli-matrix`.
- Genuinely external/non-Mathlib ingredients:
  - there is no ready-made matrix Chernoff or matrix Bernstein library here;
  - the paper’s operator-valued Bernoulli-tail estimate must be built locally, even though the scalar concentration input exists in Mathlib.

## `blueprint/src/chapter/ch10_induction.tex`

- Structurally, putting `thm:main-induction` last is correct for proof filling.
- Likely existing in Mathlib already:
  - basic finite-type bookkeeping and symmetrization machinery;
  - all serious mathematics here should reduce to previously established local results.
- Likely thin local wrappers:
  - the `x`-restricted strategy construction;
  - the symmetrization/unsymmetrization argument in the proof of `thm:main-formal`.
- Likely substantial new local development:
  - the final assembly of the error bookkeeping;
  - the final passage from pointwise consistency to global measurement self-consistency.
- Structural warning:
  - the final proof text clearly uses Schwartz--Zippel, but the dependency list in the blueprint should say so explicitly.

# Likely Mathlib-supported pieces

- **Finite-dimensional complex matrix/operator layer**:
  - `Matrix.IsHermitian` in `Mathlib.LinearAlgebra.Matrix.Hermitian`;
  - `Matrix.PosSemidef`, `Matrix.PosSemidef.trace_nonneg`, `Matrix.posSemidef_conjTranspose_mul_self` in `Mathlib.LinearAlgebra.Matrix.PosDef`.

- **Trace identities and cyclicity**:
  - `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle` in `Mathlib.LinearAlgebra.Matrix.Trace`.

- **Hermitian spectral theory**:
  - `Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.eigenvectorUnitary` in `Mathlib.Analysis.Matrix.Spectrum`.

- **Positive square roots and operator functional calculus**:
  - `Matrix.IsHermitian.cfc` in `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`;
  - `CFC.sqrt`, `CFC.sqrt_nonneg`, `CFC.sq_sqrt` in `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`;
  - the matrix-order side in `Mathlib.Analysis.Matrix.Order`.

- **Finite fields and Frobenius/trace formulas**:
  - `FiniteField.card`, Frobenius infrastructure in `Mathlib.FieldTheory.Finite.Basic`;
  - `FiniteField.trace_to_zmod_nondegenerate`, `FiniteField.algebraMap_trace_eq_sum_pow` in `Mathlib.FieldTheory.Finite.Trace`.

- **Finite-field additive characters / Fourier inputs**:
  - `AddChar.FiniteField.primitiveChar_to_Complex`, `AddChar.sum_eq_zero_of_ne_one`, `AddChar.sum_mulShift` in `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`.

- **Polynomial vanishing machinery**:
  - `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` in `Mathlib.Combinatorics.Nullstellensatz` is a serious reusable ingredient, even if it does not directly replace the exact Schwartz--Zippel lemma used in the paper.

- **Scalar probability / concentration**:
  - `ProbabilityTheory.measure_ge_le_exp_mul_mgf` in `Mathlib.Probability.Moments.Basic`;
  - `PMF.binomial` in `Mathlib.Probability.ProbabilityMassFunction.Binomial`.

- **Generic graph adjacency/laplacian APIs (partial reuse only)**:
  - `SimpleGraph.adjMatrix` and `SimpleGraph.lapMatrix` in `Mathlib.Combinatorics.SimpleGraph.AdjMatrix` and `...LapMatrix`.
  - These are not a direct match for the paper’s weighted looped hypercube, but they show that graph-matrix infrastructure is available.

# Likely local-wrapper pieces

- The existing honest local matrix layer in:
  - `MIPStarRE/MIPStarRE/Quantum/FiniteMatrix.lean`,
  - `MIPStarRE/MIPStarRE/Quantum/Measurement.lean`,
  - `MIPStarRE/MIPStarRE/Quantum/OutcomeFamily.lean`.

  These already package useful paper-adjacent notions such as `Op d := Matrix d d ℂ`, a projector predicate `IsProj`, submeasurements/measurements, postprocessing, and overlap bookkeeping.

- A wrapper layer converting paper notation into the honest matrix API will likely be needed for:
  - point/line/diagonal-line measurement families;
  - postprocessed evaluations `G_{[g(u)=a]}`;
  - consistency, state-dependent distance, strong self-consistency, completeness, and boundedness.

- The paper’s finite-field notation will need wrappers around actual finite field types. The current `Parameters.q : ℕ` plus `Fq := Fin q` placeholder is not a mathematically adequate endpoint for formalization of `\F_q` as a field.

- Chapter 5 will need a paper-local Fourier wrapper turning Mathlib’s additive-character API into exactly the basis vectors
  `\ket{\varphi_\alpha}` and the orthogonality/eigenvalue lemmas used in `expansion.tex`.

- Chapter 4 will need wrappers around the spectral theorem/CFC to express:
  - square roots of PSD effects,
  - projector truncations,
  - spectral decompositions in the paper’s matrix notation,
  - “complete part / incomplete part” constructions for submeasurements.

- Chapter 9 will need local wrappers for:
  - distinct-tuple sampling,
  - the completed family `\widehat G`,
  - sandwiched measurement products,
  - the Bernoulli-tail operator polynomial.

# Likely missing or external pieces

- **Current `Paper2009LDT` Lean support is still scaffold-level, not semantic support.**
  - `MIPStarRE/MIPStarRE/Paper2009LDT/Section3Test.lean` introduces placeholder `QuantumState`, `Operator`, and `Distribution` objects.
  - Later files such as `Section7ExpansionHypercubeGraph.lean` and `Section12Pasting.lean` explicitly say they are lightweight scaffolds, and many statement wrappers are literally `Prop := True`.
  - The `Paper2009LDT` tree does not currently import the honest `MIPStarRE.Quantum.*` matrix layer at all.

- **No ready-made POVM / Naimark infrastructure** appears to be present in Mathlib.

- **No ready-made SVD or rectangular partial-isometry theorem** matching the proof pattern in `orthonormalization.tex` was evident from local search. The spectral theorem for Hermitian matrices exists, but the SVD-based chapter-4 chain is not a turnkey import.

- **No SDP duality / complementary slackness package** is available at the right level.
  - `Mathlib.Analysis.Convex.Cone.Basic` explicitly lists primal/dual cone programs, weak duality, and strong duality as future work.
  - So `lem:sdp` in `self_improvement.tex` should be treated as genuinely nontrivial local or externally guided development.

- **No off-the-shelf matrix Chernoff theorem** was found. The scalar concentration side is available, but `lem:chernoff-bernoulli-matrix` will still require a custom spectral reduction argument.

- **The exact normalized hypercube spectral package** is not present as a reusable library result. Generic graph APIs are weaker than what this paper uses.

- **The exact Schwartz--Zippel statement used repeatedly in the paper** is not obviously present under that name. This should be regarded as a short local development item rather than assumed Mathlib support.

- **External/literature-driven ingredients still worth recording explicitly**:
  - Kempe--Vidick orthogonalization (`KV11`);
  - textbook Naimark dilation;
  - a scalar Chernoff reference for the Bernoulli tail step in `ld-pasting.tex`;
  - a convex-optimization source for Slater/complementary slackness;
  - likely the NW19 measurement-comparison background that `preliminaries.tex` mirrors.

# Immediate recommendations before proof filling

1. **Do not treat the merged self-improvement node as literally safe.**
   Split it, or at minimum annotate it. `thm:self-improvement-in-induction-section` (`inductive_step.tex`) has input `G \in \polysub`, whereas `thm:self-improvement` (`self_improvement.tex`) is only stated for `G \in \polymeas`. This discrepancy is already reflected in `Section6MainInductionStep.lean` versus `Section9SelfImprovement.lean`.

2. **Choose the real semantic layer now, before proving late chapters.**
   The present `Paper2009LDT` declarations are useful as blueprint targets, but not as proof-ready objects. In particular:
   - `Fin q` should not be the final representation of `\F_q` if one needs honest field operations and finite-field trace/Frobenius;
   - string-valued placeholder `Operator`/`Distribution` objects should be replaced by real matrix/probability semantics.

3. **Rebase the LDT development onto the existing honest matrix API** in `MIPStarRE/MIPStarRE/Quantum/FiniteMatrix.lean` and `Quantum/Measurement.lean` rather than expanding the current placeholder API further.

4. **Make Chapter 4’s hidden burden explicit.**
   Even if the blueprint keeps only `lem:orthonormalization-main-lemma` and `thm:orthonormalization` as formal targets, add a dependency note (or internal checklist) for the omitted source lemmas in `orthonormalization.tex`. Otherwise the blueprint understates the actual linear-algebra work.

5. **Add the missing direct dependency edge from the final proof of `thm:main-formal` to `lem:schwartz-zippel-individual`.**
   The proof prose in `ch10_induction.tex` already uses it.

6. **Consider adding `lem:h-b-consistency` as an explicit dependency of `lem:over-all-outcomes`** if the proof text continues to cite it directly. The current graph is defensible but slightly misaligned with the prose.

7. **Record the non-Mathlib ingredients explicitly.**
   The present `references.bib` is too thin for later proof work. At minimum, I would want explicit bibliographic placeholders for:
   - the scalar Chernoff input used in `ld-pasting.tex`,
   - the SDP duality/complementary-slackness background for `lem:sdp`,
   - the NW19-style measurement-comparison background mirrored by `preliminaries.tex`.

8. **Treat `lem:chernoff-bernoulli-matrix` as an early standalone milestone.**
   It is both structurally central and mathematically separable. The natural implementation route is: scalar Chernoff / binomial in Mathlib + Hermitian spectral theorem + operator polynomial functional calculus.

9. **For the hypercube chapter, decide early whether to use generic graph APIs only opportunistically.**
   `SimpleGraph.adjMatrix`/`lapMatrix` exist, but the paper’s operator is a normalized weighted walk with loops. My expectation is that a custom matrix development will be cleaner than forcing the proof through `SimpleGraph` abstractions.

10. **If the chapter order is intentionally dependency-ordered rather than source-ordered, say that plainly in the documentation.**
    Right now `ch01_overview.tex` overstates source-tree faithfulness.
