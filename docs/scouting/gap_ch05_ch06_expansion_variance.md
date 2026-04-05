# Gap Analysis for Chapter 05-06: Expansion and Global Variance

## Scope

Files reviewed:

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization.lean`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean`
- `MIPStarRE/LDT/GlobalVariance/Defs.lean`
- `MIPStarRE/LDT/GlobalVariance/MatrixRealization.lean`
- `MIPStarRE/LDT/GlobalVariance/Theorems.lean`

Build check:

- `lake build MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems` succeeds, with `sorry` warnings in `ExpansionHypercubeGraph/Theorems.lean`.
- `lake build MIPStarRE.LDT.GlobalVariance.Theorems` succeeds, with `sorry` warnings in both `ExpansionHypercubeGraph/Theorems.lean` and `GlobalVariance/Theorems.lean`.

## Executive summary

- The blueprint covers all of the main named results from the paper for these chapters.
- The paper has 22 labels in `expansion.tex`; 12 of them reappear verbatim in the blueprint and 10 do not.
- The missing labels are almost entirely proof-granularity artifacts: section labels, item labels inside propositions, and intermediate equations.
- The blueprint statements generally match the paper statements well, but the proofs are much more compressed and omit several nontrivial intermediate equalities that matter for a Lean implementation.
- On the Lean side, the Fourier/spectral setup in `ExpansionHypercubeGraph/Defs.lean` is fairly substantial and free of `sorry`, but the chapter-level theorem layer still has key `sorry` gaps.
- `GlobalVariance/Defs.lean` has a good abstract API, but the theorem layer still has many `sorry` sites, and the matrix-realization layer is a deliberate placeholder in a few places rather than a literal transcription of the paper.

## 1. Expansion in the hypercube graph

### 1.1 Paper labels and blueprint coverage

| Paper label | Kind | In blueprint? | Notes |
| --- | --- | --- | --- |
| `sec:expansion` | section | No | Replaced by chapter label `chap:expansion` and unlabeled section text. |
| `prop:laplacian-rewrite` | proposition | Yes | Same label in `ch05_expansion.tex`. |
| `prop:eigenvectors` | proposition | Yes | Same label in `ch05_expansion.tex`. |
| `item:orthonormal` | proposition item | No | Merged into `prop:eigenvectors` statement body. |
| `item:eigenvector` | proposition item | No | Merged into `prop:eigenvectors` statement body. |
| `eq:eigenvector-calculation` | equation | No | Proof-level computation omitted from blueprint. |
| `cor:laplacian-spectral-gap` | corollary | Yes | Same label in `ch05_expansion.tex`. |
| `def:local-and-variance` | definition | Yes | Same label in `ch05_expansion.tex`. |
| `lem:local-to-global` | lemma | Yes | Same label in `ch05_expansion.tex`. |
| `lem:local-rewrite` | lemma | Yes | Same label in `ch05_expansion.tex`. |
| `eq:reader-probably-has-no-idea-whats-going-on-yet` | equation | No | Key bridge equation omitted from blueprint proof. |
| `lem:global-rewrite` | lemma | Yes | Same label in `ch05_expansion.tex`. |
| `eq:just-took-trace` | equation | No | Intermediate variance identity omitted from blueprint proof. |
| `eq:used-0-eigenvector` | equation | No | Critical decomposition step omitted from blueprint proof. |

### 1.2 Exact statements for labels missing from the blueprint

- `sec:expansion`

  `Expansion in the hypercube graph`

- `item:orthonormal`

  `The \ket{\varphi_\alpha}'s form an orthonormal basis of \C^V.`

- `item:eigenvector`

  `For each \alpha \in \F_q^m, \ket{\varphi_\alpha} is an eigenvector for~K with eigenvalue~\frac{1}{M} \cdot  \frac{m - |\alpha|}{m}, where |\alpha| is the number of nonzero coordinates in~\alpha.`

- `eq:eigenvector-calculation`

```tex
K \cdot \ket{\varphi_\alpha}
= \left(\E_{(\bu, \bv) \sim C} \ket{\bu}\bra{\bv}\right) \cdot \bigg(\frac{1}{M^{1/2}} \cdot \sum_{u \in \F_q^m} \omega^{\mathrm{tr}[u \cdot \alpha]}\cdot \ket{u}\bigg)\\
= \frac{1}{M^{1/2}} \cdot \E_{(\bu, \bv) \sim C} \omega^{\mathrm{tr}[\bv \cdot \alpha]} \ket{\bu}.
```

- `eq:reader-probably-has-no-idea-whats-going-on-yet`

```tex
((\bra{u} - \bra{v}) \otimes \bra{\psi})\cdot A_{\mathrm{combine}}
=  \bra{\psi}\cdot  ((A^u- A^v) \otimes I).
```

- `eq:just-took-trace`

```tex
\frac{1}{M} \cdot \mathrm{Tr}(\bra{\varphi_{\perp}} \otimes A_{\perp} \cdot (I \otimes \ket{\psi}\bra{\psi}) \cdot \ket{\varphi_{\perp}} \otimes A_{\perp})
= \E_{\bu \sim \F_q^m} \bra{\psi} (A^{\bu} - A_{\mathrm{avg}})^2 \otimes I \ket{\psi}.
```

- `eq:used-0-eigenvector`

```tex
A_{\mathrm{combine}}^\dagger \cdot L \otimes \ket{\psi}\bra{\psi} \cdot A_{\mathrm{combine}}
= \bra{\varphi_{\perp}} L \ket{\varphi_{\perp}} \cdot A_{\perp}  \ket{\psi}\bra{\psi}  A_{\perp}.
```

### 1.3 Do the blueprint statements match the paper?

#### `prop:laplacian-rewrite`

Match: yes. The blueprint statement is the same formula, with notation normalized from `M` to `q^m` through the earlier definition.

#### `prop:eigenvectors`

Match: yes at theorem level.

Notes:

- The blueprint folds the paper's two item labels `item:orthonormal` and `item:eigenvector` into a single displayed statement.
- The normalization `q^{-m/2}` is equivalent to `M^{-1/2}`.
- The blueprint adds explicit supporting lemmas `lem:character-average-scalar` and `lem:character-average-vector`, which makes the formalization path clearer than the paper.
- The missing gap is not the theorem statement but the omitted intermediate computation `eq:eigenvector-calculation`.

#### `cor:laplacian-spectral-gap`

Match: yes. The blueprint states exactly the same ordered-eigenvalue conclusion.

#### `def:local-and-variance`

Match: yes. The formulas are the same.

Minor difference:

- The paper says explicitly that `\ket{\psi}` need not be normalized and that `0 \le A^u \le I` for each `u` in the section preamble; the blueprint folds those assumptions into the definition statement itself.

#### `lem:local-rewrite`

Match: yes. The displayed trace formula matches the paper.

Gap:

- The proof is compressed to one sentence and omits the crucial bridge equation `eq:reader-probably-has-no-idea-whats-going-on-yet`.

#### `lem:global-rewrite`

Match: yes at the displayed equality level.

Gap:

- The paper proves this by explicitly extracting `A_0`, identifying the average operator `A_{\mathrm{avg}}`, and rewriting the fluctuation square as a pairwise variance.
- The blueprint compresses all of that into: "The `\ket{\varphi_0}` component is the average operator ...".
- The missing labels `eq:just-took-trace` and the subsequent square-expansion chain are exactly the steps that a Lean proof will need.

#### `lem:local-to-global`

Match: yes at the inequality level.

Gap:

- The paper proof isolates the orthogonal Fourier mode and inserts the spectral-gap lower bound through `eq:used-0-eigenvector`.
- The blueprint gives only the high-level proof plan and omits the explicit mode decomposition calculation.

### 1.4 Lean coverage and proof-structure assessment

#### `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`

What is present:

- The basic graph/distribution objects are defined: `rerandomizeCoord`, `independentPointPair`, `adjacency`, `laplacian`, `localVariance`, `globalVariance`.
- Fourier objects are defined explicitly: `addCharFq`, `dotProductFq`, `fourierBasisState`, `adjacencyEigenvalue`, `laplacianEigenvalue`, `hypercubeSpectralGap`.
- Theorems `eigenvectors` and `laplacianSpectralGap` are fully proved without `sorry`.

Where the proof structure matches the paper:

- The eigenvector calculation really does go through the adjacency matrix action and the rerandomization update sum.
- The proof uses supporting character-sum lemmas in the same general way as the paper's Fourier argument.
- The spectral gap proof packages the relation between adjacency and Laplacian eigenvalues and identifies the gap at Hamming weight `1`.

Where it diverges from the paper:

- `laplacianRewrite` is not proved by expansion of marginals as in the paper; `laplacianDifferenceForm` is simply defined to be `laplacian`, so the theorem in `Theorems.lean` is `rfl`.
- `fourierBasisInnerProduct` is itself defined as `if α = β then 1 else 0`, and `eigenvectors.orthonormality` is proved by `rfl`. So the orthogonality statement is packaged, but not derived from the actual vector formula `fourierBasisState`.
- `laplacianSpectralGap` does not literally state "`\lambda_1 = 0` and `\lambda_2 = 1/(mM)`"; instead it provides a more usable package:
  - `eigenvalueRelation`
  - `positiveModesLowerBound`
  - `unitWeightModesAttainGap`
  This is enough for the later expansion argument, but it is not a direct formalization of the paper's sorted-spectrum statement.

#### `MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization.lean`

What is present:

- Concrete matrix-level versions of local/global variance, the combined operator, and the trace witnesses.
- Matrix statement packages `MatrixLocalRewriteStatement` and `MatrixGlobalRewriteStatement`.

Gap relative to the paper:

- The matrix layer records the trace witnesses but does not prove the rewrite lemmas.
- The global trace witness is phrased via the orthogonal projector `I - |φ_0><φ_0|`, not via an explicit decomposition `|φ_\perp> \ot A_\perp`.

#### `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean`

`sorry` sites:

- `matrixLocalToGlobal` at line 90
- `matrixLocalRewrite` at line 96
- `matrixGlobalRewrite` at line 102

Consequences:

- The public chapter theorems `localToGlobal`, `localRewrite`, and `globalRewrite` are only wrappers around these unfinished matrix lemmas.
- So the blueprint-facing theorems exist and compile, but the core proofs for the chapter are still missing.

Proof-structure match assessment:

- `localToGlobal` wrapper matches the paper's intended structure: reduce to a matrix model, then compare local and global forms.
- `globalRewrite` is materially weaker than the paper's proof structure. The statement only asks for existence of a decomposition, and the wrapper uses `default` as a witness because the underlying theorem only proves equality of trace forms, not a concrete decomposition tied to `A_{\mathrm{comb}} = |φ_0> \ot A_0 + |φ_\perp> \ot A_\perp`.

### 1.5 Nontrivial intermediate equations in the paper

These `eq:` labels are not just cosmetic; they encode proof steps likely to matter in Lean:

- `eq:eigenvector-calculation`
  - Starts the actual computation of `K |φ_α>`.
  - Important because it rewrites the operator action into an expectation over sampled edges.

- `eq:reader-probably-has-no-idea-whats-going-on-yet`
  - Key bridge from the combined operator `A_{\mathrm{combine}}` to the squared difference operator `(A^u - A^v)^2`.
  - This is the main algebraic identity behind `lem:local-rewrite`.

- `eq:just-took-trace`
  - Converts the orthogonal Fourier mass into the fluctuation average around `A_{\mathrm{avg}}`.
  - This is the exact point where the paper moves from a decomposition identity to a variance identity.

- `eq:used-0-eigenvector`
  - Removes the constant Fourier mode and isolates the orthogonal component.
  - This is the main spectral step used in `lem:local-to-global`.

## 2. Global variance of the points measurements

### 2.1 Paper labels and blueprint coverage

| Paper label | Kind | In blueprint? | Notes |
| --- | --- | --- | --- |
| `sec:variance` | section | No | Replaced by chapter label `chap:variance`. |
| `lem:generalize-b` | lemma | Yes | Same label in `ch06_variance.tex`. |
| `lem:local-variance-of-points` | lemma | Yes | Same label in `ch06_variance.tex`. |
| `eq:local-variance-of-points-equation` | equation | No | The displayed theorem formula is present, but the equation label is dropped. |
| `eq:equivalent-local-variance` | equation | No | Important equivalent squared-form inequality omitted. |
| `lem:global-variance-of-points` | lemma | Yes | Same label in `ch06_variance.tex`. |
| `eq:global-variance-of-points-equation` | equation | No | The displayed theorem formula is present, but the equation label is dropped. |
| `eq:TODO:bound-this!` | equation | No | The proof's target quantity is omitted from the blueprint. |

### 2.2 Exact statements for labels missing from the blueprint

- `sec:variance`

  `Global variance of the points measurements`

- `eq:local-variance-of-points-equation`

```tex
A^u_{g(u)} \otimes (G_g)^{1/2} \approx_{24\cdot(\eps + \delta + \frac{md}{q})} A^v_{g(v)} \otimes (G_g)^{1/2}
```

- `eq:equivalent-local-variance`

```tex
\sum_{g \in \polyfunc{m}{q}{d}}\E_{(\bu, \bv) \sim C} \bra{\psi} (A^{\bu}_{g(\bu)}  - A^{\bv}_{g(\bv)})^2 \otimes G_g \ket{\psi}
\leq 24\left(\eps + \delta + \frac{md}{q}\right).
```

- `eq:global-variance-of-points-equation`

```tex
A^u_{g(u)} \otimes (G_g)^{1/2} \approx_{24m\cdot(\eps + \delta + \frac{md}{q})} A^v_{g(v)} \otimes (G_g)^{1/2}
```

- `eq:TODO:bound-this!`

```tex
\E_{\bu, \bv \sim \F_q^m} \sum_{g \in \polyfunc{m}{q}{d}} \Vert (A^{\bu}_{g(\bu)}  - A^{\bv}_{g(\bv)} ) \otimes (G_g)^{1/2} \ket{\psi}\Vert^2
= \E_{\bu, \bv \sim \F_q^m} \sum_{g \in \polyfunc{m}{q}{d}} \bra{\psi} (A^{\bu}_{g(\bu)}  - A^{\bv}_{g(\bv)} )^2 \otimes G_g \ket{\psi}.
```

### 2.3 Do the blueprint statements match the paper?

#### `lem:generalize-b`

Match: yes. Same statement, same bound `md/q`, same distribution.

Gap:

- The paper gives the full squared-norm expansion with the Schwartz–Zippel step visible.
- The blueprint proof summarizes that argument correctly, but drops the exact operator-sum chain.

#### `lem:local-variance-of-points`

Match: yes. The displayed `\approx` statement is the same.

Gap:

- The paper explicitly records the displayed theorem equation as `eq:local-variance-of-points-equation` and then rewrites it into the squared local-variance inequality `eq:equivalent-local-variance`.
- The blueprint includes the six-step comparison idea in prose, but omits the equivalent squared form that is later used in the proof of global variance.

#### `lem:global-variance-of-points`

Match: yes. The displayed `\approx` statement is the same.

Gap:

- The blueprint proof is much shorter than the paper proof.
- The paper introduces `A(g)^u := A^u_{g(u)}` and `|\psi_g> := I \ot (G_g)^{1/2} |\psi>` and then explicitly rewrites the target bound as a sum of global variances over `g`.
- The blueprint only states that `lem:local-to-global` transports the local bound to the global one.

### 2.4 Lean coverage and proof-structure assessment

#### `MIPStarRE/LDT/GlobalVariance/Defs.lean`

What is present:

- Good abstract definitions for:
  - axis-parallel line questions
  - weighted polynomial state `weightedPolynomialState`
  - weighted point-conditioned operators
  - per-polynomial and averaged local/global variance
  - left/right families for the `generalize-b`, local variance, and global variance comparisons
  - the exact error terms used in the blueprint
- No `sorry` sites in this file.

Where it matches the paper:

- At the abstract operator level, this file does use `CFC.sqrt (G.outcome g)` for `(G_g)^{1/2}`.
- The tensor-product structure is preserved abstractly via `opTensor`, `leftTensor`, and `rightTensor`.

#### `MIPStarRE/LDT/GlobalVariance/MatrixRealization.lean`

What is present:

- A concrete matrix model for the same constructions.
- Matrix statement packages for `generalize-b`, local variance of points, and global variance of points.

Important mismatch with the paper:

- `matrixPolynomialWeightSqrtOperator` is explicitly a placeholder:
  - it uses `G_g` itself, not `(G_g)^{1/2}`
  - see the file comment: "The concrete stand-in for `(G_g)^{1/2}`. The source uses the square root; this placeholder omits it and reuses `G_g` itself."
- The weighted operators are therefore modeled as products in one matrix algebra rather than the paper's literal bipartite tensor expression.

This matters because:

- the abstract interface matches the paper, but the matrix-realization layer that the unfinished theorems depend on is not yet a literal formal counterpart of the paper's operator formulas.

#### `MIPStarRE/LDT/GlobalVariance/Theorems.lean`

Top-level declarations containing `sorry`:

- `matrixGeneralizeB` at line 92
- `matrixLocalVarianceOfPoints` at line 103
- `matrixGlobalVarianceOfPoints` at line 114
- `generalizeB` at lines 132 and 139
- `localVarianceOfPoints` at lines 172, 178, and 186
- `globalVarianceOfPoints` at lines 244 and 251

What is already structurally in place:

- `generalizeB`
  - the averaged bound is fully proved once the pointwise bound is available
  - the missing parts are the pointwise polynomial estimate and the aggregation into `SDDRel`

- `localVarianceOfPoints`
  - the statement package includes both the comparison form and the variance form
  - the averaging shell is fully proved
  - the core six-step argument is not formalized; it is represented by `sorry`

- `globalVarianceOfPoints`
  - this is the strongest partial formalization in the file
  - the proof really does derive the pointwise expansion transfer
  - it uses `localToGlobal` from the expansion chapter on the family `u ↦ A^u_{g(u)}`
  - it fully proves the averaged global variance bound once the pointwise local bound is available
  - the remaining gaps are packaging the comparison into `SDDRel` and proving the direct pointwise norm bound

Dependency risk:

- `globalVarianceOfPoints` depends on `hlocal := localVarianceOfPoints ...`, so its completed-looking middle part still rests on earlier `sorry`s.
- It also depends on `ExpansionHypercubeGraph.localToGlobal`, whose core matrix proof is still a `sorry`.

### 2.5 Nontrivial intermediate equations in the paper

The main omitted proof-level equations here are:

- `eq:equivalent-local-variance`
  - This is the key bridge from the approximate operator statement to the variance expression actually consumed by the expansion lemma.
  - The blueprint currently skips this bridge entirely.

- `eq:TODO:bound-this!`
  - This is the explicit target quantity in the proof of global variance of points.
  - The paper then rewrites it as a sum of `2 * Var_global(A(g), ψ_g)` terms before invoking `lem:local-to-global`.
  - The blueprint proof summary elides this whole chain.

The equation labels `eq:local-variance-of-points-equation` and `eq:global-variance-of-points-equation` are theorem-display labels rather than intermediate steps, but they are still useful anchors if one wants theorem statements and proof-rewrites to reference the same displayed formula.

## 3. Overall gap assessment

### Blueprint vs paper

Coverage is good at the theorem level:

- All major results from these chapters are represented in the blueprint.
- The omitted paper labels are mostly proof-internal.

The main blueprint gap is proof granularity:

- The blueprint suppresses several algebraic equalities that are not optional from a formalization perspective.
- The most important missing bridges are:
  - the eigenvector computation `eq:eigenvector-calculation`
  - the local rewrite bridge `eq:reader-probably-has-no-idea-whats-going-on-yet`
  - the global rewrite trace identity `eq:just-took-trace`
  - the zero-mode elimination `eq:used-0-eigenvector`
  - the local-variance squared-form rewrite `eq:equivalent-local-variance`
  - the global-variance target expression `eq:TODO:bound-this!`

### Lean vs blueprint

Expansion chapter:

- Definitions and spectral infrastructure are fairly advanced.
- The chapter's main Fourier/spectral content is partially formalized in `Defs.lean`.
- The actual chapter theorem wrappers still depend on three matrix-level `sorry`s.

Variance chapter:

- Definitions and statement packaging are present and reasonably faithful.
- The theorem layer is still largely a scaffold.
- `globalVarianceOfPoints` has a meaningful partial proof structure, but it is not closed.

### Priority gaps if the goal is to close Chapters 05-06

1. Finish the matrix realization proofs in `ExpansionHypercubeGraph/Theorems.lean`:
   - `matrixLocalRewrite`
   - `matrixGlobalRewrite`
   - `matrixLocalToGlobal`

2. Strengthen the expansion-side formalization so it matches the paper more literally:
   - derive orthogonality from `fourierBasisState`, rather than defining `fourierBasisInnerProduct` by fiat
   - connect `globalRewrite` to an actual decomposition witness instead of `default`

3. Replace placeholders in `GlobalVariance/MatrixRealization.lean`:
   - use the actual square root `(G_g)^{1/2}`
   - align the concrete weighted operators with the paper's tensor-product formulation

4. Close the theorem-level `sorry`s in `GlobalVariance/Theorems.lean`:
   - pointwise `generalize-b`
   - six-step local variance transfer
   - aggregation into `SDDRel`
   - direct pointwise global deviation bound

5. Consider adding the omitted intermediate proof statements to the blueprint:
   - especially `eq:equivalent-local-variance` and the key expansion-side bridge equations
   - this would make blueprint-to-Lean tracing much easier
