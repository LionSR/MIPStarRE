# Strict proof-following effort estimate for arXiv:2111.08131

_Date: 2026-03-08._

This note is an evidence-based estimate for a **strict proof-following Lean formalization of arXiv:2111.08131 only**.

## Assessment basis

I based this report on the current repository state at `MIPStarRE/` (HEAD `9901ceb`), and I read the files requested in the task:

- `MIPStarRE/README.md`
- `MIPStarRE/docs/roadmap.md`
- `MIPStarRE/docs/mathlib_api_2111.md`
- `MIPStarRE/blueprint/src/content.tex`
- `MIPStarRE/MIPStarRE/Quantum/OutcomeFamily.lean`
- `MIPStarRE/MIPStarRE/Quantum/FiniteMatrix.lean`
- `MIPStarRE/MIPStarRE/Quantum/Measurement.lean`
- `MIPStarRE/MIPStarRE/Codes/LinearCode.lean`
- `MIPStarRE/MIPStarRE/Games/TensorCodeTest.lean`
- `MIPStarRE/MIPStarRE/Paper2111/Skeleton.lean`
- `2111.08131/section2-preliminaries.tex`
- `2111.08131/section3-tensor-code-test.tex`
- `2111.08131/section4-quantum-soundness-analysis.tex`
- `2111.08131/section5-self-improvement.tex`
- `2111.08131/section6-pasting.tex`
- `2111.08131/appendix-expander-graphs.tex`

I also inspected:

- `MIPStarRE/lakefile.toml`
- `MIPStarRE/MIPStarRE.lean`
- Mathlib support around `Mathlib.Analysis.VonNeumannAlgebra.Basic`, `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap`, `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`, and `Mathlib.Algebra.Star.StarProjection`

and confirmed that `cd MIPStarRE && lake build` currently succeeds, with only linter warnings concentrated in `Quantum/FiniteMatrix.lean`.

---

## Executive summary

1. **The strict target is much larger than the current scaffold suggests.** The canonical strict target is the theorem DAG in `blueprint/src/content.tex`, centered on `thm:main` and secondarily `thm:main-bipartite`. The current Lean scaffold still mostly reflects a finite-dimensional pilot.
2. **The main underestimated cost is not coding theory; it is the ambient operator-algebra/tracial layer and the Section 5–6 theorem chain.** The decisive blockers are the von Neumann / normal tracial setting, `lem:duality`, `lem:projectivization`, and the Method 2 completeness chain ending in `lem:from-H-to-G`, `lem:chernoff-bernoulli-matrix`, and `lem:pasting`.
3. **My central estimate for a strict 2111 formalization, assuming the external results are imported as trusted theorems with precise Lean interfaces, is about `81 person-weeks`.** An optimistic / central / pessimistic band is:
   - **54 / 81 / 124 person-weeks** for the paper itself with imported external dependencies.
4. **If the project insists on a closed-world development that also formalizes the external inputs from `de2021orthogonalization` and `vidick2021almost`, the central estimate rises to about `120 person-weeks`.** Band:
   - **78 / 120 / 190 person-weeks**.
5. **Recommendation on packaging:** do **not** split arXiv:2111.08131 into its own Lake package yet. Keep it inside `MIPStarRE` as a paper-specific namespace, but enforce a hard boundary between:
   - reusable strict infrastructure, and
   - `MIPStarRE.Paper2111` theorem files carrying the paper labels.
   If a package split is later desired, the exact cut should be at that boundary.
6. **Current code is still useful, but only saves single-digit person-weeks.** The strongest reusable pieces are `Quantum/OutcomeFamily.lean`, `Codes/LinearCode.lean`, and the geometry in `Games/TensorCodeTest.lean`. The matrix-specific operator files are not on the strict critical path.

---

## 1. The strict target, stated accurately

For this project the primary target is:

- `thm:main` = Theorem 4.1, the synchronous / tracial soundness theorem.

The secondary target is:

- `thm:main-bipartite` = Theorem 4.7, the two-prover extension via `vidick2021almost`.

The strict ambient setting is the paper’s own one:

- a von Neumann algebra on a Hilbert space,
- a **normal tracial state**,
- projective measurements valued in that algebra,
- and a proof order which is logically:
  - Section 2 definitions and utilities,
  - Section 3 test definitions,
  - Appendix A,
  - Section 5 (`lem:self-improvement`),
  - Section 6 (`lem:pasting`),
  - then Section 4 (`lem:induction`, `thm:main`, `thm:main-bipartite`).

That is exactly the order reflected by `MIPStarRE/blueprint/src/content.tex`, and it is the right backbone for the Lean plan.

---

## 2. Section-by-section dependency and workload estimate

### 2.1 Major blocks

All estimates below are in **person-weeks for one experienced Lean/mathlib formalizer**, assuming repo-local development rather than upstreaming delays.

| Block | Exact paper anchors | Main dependencies | Type | Current status | O / C / P |
|---|---|---|---|---|---:|
| Section 2.1: tracial setup and trace inequalities | `def:tracial-state`, `def:tau-norm`, `prop:holder`, `cor:cauchy-schwarz` | ambient von Neumann algebra model, positive functional API, absolute value / square root / polar decomposition access | reusable local library | not started in the strict setting; current `FiniteMatrix.lean` is only a pilot analogue | 6 / 9 / 14 |
| Section 2.2: measurements, consistency, closeness | `def:submeasurement`, `def:processed`, `def:consistency`, `lem:data-processing`, `lem:consistency-consequences`, `lem:closeness-to-consistency`, `lem:closeness-to-close-ips`, `lem:add-a-proj`, `lem:transfer-cons`, `lem:cons-sub-meas`, `lem:switcheroo` | Section 2.1, abstract measurement API, finite averaging over questions | reusable local library | partially scaffolded only at the combinatorial / matrix-bookkeeping level | 5 / 8 / 12 |
| Section 2.3: codes and tensor codes | `def:code`, `prop:distance0`, `def:interpolable`, `def:axis-line`, `def:tensor-code`, `prop:distance`, `prop:tuple-to-code-correspondence`, `prop:interpolate-tuple` | Hamming distance, line restriction maps, interpolation maps | reusable local library | `prop:distance0` and interpolability partly reusable; tensor code layer itself missing | 3 / 5 / 8 |
| Section 3: tensor code test interface | `def:tracial-strat`, `def:tracial-good` | Section 2 measurement and coding APIs | mostly paper-specific, but built on reusable question geometry | question geometry exists; actual strategy and goodness definitions missing | 1 / 2 / 4 |
| Appendix A plus hidden spectral-gap lemma | `prop:laplacian-edge-form`, `lem:local-to-global-expander`, plus the unlabeled `\lambda_2 = 1/(mn^m)` fact used in Section 5 | weighted-kernel / Laplacian API, spectral facts for the graph on `[n]^m` | reusable local library plus one paper-specific instantiation | missing | 4 / 6 / 10 |
| External Section 5 ingredients: interfaces only | `lem:projectivization`, `lem:duality` | precise Lean signatures for imported theorems | external dependency integration | missing | 1 / 2 / 4 |
| Section 5 internal chain | `lem:local-variance`, `lem:variance`, `lem:self-improvement-helper`, unlabeled completeness lemma `\sum_g \tau(H_g) \ge 1-\nu`, `lem:si-cons`, `lem:si-proj`, `lem:self-improvement` | Sections 2–3, Appendix A, `lem:projectivization`, `lem:duality` | paper-specific theorem work | missing | 7 / 11 / 16 |
| Section 6 commutativity chain | `lem:a-comm`, `lem:g-comm-after-eval`, `lem:g-comm`, `lem:commutativity-switcheroo`, `cor:g-comm`, `cor:G-hat-facts` | Section 2 utilities, Section 3 good-strategy layer, slice-measurement hypotheses from `lem:pasting` | paper-specific theorem work | missing | 6 / 8 / 12 |
| Section 6 Method 1 | `prop:ld-dnoteq`, `lem:pasting-h-cons-b`, `lem:pasting-h-cons-a`, `lem:pasting-h-close-hg`, `lem:nu-6`, unlabeled completeness lemma `\tau(H) \ge \tau(G)-\nu_7` | commutativity chain, tensor-code interpolation, Section 2 utilities | paper-specific theorem work | missing | 5 / 7 / 10 |
| Section 6 Method 2 and final pasting | `def:G-hat`, `def:types`, `def:pasted-meas`, `lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`, `cor:ha-cons`, `lem:over-all-outcomes`, `lem:from-H-to-G`, `lem:chernoff-bernoulli-matrix`, `cor:ld-pasting-N-completeness`, `lem:pasting` | commutativity chain, interpolation, functional calculus, scalar Chernoff input | paper-specific theorem work | missing | 10 / 15 / 23 |
| Section 4 main induction | `lem:induction`, `thm:main` | `lem:self-improvement`, `lem:pasting` | paper-specific theorem work | missing | 3 / 4 / 6 |
| Section 4.1 bipartite extension | `def:good-2`, `thm:main-bipartite` | `thm:main`, `lem:projectivization`, `prop:distance`, two-prover finite-dimensional Hilbert-space layer, `vidick2021almost` | paper-specific theorem work with external dependency | missing | 3 / 4 / 7 |

### 2.2 Critical-path DAG

The shortest strict path to `thm:main` is:

1. Section 2 core utilities, especially `cor:cauchy-schwarz`, `lem:closeness-to-close-ips`, `lem:transfer-cons`, `lem:cons-sub-meas`, `lem:switcheroo`, and the tensor-code lemmas.
2. Appendix A: `lem:local-to-global-expander`, plus the unlabeled spectral-gap fact for the graph on `[n]^m`.
3. Section 5:
   - `lem:projectivization`
   - `lem:duality`
   - `lem:local-variance`
   - `lem:variance`
   - `lem:self-improvement-helper`
   - `lem:si-cons`
   - `lem:si-proj`
   - `lem:self-improvement`
4. Section 6 commutativity chain:
   - `lem:a-comm`
   - `lem:g-comm-after-eval`
   - `lem:g-comm`
   - `lem:commutativity-switcheroo`
   - `cor:G-hat-facts`
5. Section 6 Method 2:
   - `lem:ld-sandwich-line-one-point`
   - `lem:h-b-consistency`
   - `cor:ha-cons`
   - `lem:over-all-outcomes`
   - `lem:from-H-to-G`
   - `lem:chernoff-bernoulli-matrix`
   - `cor:ld-pasting-N-completeness`
   - `lem:pasting`
6. Section 4:
   - `lem:induction`
   - `thm:main`

For full strict paper coverage, not only the shortest path, add:

- Section 6 Method 1 (`prop:ld-dnoteq`, `lem:pasting-h-cons-b`, `lem:pasting-h-cons-a`, `lem:pasting-h-close-hg`, `lem:nu-6`),
- Section 4.1 (`thm:main-bipartite`).

Important nuance: **Method 1 is not on the shortest path to the final proof of `lem:pasting`**, because the paper’s final Section 6 completion argument uses Method 2 after the commutativity chain. But Method 1 is still part of a strict proof-following formalization of the paper as written, so it cannot be dropped from a paper-complete estimate.

---

## 3. Comparison with the current codebase

### 3.1 File-by-file assessment

| File | Verdict for strict 2111 | Notes |
|---|---|---|
| `README.md` | misaligned | It explicitly says the first milestone is a **finite-dimensional pilot formalization**. That is not the strict target. |
| `docs/roadmap.md` | misaligned | Same issue: “Build a finite-dimensional measurement API” is the wrong top-level goal for the strict branch. |
| `docs/mathlib_api_2111.md` | partially reusable | Useful for coding-theory, `hammingDist`, and weighted-kernel / expander ideas; misaligned for the operator-algebra core because it assumes finite matrices throughout. |
| `blueprint/src/content.tex` | canonical strict guide | This is the right theorem DAG and phase ordering for the strict project. |
| `Quantum/OutcomeFamily.lean` | genuinely reusable | Best current reusable component. It is already operator-agnostic and captures postprocessing / fiberwise bookkeeping needed for `lem:data-processing`. |
| `Quantum/FiniteMatrix.lean` | mostly misaligned | Good pilot sandbox, but the strict project should not depend on matrix-only normalized trace or a local `IsProj` predicate. In the strict branch this should be treated as legacy or experimental. |
| `Quantum/Measurement.lean` | design ideas reusable, implementation not | The file proves matrix-valued postprocessing and overlap identities. The strict project needs the same shape of API but over an abstract von Neumann / tracial setting. |
| `Codes/LinearCode.lean` | strongly reusable | `LinearCode`, `Interpolable`, and `eq_of_agree_on_large_set` are directly on the strict path to `prop:distance0` and `def:interpolable`. |
| `Games/TensorCodeTest.lean` | partially reusable | Grid geometry and axis-parallel lines are reusable. The semantic layer for `def:tracial-strat` and `def:tracial-good` is still missing. |
| `Paper2111/Skeleton.lean` | misaligned / obsolete as a driver | It still reflects the pilot. The `FutureResult` names even mismatch the actual paper numbering (`section4SelfImprovement`, `section5Pasting`, `section6Soundness`), whereas the paper has Section 4 main induction, Section 5 self-improvement, Section 6 pasting. |

### 3.2 What is reusable now

**Directly reusable or close to directly reusable**

- `MIPStarRE.Quantum.OutcomeFamily.postprocess`
- `MIPStarRE.Quantum.OutcomeFamily.postprocess_total`
- `MIPStarRE.Quantum.offDiagSumRelabel_le`
- `MIPStarRE.Codes.LinearCode`
- `MIPStarRE.Codes.LinearCode.eq_of_agree_on_large_set` as the Lean core of `prop:distance0`
- `MIPStarRE.Codes.LinearCode.Interpolable`
- `MIPStarRE.Codes.LinearCode.Interpolable.interpolate_unique`
- `MIPStarRE.Games.AxisParallelLine` / grid bookkeeping

These are real assets for the strict project.

**Conceptually useful but needing a rewrite**

- `Quantum/Measurement.lean`: keep the API shape, but rewrite over an abstract operator algebra rather than `Matrix d d ℂ`.
- `Quantum/FiniteMatrix.lean`: some lemmas indicate what the strict abstract layer should provide, but the actual code is not on the strict import spine.

**Not reusable as strict core**

- pilot-facing README/roadmap
- `Paper2111/Skeleton.lean` as a roadmap authority
- matrix-only theorem names as if they were paper theorems

### 3.3 Major missing abstractions

The strict project still lacks the following major abstractions.

1. **Ambient operator-algebra layer**
   - a concrete Lean representation of the paper’s von Neumann algebra setting,
   - a `NormalTracialState`-like structure,
   - a paper-level `\tau`-norm and 1-norm layer,
   - abstract use of `IsStarProjection` rather than local matrix-only `IsProj`.

2. **Abstract measurement calculus**
   - question-indexed submeasurements and measurements in the strict ambient setting,
   - consistency / closeness on average over finite question distributions,
   - the full Section 2 utility lemma suite.

3. **Tensor-code layer**
   - actual `def:tensor-code`,
   - `prop:distance`,
   - `prop:tuple-to-code-correspondence`,
   - `prop:interpolate-tuple`.

4. **Strategy layer**
   - `def:tracial-strat`,
   - `def:tracial-good`,
   - Section 4.1 two-prover definitions.

5. **Appendix / spectral layer**
   - weighted expander kernel,
   - `prop:laplacian-edge-form`,
   - `lem:local-to-global-expander`,
   - the graph-on-`[n]^m` spectral-gap fact used by `lem:variance`.

6. **External dependency interfaces**
   - imported theorem interfaces for `lem:projectivization`, `lem:duality`, and the `vidick2021almost` corollary used by `thm:main-bipartite`.

The present scaffold is therefore best viewed as a useful **front-end shell**, not yet as the strict core itself.

---

## 4. Effort estimate with uncertainty bands

### 4.1 Category totals

| Category | O / C / P | Notes |
|---|---:|---|
| Reusable local library work | 19 / 30 / 46 | Sections 2.1–2.3, Section 3 interface, Appendix A, hidden spectral-gap lemma |
| Paper-specific theorem work (internal to 2111) | 34 / 49 / 74 | Section 5 internal chain, Section 6 commutativity + Methods 1 and 2, Section 4 main loop, Section 4.1 wrapper work |
| External dependency interfaces only | 1 / 2 / 4 | Precise imported statements for `lem:projectivization`, `lem:duality`, and `vidick2021almost` |
| **Strict 2111 total, assuming external theorems are imported** | **54 / 81 / 124** | Best estimate for the paper itself |
| Add-on if `de2021orthogonalization` is also formalized in-house | 16 / 25 / 40 | covers the mathematics behind `lem:projectivization` and `lem:duality` |
| Add-on if the `vidick2021almost` input is also formalized in-house | 8 / 14 / 25 | covers the Section 4.1 external reduction rather than merely importing it |
| **Closed-world total including both external papers** | **78 / 120 / 190** | Very likely a multi-person, multi-quarter project |

### 4.2 How much the existing scaffold actually saves

My best estimate is that the current codebase saves **single-digit person-weeks**, not more:

- roughly **4–8 person-weeks** total,
- mostly in code / interpolation / geometry bookkeeping,
- almost **none** on the strict critical path through the von Neumann / tracial Section 2 setup, `lem:self-improvement`, or the Method 2 completeness chain.

That means the scaffold is valuable, but it does **not** change the order of magnitude of the strict project.

### 4.3 Why the old high-level estimate was too low

The underestimated items are mainly:

- the gap between a matrix pilot and the strict ambient setting,
- the real cost of `lem:duality` and `lem:projectivization`,
- the unlabeled but nontrivial auxiliary lemmas inside Sections 5 and 6,
- the Method 2 completeness machinery around `lem:from-H-to-G`,
- the fact that Section 4.1 is a second ambient world (finite-dimensional bipartite strategies) layered on top of the tracial proof.

---

## 5. Main blockers and risk drivers

### 5.1 The von Neumann / tracial setting is the main blocker

Mathlib now has some useful ingredients:

- `Mathlib.Analysis.VonNeumannAlgebra.Basic` provides `WStarAlgebra` and `VonNeumannAlgebra`,
- `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap` provides positive linear maps on C\*-algebras,
- `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` provides a GNS construction for positive linear functionals,
- `Mathlib.Algebra.Star.StarProjection` provides abstract `IsStarProjection`.

But this is still far from the full paper interface.

Concretely, I found:

- only a **very small** `Analysis/VonNeumannAlgebra` subtree in the local mathlib checkout,
- no developed local layer for **normal tracial states** in the paper’s sense,
- no developed local layer for **trace-class operators** or a built-in normality API matching the paper,
- no off-the-shelf Section 2 measurement calculus.

So the strict branch should not assume that “mathlib already has the von Neumann layer.” It does not.

### 5.2 `de2021orthogonalization` is a real blocker, not a small lemma import

The paper uses `de2021orthogonalization` for both:

- `lem:projectivization`, and
- `lem:duality`.

These are not cosmetic inputs. They sit at the entry to Section 5, and Section 5 is on the critical path to `thm:main`.

Moreover, the two imported ingredients are of very different flavors:

- `lem:projectivization` is an orthogonalization / polar-decomposition theorem for POVMs in the von Neumann setting,
- `lem:duality` is a Hahn–Banach / positive-map domination theorem.

If these are not imported as trusted theorems, the project becomes much closer to an operator-algebra formalization program than to a paper-local formalization.

### 5.3 `vidick2021almost` is a second external blocker

`thm:main-bipartite` is not just a small corollary. Its proof explicitly imports the almost-synchronous-to-synchronous reduction from `vidick2021almost`, and then adds finite-dimensional symmetric-strategy and projectivization work around it.

So even after `thm:main`, the project still needs a separate proof world for:

- Schmidt decompositions,
- reduced states `\rho_A`, `\rho_B`,
- transposes and symmetrization,
- and the imported almost-synchronous reduction.

### 5.4 Section 6 Method 2 is the single largest internal theorem block

The hardest internal block is not `lem:induction`; it is the Method 2 chain in Section 6:

- `lem:commutativity-switcheroo`
- `cor:G-hat-facts`
- `lem:ld-sandwich-line-one-point`
- `lem:h-b-consistency`
- `lem:over-all-outcomes`
- `lem:from-H-to-G`
- `lem:chernoff-bernoulli-matrix`
- `cor:ld-pasting-N-completeness`
- `lem:pasting`

This part contains a lot of unlabeled internal machinery (`Outcomes_τ`, `Global_τ`, `Consistent_τ`, `S_{τ_{\ge \ell}}`) that still has to be named and formalized in Lean.

### 5.5 Hidden work items the paper does not label cleanly

A strict formalization must also supply unnamed intermediate results, for example:

- the unlabeled completeness lemma in Section 5 (`\sum_g \tau(H_g) \ge 1-\nu`),
- the unlabeled Method 1 completeness lemma (`\tau(H) \ge \tau(G)-\nu_7`),
- the spectral-gap fact for the graph on `[n]^m`, used in the proof of `lem:variance`,
- the internal recurrence lemmas around `S_{τ_{\ge \ell}}` in `lem:from-H-to-G`.

These are real work, and they should be budgeted explicitly.

### 5.6 No obvious ready-made Chernoff theorem showed up in the local mathlib search

I did not find a ready-made named Chernoff result in the local mathlib search that matches the scalar step used inside `lem:chernoff-bernoulli-matrix`. So the realistic plan is:

- prove the scalar additive bound locally, or
- prove exactly the needed Bernoulli-tail inequality locally,
- then lift it through functional calculus.

That is another reason Section 6 Method 2 should not be budgeted lightly.

---

## 6. Recommended code-organization plan

### 6.1 Package decision

**Recommendation: keep arXiv:2111.08131 inside the existing `MIPStarRE` package, as a paper-specific namespace, not as its own Lake package.**

### Why I do not recommend a package split now

1. The reusable strict infrastructure is still immature. Splitting too early would create churn before the real core API has stabilized.
2. The main cost is theorem engineering and missing abstractions, not package mechanics.
3. The future MIP*=RE* work should reuse the same strict operator / measurement / code infrastructure, so keeping everything under one package is the more natural growth path.
4. A package split would not remove the real trust-boundary question about `de2021orthogonalization` and `vidick2021almost`; that question can be handled just as well inside one package by isolating external imports in dedicated modules.

### Exact boundary I recommend instead

Inside one package, enforce this hard rule:

- **Reusable strict library work** goes under reusable directories and must **never import** `MIPStarRE.Paper2111.*`.
- **Paper-labelled theorem files** go under `MIPStarRE.Paper2111.*` and may import the reusable layer.
- Only `MIPStarRE.Paper2111.*` should carry paper-specific label names such as `thm:main`, `lem:self-improvement`, `lem:pasting`, `lem:from-H-to-G`, `cor:cauchy-schwarz`, etc.

If a package split is later wanted, the exact cut should be:

- **core package:** reusable strict infrastructure,
- **paper package:** `Paper2111` wrappers, section files, and external imported theorems.

That is the right boundary. Splitting earlier than that is not.

### 6.2 Recommended module tree

A concrete module tree for the strict project could look like this.

```text
MIPStarRE/MIPStarRE/
  OperatorAlgebra/
    VonNeumann/
      Basic.lean
      TracialState.lean
      PositiveMaps.lean
      TauNorm.lean
      Projections.lean
      FunctionalCalculus.lean

  Quantum/
    OutcomeFamily.lean                      -- keep and reuse
    Measurement/
      Basic.lean
      Process.lean
      Consistency.lean
      Closeness.lean
      Utility.lean

  Codes/
    LinearCode.lean                         -- keep and extend
    TensorCode.lean
    TupleInterpolation.lean

  Combinatorics/
    DistinctTuples.lean                     -- for prop:ld-dnoteq
    ExpanderKernel.lean
    OperatorPoincare.lean                   -- generic form of lem:local-to-global-expander
    GridGraphSpectrum.lean                  -- paper-specific λ₂ fact for [n]^m graph

  Games/
    TensorCodeTest/
      Geometry.lean                         -- axis-parallel lines, subcubes, question geometry
      TracialStrategy.lean                  -- def:tracial-strat
      GoodStrategy.lean                     -- def:tracial-good
      BipartiteStrategy.lean                -- def:good-2 and Section 4.1 setup

  Paper2111/
    Section2/
      Preliminaries.lean                    -- paper-labelled façade over reusable Section 2 results
    Section3/
      Test.lean
    Appendix/
      Expander.lean
    External/
      DeOliveiraScholz.lean                 -- lem:projectivization, lem:duality interfaces
      VidickAlmost.lean                     -- thm:main-bipartite external input
    Section5/
      Variance.lean                         -- lem:local-variance, lem:variance
      SelfImprovement.lean                  -- helper lemmas, lem:si-cons, lem:si-proj, lem:self-improvement
    Section6/
      Commutativity.lean                    -- lem:a-comm, lem:g-comm-after-eval, lem:g-comm, cor:g-comm, cor:G-hat-facts
      Method1.lean                          -- prop:ld-dnoteq, lem:pasting-h-cons-b, lem:pasting-h-cons-a, lem:pasting-h-close-hg, lem:nu-6
      Method2Defs.lean                      -- def:G-hat, def:types, def:pasted-meas
      Method2Consistency.lean               -- lem:ld-sandwich-line-one-point, lem:h-b-consistency, cor:ha-cons
      Method2Completeness.lean              -- lem:over-all-outcomes, lem:from-H-to-G, lem:chernoff-bernoulli-matrix, cor:ld-pasting-N-completeness
      Pasting.lean                          -- lem:pasting
    Section4/
      Induction.lean                        -- lem:induction
      Main.lean                             -- thm:main
      Bipartite.lean                        -- thm:main-bipartite

  Legacy/
    FinitePilot/
      Quantum/FiniteMatrix.lean
      Quantum/Measurement.lean
      Paper2111/Skeleton.lean
```

### 6.3 Why this tree is better than growing the current files in place

1. It isolates the **strict ambient operator-algebra layer** from the current finite-dimensional pilot code.
2. It preserves the genuinely reusable combinatorics (`OutcomeFamily`, codes, geometry).
3. It gives a **paper-labelled façade** under `Paper2111/` so the formal proof graph can track the actual labels `thm:main`, `lem:self-improvement`, `lem:pasting`, `lem:duality`, `lem:projectivization`, `lem:from-H-to-G`, `cor:cauchy-schwarz`, etc.
4. It isolates Section 4.1 into its own subworld, which is important because it mixes finite-dimensional bipartite Hilbert-space reasoning with the main tracial proof.
5. It keeps the current pilot code available as reference material without letting it contaminate the strict import spine.

---

## 7. Recommended first strict milestones

If the team starts now and wants to minimize rework, the first milestones should be:

1. **Choose the strict ambient Lean model** for the main theorem chain.
   - I recommend a concrete von Neumann algebra model rather than an abstract `WStarAlgebra`, because mathlib’s equivalence story is still thin.
   - Define a thin local `NormalTracialState` interface tailored to the paper.

2. **Rebuild the measurement layer abstractly.**
   - Keep `OutcomeFamily.lean`.
   - Replace the matrix-only `Quantum/Measurement.lean` by a strict reusable measurement API over the chosen ambient algebra.

3. **Finish the missing tensor-code layer.**
   - `def:tensor-code`
   - `prop:distance`
   - `prop:tuple-to-code-correspondence`
   - `prop:interpolate-tuple`

4. **Formalize the actual Section 3 strategy layer.**
   - `def:tracial-strat`
   - `def:tracial-good`

5. **Formalize Appendix A and the spectral-gap bridge to Section 5.**
   - `lem:local-to-global-expander`
   - the `[n]^m` graph eigenvalue lemma used inside `lem:variance`

6. **Introduce precise external dependency interfaces early.**
   - `lem:projectivization`
   - `lem:duality`
   - `vidick2021almost` interface for `thm:main-bipartite`

Only after these six are in place would I start budgeting Section 5 and Section 6 theorem implementation sprints.

---

## 8. Bottom-line recommendation

- Use `blueprint/src/content.tex` and the actual paper sections as the source of truth.
- Treat the current matrix pilot as **legacy scaffolding**, not as the core strict branch.
- Keep `2111.08131` inside `MIPStarRE`, but enforce a strong internal boundary between reusable strict library code and `Paper2111` theorem files.
- Budget the strict paper itself at roughly **54 / 81 / 124 person-weeks**.
- Budget a closed-world version including `de2021orthogonalization` and `vidick2021almost` at roughly **78 / 120 / 190 person-weeks**.

That is the sober estimate I would plan against.