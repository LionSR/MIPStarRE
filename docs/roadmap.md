# Strict roadmap for arXiv:2111.08131

## Source of truth

The canonical theorem DAG for the strict branch is:

- `MIPStarRE/blueprint/src/content.tex`

This roadmap follows the paper's actual proof order and labels. In particular, the primary target is `thm:main` (Theorem 4.1), and the secondary target is `thm:main-bipartite` (Theorem 4.7).

## Guiding principle

Anything reusable should live outside `MIPStarRE/Paper2111/`; only genuinely paper-specific theorems and wrappers should live in `MIPStarRE/Paper2111/`.

The strict branch should follow the paper's own ambient setting:

- von Neumann algebra,
- normal tracial state,
- projective measurements in that algebra.

Finite-dimensional pilot code may still be kept as reference material, but it should not define the strict roadmap.

## Phase order

1. **Section 2.1: tracial operator-algebra setup**
   - `def:tracial-state`
   - `def:tau-norm`
   - `prop:holder`
   - `cor:cauchy-schwarz`

2. **Section 2.2: measurement calculus**
   - `def:submeasurement`
   - `def:processed`
   - `def:consistency`
   - `lem:data-processing`
   - `lem:consistency-consequences`
   - `lem:closeness-to-consistency`
   - `lem:closeness-to-close-ips`
   - `lem:add-a-proj`
   - `lem:transfer-cons`
   - `lem:cons-sub-meas`
   - `lem:switcheroo`

3. **Section 2.3: code and tensor-code layer**
   - `def:code`
   - `prop:distance0`
   - `def:interpolable`
   - `def:axis-line`
   - `def:tensor-code`
   - `prop:distance`
   - `prop:tuple-to-code-correspondence`
   - `prop:interpolate-tuple`

4. **Section 3: tensor-code-test interface**
   - `def:tracial-strat`
   - `def:tracial-good`

5. **Appendix A and spectral bridge**
   - `prop:laplacian-edge-form`
   - `lem:local-to-global-expander`
   - the graph spectral-gap fact used in `lem:variance`

6. **External interfaces**
   - `lem:projectivization`
   - `lem:duality`
   - the `vidick2021almost` input used by `thm:main-bipartite`

7. **Section 5: self-improvement**
   - `lem:local-variance`
   - `lem:variance`
   - `lem:self-improvement-helper`
   - `lem:si-cons`
   - `lem:si-proj`
   - `lem:self-improvement`

8. **Section 6: pasting**
   - commutativity chain (`lem:a-comm`, `lem:g-comm`, `cor:G-hat-facts`, ...)
   - Method 1 intermediate lemmas
   - Method 2 consistency and completeness chain
   - `lem:from-H-to-G`
   - `lem:chernoff-bernoulli-matrix`
   - `lem:pasting`

9. **Section 4: main theorems**
   - `lem:induction`
   - `thm:main`
   - `def:good-2`
   - `thm:main-bipartite`

## Immediate structural goal

Keep a hard boundary between:

- reusable strict infrastructure under `Quantum/`, `Codes/`, `Games/`, and future operator-algebra / combinatorics modules,
- and paper-labelled theorem files under `Paper2111/`.

That internal boundary should stabilize before any future Lake package split is considered.
