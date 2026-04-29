---
title: Lean-QuantumInfo reuse audit for strict 2111
date: 2026-03-08
author: AI research assistant
purpose: >
  Assesses whether Lean-QuantumInfo can support the archived strict
  arXiv:2111.08131 formalization track and records reuse constraints.
status: archived
track: paper2111
kind: external-dependency-audit
---

# Repository snapshot

_Archived 2111 note: this audit was written for the preserved strict-2111 planning track and is kept as an external-dependency reference, not as current Paper2009LDT guidance._

- I inspected `Timeroot/Lean-QuantumInfo` at GitHub HEAD commit `fcd31bcea57e8280aa47f812dc4396af53cb9318` (latest commit dated 2026-03-07 in the cloned snapshot).
- Package metadata:
  - `lean-toolchain`: `leanprover/lean4:v4.24.0`
  - `lakefile.lean`: requires mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
  - top-level libraries: `QuantumInfo`, `ClassicalInfo`, `StatMech`
- Repository scope:
  - `README.md` explicitly says the project is **only about finite-dimensional Hilbert spaces**.
  - The main quantum code lives in `QuantumInfo/Finite/`.
  - `QuantumInfo/InfiniteDim/` contains only `QState.lean`, and that file is currently just a commented-out sketch rather than live infrastructure.
- The parts most relevant to the present question are:
  - `QuantumInfo/Finite/MState.lean`: density matrices (`MState`), expectation values, tensor products, partial trace.
  - `QuantumInfo/Finite/POVM.lean`: bundled POVMs `POVM X d`, outcome distributions, and induced CPTP maps.
  - `QuantumInfo/Finite/CPTPMap/Dual.lean`: finite-dimensional dual / Heisenberg-picture lemmas for positive trace-preserving maps.
  - `QuantumInfo/ForMathlib/HermitianMat/*.lean`: a substantial helper layer for `HermitianMat`, including `Trace`, `Inner`, `Proj`, `Sqrt`, `CFC`, `Rpow`, and `Order`.
- The repository's current mathematical center of gravity is entropy/channels/resource theory/Stein's lemma, not nonlocal games or operator-algebraic rigidity.
- The inspected snapshot is not fully finished: over `QuantumInfo`, `ClassicalInfo`, and `StatMech`, I found `78` occurrences of `sorry` and `5` `proof_wanted` markers.

# Potential direct reuse for 2111.08131

For the **strict** 2111 project, direct reuse is very limited.

The only pieces that look plausibly useful are low-level finite-dimensional lemmas, not the package's high-level architecture:

- `QuantumInfo/ForMathlib/HermitianMat/Trace.lean`
  - ordinary trace on `HermitianMat`
  - `traceLeft`, `traceRight`
  - `trace_kronecker`
- `QuantumInfo/ForMathlib/HermitianMat/Inner.lean`
  - Hilbert-Schmidt-style inner product facts such as
    `inner_eq_trace_rc`, `inner_ge_zero`, `inner_mono`, `inner_le_mul_trace`
- `QuantumInfo/ForMathlib/HermitianMat/Proj.lean`
  - projector/support/positive-part lemmas that could be relevant to a **finite-dimensional** orthogonalization layer
- `QuantumInfo/Finite/POVM.lean`
  - a bundled definition of a complete finite POVM and the associated measurement channel/distribution

These are best viewed as **selective port/cherry-pick candidates** for a finite-dimensional auxiliary layer.
They are not a direct implementation of the Section 2 interface needed by arXiv:2111.08131.

Compared with the current local `MIPStarRE` files, `Lean-QuantumInfo` is actually *less aligned* with the strict 2111 interface:

- `MIPStarRE/Quantum/OutcomeFamily.lean` already has the paper-relevant answer-relabeling/data-processing shape:
  - `OutcomeFamily.postprocess`
  - `OutcomeFamily.postprocess_total`
  - `offDiagSumRelabel_le`
- `MIPStarRE/Quantum/FiniteMatrix.lean` already uses the paper-style normalized trace with `τ(1)=1`:
  - `normalizedTrace`
  - `tauNormSq`
  - `IsProj`
- `MIPStarRE/Quantum/Measurement.lean` already has the paper-relevant measurement bookkeeping:
  - `Submeasurement`
  - `Measurement`
  - `postprocess`
  - `inconsistency`
  - `diagOverlap`
  - `Measurement.inconsistency_add_diagOverlap_eq_one`

So even where `Lean-QuantumInfo` has useful mathematics, it is not obviously a better direct base than the local thin layer already being built.

# Mismatches and blockers

- **Fundamental ambient mismatch.**
  - The archived strict 2111 blueprint in `MIPStarRE/blueprint/legacy/content_2111_strict_20260320.tex` targets a von Neumann algebra with a normal tracial state and explicitly says this is **not** to be replaced by a finite-dimensional matrix pilot.
  - `Lean-QuantumInfo` explicitly restricts itself to finite-dimensional Hilbert spaces.
  - Its `QuantumInfo/InfiniteDim/QState.lean` file is essentially dead code, so there is no live infrastructure there for von Neumann algebras, normal states, trace-class operators, or normal positive maps.

- **State-centric interface instead of tracial-algebra interface.**
  - `Lean-QuantumInfo` is organized around `MState` (trace-1 density matrices) and expectation values against an arbitrary state.
  - 2111 is organized around operator families inside a single algebra and a fixed tracial functional `τ`.
  - Even in finite dimension, the paper wants the normalized trace viewpoint (`τ(1)=1`), whereas `Lean-QuantumInfo` is built around ordinary trace-1 states.
  - Reusing `MState`/`POVM` would therefore rephrase the paper in a different interface rather than following it closely.

- **Missing Section 2 structures.**
  `Lean-QuantumInfo` does not provide the central paper-specific objects already visible in the local `MIPStarRE` design:
  - no bundled `Submeasurement`
  - no question-indexed measurement families
  - no generic processed-measurement / fiber-sum API analogous to `OutcomeFamily.postprocess`
  - no paper-style consistency / closeness / off-diagonal bookkeeping layer
  - no local test interface for tensor-code strategies

- **Even the finite-dimensional measurement layer is too thin.**
  `QuantumInfo/Finite/POVM.lean` gives a complete POVM, but the file itself says commutation/projectivity development is still TODO. That is not enough for the 2111 Section 2 calculus.

- **Wrong high-level focus.**
  I found no tensor-code, expander, synchronous-strategy, subcube-test, or 2111-specific infrastructure. The repository is mainly about entropy, channels, resource theory, and generalized quantum Stein's lemma.

- **Representation mismatch with the local project.**
  - `Lean-QuantumInfo` heavily uses bundled `HermitianMat` and `MState`.
  - The current local `MIPStarRE` layer deliberately uses plain `Matrix d d ℂ` plus explicit positivity/normalization assumptions.
  - The strict 2111 project ultimately wants an abstract operator-algebra interface anyway, so porting into the `MState` worldview would be a detour.

- **Unfinished relevant files.**
  Even among nearby modules there are placeholders, e.g.
  - `QuantumInfo/Finite/POVM.lean`: `measureForget_eq_kraus`
  - `QuantumInfo/Finite/MState.lean`: `pure_inner`
  - `QuantumInfo/Finite/CPTPMap/Dual.lean`: two `sorry`s
  - `QuantumInfo/ForMathlib/HermitianMat/Proj.lean`: two `proof_wanted`s

# Dependency and version compatibility

- Local `MIPStarRE`:
  - `lean-toolchain`: `leanprover/lean4:v4.28.0`
  - `lakefile.toml`: `mathlib` `v4.28.0`
  - no extra direct dependency beyond mathlib
- `Lean-QuantumInfo` snapshot:
  - `lean-toolchain`: `leanprover/lean4:v4.24.0`
  - `lakefile.lean`: mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

So `Lean-QuantumInfo` is **not a drop-in dependency** for the current `MIPStarRE` package.

A few compatibility details:

- The direct declared dependency surface is fairly light: essentially mathlib.
- The committed `lake-manifest.json` also still records `doc-gen4` and mathlib's transitive tooling, but the main compatibility issue is not extra packages; it is the Lean/mathlib revision gap and the heavy custom API surface.
- Because four Lean/mathlib minor versions separate the projects, direct import would require a port.
- Because the repository has a large custom `HermitianMat` helper layer, that port is not just syntax churn; it would also import a mathematical interface that does not line up with the local `OutcomeFamily` / `Submeasurement` / normalized-trace design.

Conclusion: **selective manual porting of isolated low-level lemmas is plausible; direct package reuse is not.**

# Recommendation for package structure

For a **strict proof-following** formalization of 2111.08131:

- Keep the paper-specific development separate from reusable foundations.
- But the reusable foundation should be **local and 2111-aligned**, not `Lean-QuantumInfo`-shaped.

Concretely, the current `MIPStarRE` split already points in the right direction:

- reusable layer:
  - `MIPStarRE/Quantum/`
  - `MIPStarRE/Codes/`
  - `MIPStarRE/Games/`
- paper-specific layer:
  - `MIPStarRE/Paper2111/`

If this is ever split into multiple Lake packages, the reusable package should expose:

- the operator/tracial interfaces that survive the move to the von Neumann-algebra setting,
- the paper-specific measurement bookkeeping from Section 2,
- and only secondarily a finite-dimensional specialization layer.

`Lean-QuantumInfo` should **not** serve as that foundation package for strict 2111:

- it is too finite-dimensional,
- too state/channel oriented,
- too far behind in Lean/mathlib version,
- and too misaligned with the actual theorem DAG of the paper.

The only sensible reuse path is selective:

- port a few low-level finite-dimensional `HermitianMat` lemmas if they materially shorten the local finite matrix layer;
- keep them behind a local finite-dimensional module;
- do **not** make the strict 2111 formalization depend on the whole `Lean-QuantumInfo` repository or on its `MState`/`POVM` interface.

Bottom line: for the strict 2111 project, `Lean-QuantumInfo` is a source of possible finite-dimensional helper lemmas, **not** a viable base dependency or reusable foundation package.
