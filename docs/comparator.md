# Comparator verification of `mainFormal`

The headline theorem `MIPStarRE.LDT.Test.mainFormal` (the corrected source
statement of `thm:main-formal` from the low individual degree test paper) is
independently verifiable with the official
[leanprover/comparator](https://github.com/leanprover/comparator), the
top level of the escalating checks in the Lean reference manual's
[Validating Proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
chapter.

Following community practice
([lamplighter-comparator](https://github.com/vidick/lamplighter-comparator),
[erdos-unit-distance-comparator](https://github.com/kim-em/erdos-unit-distance-comparator)),
the challenge lives in a separate repository —
**[MIPStarRE-comparator](https://github.com/LionSR/MIPStarRE-comparator)** —
which requires this library as a lake dependency pinned by commit:

- `Challenge.lean` there imports **only Mathlib** and re-declares, verbatim
  and in dependency order, every declaration in the comparator-relevant
  closure of the statement of `mainFormal` (111 declarations, ~1200 lines),
  then states the theorem with `sorry`.  It is the entire human audit
  surface.
- `Solution.lean` there imports this library, which proves the theorem under
  the same fully-qualified names; no bridging lemmas are needed.
- Its CI runs the comparator (real landrun sandbox, nanoda external kernel,
  `lean4checker` re-check) on every push and weekly.

## What this repository contributes

1. **Environment alignment.**  Comparator compares, constant by constant, the
   full kernel closure of the statement — types, definition bodies, and the
   proofs embedded in them — so `Challenge.lean` must elaborate to
   bit-identical terms.  Every module contributing a declaration to the
   closure therefore uses the full `import Mathlib` (directly or through
   `MIPStarRE/LDT/Basic/ParametersBase.lean` /
   `MIPStarRE/Quantum/FiniteMatrix/Basic.lean`), so tactic elaboration sees
   the same environment as the Mathlib-only `Challenge.lean`.  The four
   modules with direct Mathlib imports carry a comment saying not to narrow
   them.  (Measured impact: only 14 modules that did not already see full
   Mathlib through `Quantum/FiniteMatrix/Basic.lean` gained it.)
2. **Regeneration tooling.**  `scripts/comparator/` holds the closure
   extractor (a Lean metaprogram mirroring comparator's `runForUsedConsts`)
   and the assembler that produce `Challenge.lean`.  After changing any
   definition in the closure: regenerate per `scripts/comparator/README.md`,
   copy the result into MIPStarRE-comparator, and bump its library pin.

## Checklist against the official *Validating Proofs* guide

| Level | Requirement | Status |
|---|---|---|
| 2 | `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` | `MIPStarRE/LDT/Test/AxiomAudit.lean`; also enforced by comparator's `permitted_axioms` |
| 3 | `lean4checker --fresh` re-check | `lean4checker: true` in the comparator repo's lean-action step |
| 4 | Statement written in a trusted environment, separate from proof code | `Challenge.lean` imports only Mathlib (CI-enforced grep); separate repo, library pinned by commit |
| 4 | Sandboxed build + export + kernel replay | official comparator binary (pinned to the toolchain tag), real landrun in CI |
| 4 | External checker in addition to the Lean kernel | `enable_nanoda = true` (pinned nanoda tag); local macOS runs use `./verify.sh --fake-landrun` which disables it |
| 5 | No native evaluation (`Lean.trustCompiler`, `decide +native`) | excluded by `permitted_axioms` — comparator rejects any extra axiom |
| — | Statement review: custom notation and type classes must not obscure meaning | `Challenge.lean` uses no custom notation; review of it is the human step |

Deliberate deviations from the comparator README's adversarial setup, per its
own guidance for trusted trees: the `systemd-run` landrun-escape guard is
omitted and prebuilt `.lake` artifacts are reused, because both modules come
from a trusted checkout rather than an untrusted submitter.

Residual trust: Lean's logical soundness, comparator's own plumbing, sandbox
security, simultaneous bugs in all checkers, and human error in
`Challenge.lean` itself — keep that file short, notation-free, and reviewed.

## Benchmark use

The same statement is submission-ready for
[leanprover/lean-eval](https://github.com/leanprover/lean-eval) (the official
comparator-based benchmark behind [lean-lang.org/eval](https://lean-lang.org/eval/)):
port the statement module to lean-eval's toolchain, tag the theorem
`@[eval_problem]`, add a `manifests/problems/<id>.toml` (`holes`, `submitter`,
`source`, `informal_solution`), and open a PR to lean-eval.  Large
self-contained statement preludes have precedent there (the knot-theory
problems ship a 23 KB trusted `ChallengeDeps.lean`).  Solvers edit only
`Submission.lean`; scoring is comparator acceptance, with submissions run by
the Lean FRO's hosted pipeline.
