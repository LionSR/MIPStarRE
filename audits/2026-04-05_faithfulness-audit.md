---
title: Faithfulness audit
date: 2026-04-05
purpose: >
  Audits faithfulness of the LDT formalization to the paper and records
  statement-level mismatches requiring mathematical review.
status: snapshot
track: paper2009ldt
kind: faithfulness-audit
---

# Faithfulness Audit

This audit compares the following paper/blueprint pairs for mathematical faithfulness:

- `references/ldt-paper/preliminaries.tex` -> `blueprint/src/chapter/ch03_preliminaries.tex`
- `references/ldt-paper/orthonormalization.tex` -> `blueprint/src/chapter/ch04_projective.tex`
- `references/ldt-paper/self_improvement.tex` -> `blueprint/src/chapter/ch07_self_improvement.tex`
- `references/ldt-paper/commutativity-G.tex` -> `blueprint/src/chapter/ch08_commutativity.tex`

## High-level summary

- Copy-paste detection: I did not find any serious verbatim proof-sketch copy-paste from the paper into the blueprint. The blueprint is generally shorter and usually rephrases the paper's proofs in its own voice.
- Timing note: this audit was run after the blueprint expansion work, so the label counts below reflect the post-expansion state rather than the earlier pre-expansion gap counts used in some proof-planning notes.
- Missing labels:
  - `preliminaries`: paper `47`, blueprint `55`. No paper labels are missing.
  - `orthonormalization`: paper `38`, blueprint `36`. The paper-only labels are `sec:making-measurements-projective`, `ex:easy-but-long`, and `eq:awefea`; these belong to the omitted Naimark counterexample/example material rather than the main theorem chain.
  - `self_improvement`: paper `56`, blueprint `57`. No paper labels are missing.
  - `commutativity-G`: paper `34`, blueprint `38`. No paper labels are missing.

## Findings

### 1. `ch03_preliminaries`: `\polyfunc` changes the underlying object from polynomials to functions

- Paper: `references/ldt-paper/preliminaries.tex:89-94`
- Blueprint: `blueprint/src/chapter/ch03_preliminaries.tex:57-59`

The paper defines `\polyfunc{m}{q}{d}` as a set of polynomials of individual degree `d`. The blueprint defines it as a set of functions `\F_q^m \to \F_q` represented by such polynomials.

This is a real mathematical shift, not just a stylistic rewrite: over finite fields, distinct polynomials can induce the same function, so the blueprint's definition quotients by functional equivalence while the paper does not.

What to change:

- Rewrite the blueprint definition so that `\polyfunc{m}{q}{d}` is again a set of polynomials, not a set of functions.
- If the Lean formalization genuinely works with polynomial functions, add an explicit remark explaining the identification and the hypothesis under which it is harmless, rather than silently changing the definition.

### 2. `ch03_preliminaries`: the definition of submeasurement is strengthened from an arbitrary outcome set to a finite outcome set

- Paper: `references/ldt-paper/preliminaries.tex:127-137`
- Blueprint: `blueprint/src/chapter/ch03_preliminaries.tex:83-85`

The paper says "let `\mathcal A` be a set of outcomes"; the blueprint says "let `\mathcal A` be a finite outcome set".

In the surrounding project this may be harmless, but it is still a stronger hypothesis than the paper states. Since this is a foundational definition, the blueprint should not silently strengthen it unless the finiteness assumption is needed later and is called out explicitly.

What to change:

- Either revert to the paper's statement with an arbitrary outcome set, or
- add a short note that the blueprint restricts to the finite-outcome case because that is the only case used downstream / formalized in Lean.

### 3. `ch07_self_improvement`: the helper lemma's final constant bookkeeping is over-compressed

- Paper: `references/ldt-paper/self_improvement.tex:591-624`
- Blueprint: `blueprint/src/chapter/ch07_self_improvement.tex:226-257`

The blueprint compresses the last part of the proof of `lem:self-improvement-helper` to:

- "The paper's arithmetic shows that the right-hand error is at most ..."
- "the paper bounds by ..."

This loses mathematical content. In the paper, the exact accumulated error terms are still displayed before being absorbed into `\zeta`, and those displayed terms are what let the reader check that the constants are correct.

What to change:

- Keep the proof short, but explicitly restate the pre-absorption error expressions before the final `\le \zeta` step.
- In particular, the sketch should show the bounds corresponding to
  - `11 \sqrt{\zeta_{\mathrm{variance}}} + \sqrt{2\delta} + md/q`, and
  - `3\sqrt{\delta} + 4\sqrt{\zeta_{\mathrm{variance}}}`,
  before concluding that each is at most `\zeta`.

### 4. `ch07_self_improvement`: the projective-output theorem suppresses too much of the exponent bookkeeping

- Paper: `references/ldt-paper/self_improvement.tex:764-810`
- Blueprint: `blueprint/src/chapter/ch07_self_improvement.tex:527-552`

The blueprint ends the proof of `thm:self-improvement` with "The paper's exponent bookkeeping then shows ...", followed by only the final inequalities. That is too compressed for this theorem: the exponent cascade

- `\widehat\zeta`
- `\widehat\zeta_{\mathrm{ortho}}`
- `\widehat\zeta_{\mathrm{dataprocess}}`
- the four transferred conclusion errors

is part of the mathematical content, not just editorial detail.

What to change:

- Add a short displayed derivation mirroring the paper's three bookkeeping steps:
  - bound `\widehat\zeta_{\mathrm{ortho}}` in terms of `(\eps^{1/8},\delta^{1/8},(d/q)^{1/8})`,
  - bound `\widehat\zeta_{\mathrm{dataprocess}}` in terms of `(\eps^{1/16},\delta^{1/16},(d/q)^{1/16})`,
  - then show the four final error quantities are each at most `\zeta`.
- The proof can stay much shorter than the paper, but it should not outsource all of this to "the paper's bookkeeping".

### 5. `ch08_commutativity`: the proof of `thm:com-main` is compressed past the point where the second-term argument is reconstructible

- Paper: `references/ldt-paper/commutativity-G.tex:332-416`
- Blueprint: `blueprint/src/chapter/ch08_commutativity.tex:302-373`

The blueprint's first-term sketch is fine, but the second-term analysis is compressed too aggressively. The paper goes through:

- the `\eqref{eq:gcom4}` comparison,
- the first Schwartz–Zippel evaluation step,
- two `\prop:closeness-of-ip` transports,
- the second Schwartz–Zippel evaluation step,
- the evaluated commutativity lemma,
- the final transport back to `\bra{\psi} G \ot G \ket{\psi}`,
- and then an explicit error tally.

The blueprint collapses almost all of this into a few sentences and finishes with "exactly as in the paper". At that point the reader no longer has enough information to reconstruct where the final
`30m(\gamma^{1/4}+\zeta^{1/4}+(d/q)^{1/4})`
comes from.

What to change:

- Expand the sketch enough to name the intermediate expressions corresponding to the paper's
  - `\eqref{eq:gcom4}`,
  - `\eqref{eq:evaluate-gcom-at-points}`,
  - `\eqref{eq:don't-understand-the-numbering-system}`,
  - `\eqref{eq:evaluate-gcom-at-points-part-dos}`.
- Include the actual error sources being summed: the two `\sqrt{\zeta}` transports, the two `dm/q` Schwartz–Zippel losses, and the `\sqrt{\nu_{\mathrm{evaluation}}}` contribution coming from the evaluated commutativity lemma.
- Replace "exactly as in the paper" with a short explicit bound, even if abbreviated.

## No additional issues found

- `ch04_projective` is faithful overall. I did not find statement mismatches in the main theorem chain, and I did not find proof sketches that were verbatim copies of the paper.
- Apart from the two foundational-definition shifts in `ch03_preliminaries`, the remaining statement-level rewrites I checked were faithful to the paper.
