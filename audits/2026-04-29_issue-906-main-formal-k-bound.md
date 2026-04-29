---
title: "Issue 906 main-formal k-bound audit"
date: 2026-04-29
purpose: >
  Records the large-k side-condition gap in the paper statement of the main
  formal low individual degree theorem and the corresponding formal statement
  repair.
status: active
track: paper2009ldt
kind: statement-fix-audit
origin: "issue #906"
issue: "#906"
---

# Issue 906: Large-`k` Side Condition In The Main Formal Theorem

The paper statement of the main formal low individual degree theorem assumes
`k >= m d`. In the successor step of the proof, however, the argument invokes
the pasting theorem from Section 6, whose hypotheses include the stronger
condition `k >= 400 * m * d` for the relevant ambient dimension. The inequality
`k >= m d` does not imply this Section 6 side condition, so the printed proof
does not justify the full interval `m d <= k < 400 * m * d`.

This is a side-condition gap in the mathematical proof, not a Lean artifact.
The formal public statement is therefore strengthened to assume
`k >= 400 * m * d`. The formalization records the hypothesis actually needed
for the pasting argument instead of hiding the gap behind an unjustified
arithmetic step or a vacuous-case argument. Trivial witnesses are used only in
branches where the final error parameter is already at least one, so the
consistency claims are saturated.
