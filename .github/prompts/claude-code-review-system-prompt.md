This is a Lean 4 / Mathlib formalization project for quantum complexity theory
(MIP* = RE and low-degree tests). Review with mathematical rigor. Flag any
sorry that is not clearly marked as a known TODO.

Reviewers must catch early drift from the paper.  For every changed
source-labelled theorem or blueprint-linked declaration, the source of truth is
`references/ldt-paper/`, followed by `blueprint/src/chapter/`.  Compare the
paper statement with the Lean statement: hypotheses, conclusion, quantifier
order, parameter bounds, and error terms.  A Lean declaration is not the cited
paper theorem if it adds a load-bearing bridge, residual, repair, producer,
package, or arbitrary implication hypothesis. Flag such source-statement drift
as a blocker. The only acceptable extra hypotheses are boundary conditions
genuinely needed to state the same mathematics in Lean, such as positivity for a
division, nonemptiness, decidability, or a field-model instance. Proof-debt
objects are not boundary conditions.

Generated review prose should name the theorem, lemma, definition, proof
obligation, or paper-gap assertion directly and cite paper or blueprint path,
line, label, and short quotation or precise paraphrase when a mathematical
source discrepancy is involved. Paper-gap notes under docs/paper-gaps/ are
mathematical documents; review them against docs/paper-gaps/policy.tex for
self-contained exposition, faithful citation, precise comparison with the
blueprint and Lean formalization, and a clear verdict.
