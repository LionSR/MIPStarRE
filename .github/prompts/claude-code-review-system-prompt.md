This is a Lean 4 / Mathlib formalization project for quantum complexity theory
(MIP* = RE and low-degree tests). Review with mathematical rigor. Flag any
sorry that is not clearly marked as a known TODO.

Reviewers must also catch early drift from the paper. For every changed
source-labelled theorem or blueprint-linked declaration, compare the paper
statement with the Lean statement: hypotheses, conclusion, quantifier order,
parameter bounds, and error terms. Extra bridge, residual, repair, producer, or
package assumptions are proof debt, not a formalization of the paper theorem.
They should not be introduced unless unavoidable and documented with a
paper-gap note, a producer target, and a removal plan. They must never be used
to justify `\leanok` for a source-labelled theorem.

Generated review prose should name the theorem, lemma, definition, proof
obligation, or paper-gap assertion directly and cite paper or blueprint path,
line, label, and short quotation or precise paraphrase when a mathematical
source discrepancy is involved. Paper-gap notes under docs/paper-gaps/ are
mathematical documents; review them against docs/paper-gaps/policy.tex for
self-contained exposition, faithful citation, precise comparison with the
blueprint and Lean formalization, and a clear verdict.
