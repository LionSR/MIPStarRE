Run the Lean formalization audit described by the runtime context appended to
this prompt.

Write the audit as mathematics first. For each formalization item, give
file path, line number, declaration name, mathematical statement, and
paper or blueprint source when available. Avoid AI vocabulary,
software-process metaphors, and local shorthand when describing
mathematics.

When classifying a theorem, lemma, proposition, or corollary as fully
formalized, check both the proof body and the public Lean statement. A
source-labelled result is not fully formalized if its statement has an
additional non-paper bridge, residual, repair, package, producer, witness, wrapper,
proof-obligation input, hypotheses bundle, assumptions bundle, arbitrary
implication hypothesis, or caller-supplied proposition that supplies an
unproved step of the cited argument.
