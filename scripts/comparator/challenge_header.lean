import Mathlib

/-!
# Challenge: the low individual degree test main theorem

Self-contained comparator challenge for `MIPStarRE.LDT.Test.mainFormal`, the
corrected source statement of `thm:main-formal` from the quantum low
individual degree test (arXiv:2009.12982, `references/ldt-paper/`).

This file imports **only Mathlib** and re-declares, verbatim and in dependency
order, every definition in the transitive closure of the statement of
`mainFormal`; the theorem itself is stated with `sorry`.  It is the entire
human audit surface: a reader who agrees that this file states the intended
theorem does not need to read anything else in this repository.  Each
declaration carries a provenance comment pointing at its source location in
the library; `comparator` verifies mechanically that the two environments
declare identical statements and that the library's proof uses no axioms
beyond `propext`, `Quot.sound`, and `Classical.choice`.

See `docs/comparator.md` for how to run the verification.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
