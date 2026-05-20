# Issue #1507: degree-zero successor pasting-family obligation

## Source passage

The relevant part of the proof of the successor step is
`references/ldt-paper/inductive_step.tex:441-551`.  In the branch
`d = 0`, the successor proof must construct a family of degree-zero slice
polynomials and then apply the pasting theorem to obtain the next-stage
polynomial measurement.

## Lean classification

| declaration | classification | audit verdict |
| --- | --- | --- |
| `mainInductionSuccessorNextOfSmallError` | source-shaped proof obligation | The statement has the paper hypotheses for the small-error successor branch and remains the direct proof target. |
| `mainInductionSuccessorNext_degreeZero_ofPastingFamily` | internal conditional reduction | This theorem proves that a complete and point-consistent degree-zero family suffices.  It is not the paper theorem. |
| `DegreeZeroPastingFamilyObligation` | named internal proof obligation | This record names exactly the missing degree-zero family construction and the scalar error comparison. |
| `mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations` | internal conditional assembly | The stable interface still consumes the anonymous existential used before this PR. |
| `mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligation` | internal conditional assembly | This wrapper consumes the named degree-zero obligation and projects it to the stable existential interface. |
| `mainInductionSuccessorNext_ofDegreeSplitPastingObligations` | internal conditional assembly | The stable interface adds the large-error split while retaining the anonymous existential in the small-error branch. |
| `mainInductionSuccessorNext_ofDegreeSplitPastingObligation` | internal conditional assembly | This wrapper adds the large-error split while consuming the named degree-zero obligation in the small-error branch. |

## Statement integrity audit

No paper-facing declaration was strengthened in this change.

The source-facing theorem `mainInductionSuccessorNextOfSmallError` still has:

- paper assumptions: projective successor strategy, displayed error parameters,
  the successor size bound, and the small-error branch condition;
- Lean assumptions: the same mathematical hypotheses, with Lean's explicit
  field-model and finite-index parameters;
- paper conclusion: existence of a global polynomial measurement at the
  successor parameter with the next-stage consistency error;
- Lean conclusion: the same existence statement.

Verdict: the source-facing statement is unchanged.  The new record is an
internal construction target, not an extra hypothesis of `thm:main-induction`.

## Remaining mathematical task

Construct `DegreeZeroPastingFamilyObligation` from the source hypotheses in
the branch `params.d = 0`.  The expected construction is the family of
degree-zero slice polynomials used in the paper before the pasting step,
together with the comparison

```lean
ldPastingInInductionError params k eps delta gamma kappa zeta ≤
  mainInductionError params.next k eps delta gamma
```

for the produced completeness and consistency losses.
