# Issue 1557: Boundary Input Classification Audit

This note records the source comparison for the remaining faithful-boundary
findings reported by `scripts/audit_paper_facing_proof_debt.py` after the
slice-boundedness repair in issue #1556.

## Audit Command

On the current branch, the command

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root . --ci
```

reports zero proof-debt header findings and zero conditional declaration-name
findings. The remaining faithful boundary-input findings are the explicit
slice-boundedness hypotheses and `CascadeHypotheses`.

## Slice Boundedness

The source statements are:

- `references/ldt-paper/commutativity-G.tex:29-36`,
  item `item:data-processed-boundedness` in `lem:comm-data-processed-g`;
- `references/ldt-paper/ld-pasting.tex:28-35`,
  item `item:ld-pasting-boundedness` in `thm:ld-pasting`.

Both statements assume positive semidefinite witnesses `Z^x`, an averaged
residual bound

```text
E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta,
```

and the pointwise domination condition

```text
Z^x >= E_u A^{u,x}_{g(u)}.
```

Lean now states these three assumptions directly in the relevant theorem
headers: witness positivity, the averaged residual bound, and domination of the
averaged point-evaluation operator.  No separate domination-target
identification field is exposed.  Thus the remaining boundedness findings are
source hypotheses, not hidden proof obligations.

## `CascadeHypotheses`

The source comparison for `CascadeHypotheses` is against the final error
calculation in `references/ldt-paper/inductive_step.tex:187-234` and the
corresponding blueprint definition
`blueprint/src/chapter/ch10_induction.tex:545-564`.

The Lean structure records only the scalar regime used in the cascade:

- `k >= 1`;
- `m >= 1`;
- `0 <= eps`;
- `eps <= 1`;
- `d <= q`;
- `q > 0`.

These fields are not bridge, residual, repair, producer, package, or
construction data. They are the hypotheses needed to make the paper's
asymptotic comparisons into inequalities over real-valued error parameters:
fractional powers are compared on `[0,1]`, `d/q` is bounded by `1`, and lower
powers of `k` and `m` are absorbed into `k^2 m^4`.

The final theorem does not acquire `CascadeHypotheses` as a new assumption.
`MIPStarRE.LDT.Test.cascadeHypotheses_of_not_mainFormalError_ge_one` derives
the scalar regime in the non-vacuous branch; if `eps > 1` or `d > q`, the final
error envelope is already at least `1`, so the theorem is handled by the
vacuous branch.

## Verdict

The current faithful-boundary allowlist contains no known internal
identification bridge.  The explicit slice-boundedness hypotheses are paper
hypotheses, and `CascadeHypotheses` is an explicit scalar form of the paper's
unit-scale error regime. Future additions to this allowlist should receive the
same field-level source comparison before being accepted.
