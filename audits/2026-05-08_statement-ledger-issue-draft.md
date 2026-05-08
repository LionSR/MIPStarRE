# Draft: ledger issue body to replace closed #449 / #451

This file is a *draft* of the issue body to post when reopening (or replacing)
the smuggle ledger referenced by `docs/anti_patterns.md` §A6. **Not yet
posted** — awaiting user approval per PR-management protocol.

## Suggested title

```
Ledger: track *Statement extra-hypothesis structures (replaces #449, #451)
```

(Bracket-free, so any resulting `@codex` PR has a `@claude`-compatible branch
name per `docs/pr_review_management.md`.)

## Suggested labels

`tracking`, `formalization`, `2009.12982`

## Body

```markdown
## Purpose

This issue is the live ledger for the `*Statement` extra-hypothesis pattern
catalogued by [`docs/anti_patterns.md`](../blob/main/docs/anti_patterns.md) §A6.
It replaces the closed parents:

- #449 (paper-wide tracker, closed 2026-05-01)
- #451 (Ch04/Ch10 bridge-hypothesis ledger, closed 2026-04-30)

§A6 instructs contributors to file new `*Statement` structures here when
no producer exists. With #449 / #451 closed there was no live destination,
so 5 `*Statement` structures landed between 2026-04-18 and 2026-05-08
without a tracker entry. This issue restores that destination.

## Scope

A `*Statement` (or `*Witness` / `*Output` / `*Hypothesis`) structure is
**audit-clean** when it has at least one of:

- a **producer** theorem on the same branch (G);
- a **genuine external citation** named in the structure's docstring (E);
- an **open sub-issue** documenting the missing producer (T).

A `*Statement` with **no consumer** is dead scaffolding to delete (D), not a
tracked smuggle.

## Current inventory (39 entries, audit 2026-05-08)

Full table in
[`audits/2026-05-08_statement-smuggle-reaudit.md`](../blob/main/audits/2026-05-08_statement-smuggle-reaudit.md).
Headline counts:

| Verdict | Count |
|---|---|
| G — grounded (producer exists) | 35 |
| E — genuine external citation | 3 |
| T — tracked smuggle (open sub-issue) | 2 (Spectral truncation #1032; Naimark full tensor #1361) |
| P — paper-faithful packaging (no external consumer expected) | 1 |
| **D — dead** | **1** (`MatrixAddInUTransferStatement`) |

## Open obligations

### Cleanup

- [ ] **Delete or justify `MatrixAddInUTransferStatement`**
      (`MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:148`) — zero
      consumers, zero producers. (sub-issue: TBD)

### Verify

- [ ] **Verify `LdSandwichLineOnePointStatement` chain**
      (`MIPStarRE/LDT/Pasting/Statements.lean:334`). Heavy consumer footprint;
      producer not visible in top-level scan. Likely in
      `BridgeLemmas/LdSandwichLineOnePoint/`. Confirm and mark G, or open a
      tracker.
- [ ] **Verify `SdpStatement` external-consumer chain**
      (`MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean:78`). Producer
      at `Bracketed.lean:520`; downstream consumer chain unclear.

### Tracked-smuggle sub-issues (already open — link as sub-issues)

- [ ] #1032 — `SpectralTruncationStatement` producer (43 occurrences, core)
- [ ] #1230 — abstract / matrix SDP statements (`SdpStatement*`,
      `MatrixSdpStatementWithSlackness*`, `AddInUStatement`)
- [ ] #1359 — `OrthonormalizeAndCompleteStatement` extra-hypothesis chain
- [ ] #1361 — `NaimarkStatement` full tensor-product version (paper-gap by
      design)
- [ ] #1041, #1035, #1369 — `RestrictedProbabilitiesStatement` /
      `AnswerRestrictedProbabilitiesStatement` consumer chain
- [ ] #1364 — Ch06 (Global Variance) `*Statement`s

### Process

- [ ] Update `docs/anti_patterns.md` §A6 to point at this issue (replacing the
      stale #449 / #451 references).
- [ ] Extend the `\lean` / `\leanok` count badge requested in #1244 to also
      count `*Statement` structures and CI-assert against an allow-list, so a
      PR that adds a new `*Statement` without updating the ledger fails CI.

## Adding a new `*Statement` (process)

When a PR introduces a new `structure FooStatement ...` or `def FooStatement
... : Prop`:

1. The PR description must classify the structure as G / E / T / P (per the
   key above).
2. If T: link the sub-issue under this ledger.
3. If E: name the paper / Mathlib gap in the structure's docstring.
4. If G/P: name the producer theorem in the docstring.
5. The PR review must confirm the Statement has at least one consumer.

A future CI step will enforce (1)–(5) automatically.

## References

- `docs/anti_patterns.md` §A6
- `docs/proof_frontier_review.md`
- `docs/formalization-patterns.md`
- `audits/2026-05-08_statement-smuggle-reaudit.md`
```

## Posting plan (if approved)

1. Open this issue with the body above.
2. Add the existing trackers (#1032, #1230, #1359, #1361, #1041, #1035, #1369,
   #1364) as native sub-issues using `mcp__github__sub_issue_write`.
3. Create one new sub-issue:
   *"Delete or justify `MatrixAddInUTransferStatement`"* (single,
   bracket-free title; `@claude`-compatible).
4. Edit `docs/anti_patterns.md` §A6 to point at the new ledger number.
5. (Optional, separate PR) Extend the #1244 count-badge script to enforce
   the `*Statement` allow-list.
