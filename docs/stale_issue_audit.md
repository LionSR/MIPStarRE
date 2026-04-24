# Stale-issue audit for theorem / sorry trackers

This document describes the periodic triage workflow for open formalization
issues in this repo, and how to run
[`scripts/audit_stale_issues.py`](../scripts/audit_stale_issues.py).

## Motivation

Issue trackers that name specific `sorry` sites, file/line locations, or
declaration names drift out of date whenever `main` moves:

- a referenced file is split, renamed, or deleted;
- the cited line number is no longer a `sorry` after a proof lands;
- a named declaration is inlined, renamed, or removed.

Issue #301 is a worked example — it stayed open long after its named
blockers (`spectralTruncateAlmostProjective`, `orthonormalization`) had
been resolved on `main`, and PR #647 had to do a retroactive cleanup pass.
This audit script exists so humans can catch that drift earlier.

## What the script does

Given a JSON dump of open issues, the script extracts three kinds of
citations from each issue body and checks them against the current
working tree:

| Citation pattern | Example | Stale if … |
|------------------|---------|------------|
| `MIPStarRE/.../X.lean`        | `MIPStarRE/LDT/Foo.lean`           | the file no longer exists |
| `MIPStarRE/.../X.lean:LINE`   | `MIPStarRE/LDT/Foo.lean:131`       | the line is no longer a `sorry`/`admit` |
| ``` `declName` ``` (backtick) | `` `spectralTruncateAlmostProjective` `` | no matching `def`/`theorem`/`lemma`/`instance`/`class`/`structure`/`abbrev`/`inductive`/`opaque` exists under `MIPStarRE/` |

The tool is **report-only** — it never edits or closes issues and never
posts comments.  Its output is intended for human review by a maintainer
doing periodic triage before launching a proof-closing round.

## Why a script, not a live workflow

Authenticated `gh` calls in CI are awkward (the default `GITHUB_TOKEN`
can list issues but rate-limits across large repos, and the script is
most useful to run locally alongside other maintenance scripts).  The
script therefore reads pre-exported JSON from `gh issue list`.  Running
it on a CI schedule remains a possible follow-up (see
[`docs/ci-automation.md`](ci-automation.md)), but the v1 is deliberately
offline-friendly.

## Usage

### One-shot local audit

```bash
# 1. Export open issues that plausibly reference code.
gh issue list --repo LionSR/MIPStarRE --state open --limit 500 \
  --json number,title,body,url,labels \
  > /tmp/mipstarre-open-issues.json

# 2. Run the audit.  Default output lists only flagged issues.
python3 scripts/audit_stale_issues.py \
  --issues /tmp/mipstarre-open-issues.json
```

### Narrower scope (sorry trackers only)

```bash
gh issue list --repo LionSR/MIPStarRE --state open --limit 500 \
  --label sorry-elimination \
  --json number,title,body,url,labels \
  > /tmp/mipstarre-sorry-issues.json

python3 scripts/audit_stale_issues.py \
  --issues /tmp/mipstarre-sorry-issues.json
```

### Machine-readable output

```bash
python3 scripts/audit_stale_issues.py \
  --issues /tmp/mipstarre-open-issues.json \
  --format json \
  --output /tmp/audit.json
```

### Credentials-free self-test

```bash
python3 scripts/audit_stale_issues.py --self-test
```

The self-test constructs a synthetic issue that references a non-existent
file and a non-existent declaration, runs the audit against the current
checkout, and exits 0 only if both flags fire.  Use this to verify the
tool still works after editing the script or changing the repository
layout.

## Output format

Text mode groups each flagged issue:

```
Stale-issue audit report
========================
issues scanned        : 147
issues with citations : 92
issues flagged stale  : 6

#301 — Audit: Ch5 MMP — prove spectralTruncateAlmostProjective + …
------
  https://github.com/LionSR/MIPStarRE/issues/301
  declarations not found under MIPStarRE/:
    - spectralTruncateAlmostProjective
    - orthonormalization
```

JSON mode emits an array with the same information keyed by issue number
and suitable for downstream automation.

## Recommended cadence and follow-up

1. Run the audit before kicking off a new proof-closing round (monthly
   or before a campaign, whichever is sooner).
2. For each flagged issue, open it and decide:
   - close it as resolved, optionally with a comment like
     `resolved in #...` or `stale on current main; close after audit`;
   - update the body so the cited file/line/declaration matches current
     `main`;
   - leave it open if the flag is a false positive (e.g. a backticked
     word that happens to look like an identifier).
3. Do **not** let the script close issues automatically.  Flags are a
   starting point for human review, not a decision.

## Known limitations

- Backtick-quoted tokens are matched against unqualified declaration
  names.  A false positive is possible when an issue cites a plain
  English word that happens to look like a Lean identifier; the
  stoplist in `_DECL_STOPLIST` suppresses the most common offenders.
- Line-number checks only consider whether the cited line currently
  contains `sorry` or `admit`.  A `sorry` that moved a few lines up or
  down will be flagged even though the tracker is still basically
  valid — in practice, triage that as "issue body wants a line-number
  refresh".
- The script does not consult `git log`; it only inspects the checkout
  it runs against.  Run it from a clean checkout of current `main` for
  the most meaningful report.

## Related scripts

- [`scripts/blueprint_lean_sync.py`](../scripts/blueprint_lean_sync.py)
  — blueprint ↔ Lean declaration sync.
- [`scripts/check_blueprint_sync.py`](../scripts/check_blueprint_sync.py)
  — axiom-level `\leanok` verification harness used by CI.
