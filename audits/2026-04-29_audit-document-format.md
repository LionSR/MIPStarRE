---
title: Audit document format
date: 2026-04-29
purpose: >
  Defines the audit-file naming, YAML front matter, terminology, and review
  use conventions for MIPStarRE audit documents.
status: active
track: documentation
kind: audit-format
origin: "issue #913"
issue: "#913"
pr: "#915"
---

# Audit Document Format

This file gives the common format and terminology for audit documents under
`audits/`. Every audit file should begin with YAML front matter. New audit
files and substantive updates to existing audits should also follow the section
format below.

## Metadata

Every audit should begin with YAML front matter in this shape:

```yaml
---
title: "Short human-readable title"
date: YYYY-MM-DD
purpose: >
  One or two sentences explaining what the audit records and how it should be
  used by later readers.
---
```

Use `issue` and `pr` when the audit is tied to a specific GitHub issue or pull
request:

```yaml
issue: "#N"
pr: "#M"
```

The values should be quoted strings such as `"#913"` so YAML parses them as
text rather than comments.

Existing or useful classification fields may be kept. In this repository the
common ones are:

```yaml
status: active
track: paper2009ldt
kind: naming-audit
origin: internal
```

These fields are optional metadata, not a replacement for the prose purpose.
When adding a new audit, prefer the minimal header above unless the extra fields
help later readers sort or review the audit.

## File Names

Dated audit artifacts should use a leading `YYYY-MM-DD_` filename. For example,
use `2026-04-29_mathematical-naming-audit.md`, not
`mathematical-naming-audit_2026-04-29.md` and not
`20260429_mathematical-naming-audit.md`.

## Required Sections

Use these sections unless the audit is deliberately narrower:

- `Scope`: the files, declarations, prose, or mathematical objects audited.
- `Source of Truth`: the paper, blueprint chapter, or repository convention used
  to decide the mathematical terminology.
- `Findings`: the observed mismatches, grouped by mathematical topic or API
  surface.
- `Required Action`: the precise cleanup or migration needed before the audit
  can be marked resolved.
- `Validation`: the Lean, blueprint, or documentation checks relevant to the
  audit.
- `Review Use`: how reviewers should apply the audit in later PRs.

## Term Norm

Audit prose should use terms from the mathematical source, the blueprint, or an
established repository convention. It should not introduce project management
phrases as mathematical names. In particular, avoid presenting words such as
`pipeline`, `wrapper`, `package`, `raw`, `oneShot`, or `liveBlock` as preferred
mathematical terminology unless the cited source uses them with that meaning.

When an audit names a problematic existing identifier, describe it as a legacy
identifier or a finding. Do not turn an implementation-history word into the
title of a new concept. Prefer terms such as:

- `finding`
- `required action`
- `legacy identifier`
- `source of truth`
- `validation`
- `review use`
- `API migration`

For Lean naming audits, a name is suspect when it encodes historical
formalization status rather than mathematical content. If a public name cannot
be changed immediately, record the migration here or in a linked issue, and do
not add an empty pass-through abbreviation just to create a second public name.

## Review Rule

When a review fix touches a surface covered by an active audit, the audit is
required reading. A PR is not ready to merge if it ignores an in-scope required
action, leaves the same terminology problem on the touched surface, or replaces
it only with an empty pass-through abbreviation. If the PR deliberately defers
the migration, it should update the audit or linked issue with the remaining
work and the mathematical reason for the deferral.
