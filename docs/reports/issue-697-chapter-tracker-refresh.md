# Issue 697 Chapter-Tracker Umbrella Refresh

Audit date: 2026-04-24

Scope: one-time sweep across the chapter-tracker umbrellas and the cross-cutting trackers to
drop stale closed-issue references from the human-readable indexes and repoint each umbrella
at the currently-open leaf issues on `main`. See `#656` for the recurring periodic audit.

## Method

1. Listed all issues with `state: OPEN` via the GitHub API to establish the live set.
2. Fetched the body of each umbrella in scope and cross-checked every referenced issue
   against the open set.
3. Moved closed references out of "Remaining chapter tasks" and into "Completed chapter
   milestones" (or deleted when no longer relevant).
4. Added the four new sibling leaf issues filed alongside this sweep (#693, #694, #695, #696)
   under their owning umbrellas.
5. Added already-open leaf issues that currently own chapter work but were previously not
   linked from the umbrella (for example the Section-6 wrapper chain on `#104`).
6. Left the Notes sections intact where the referenced PR / issue is still relevant; trimmed
   only the sentences that pointed at closed work as if it were still live.

## Umbrellas touched

| Umbrella | Remaining (open) | Completed (moved) |
|---|---|---|
| #101 Ch 2 Test | #422, #560, #669 | #306, #454, #596 |
| #103 Ch 4 Projective | #651, #652 | #301, #396, #450, #525, #595 |
| #104 Ch 5 Main Induction | #427, #628, #630, #633, #634, #653, #667 | #428, #552, #585, #593, #603 |
| #105 Ch 6 Expansion | — (no live leaf) | #162, #452, #594 |
| #106 Ch 7 Global Variance | #694 | #163, #302, #321, #594 |
| #107 Ch 8 Self-Improvement | #654 | #301, #321, #396, #450, #453, #594 |
| #108 Ch 9 Commutativity of Points | #529 | #367, #592 |
| #110 Ch 11 Pasting | #299, #300, #351, #639, #672, #673, #687, #689, #691, #693, #695 | #298, #395, #570, #586, #597, #598 |
| #422 mainFormal assembly | #423, #424, #425, #426, #427 | #428, #470, #471, #509, #552, #593, #596 |
| #439 Phase 2 sweep | #299, #300, #351, #361, #411, #639, #651, #652, #654, #672, #673, #694, #695 | #301, #367, #395, #396, #552, #570, #589, #590, #592, #593, #594, #596, #597, #598 |
| #449 Paper-wide | #101–#110, #422, #439, #451, #656, #670, #696, #697 | #589, #590, #596, #597, #598 |
| #451 Bridge-package | #651, #652 | #301, #396, #428, #525, #595 |

## Known gaps follow-up

- Ch 3 Preliminaries (#102): already documented as having no dedicated open child; confirmed
  still accurate. Future Chapter-3-local gaps should be filed as fresh leaves under #102.
- Ch 6 Expansion (#105): both live leaves (#452, #594) were already closed. No new leaf
  filed in this sweep; the umbrella now documents the empty leaf state explicitly and asks
  future contributors to file new leaves if chapter-local gaps reappear.
- Ch 10 Commutativity of G (#109): live leaf set `{#411, #600, #601}` reviewed; no edits
  required. Older umbrella issues (#296, #297, #361, #478) remain linked for historical
  snapshot context.

## Non-goals

- No umbrellas were closed; all remain open as living indexes.
- No umbrellas were merged.
- Notes sections were trimmed only where a referenced PR/issue became stale.
- No Lean code or blueprint `.tex` was modified in this sweep.
