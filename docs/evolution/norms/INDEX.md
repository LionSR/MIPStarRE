# Norms Index

Append-only ledger of accepted repository norms. New norms are added at the
bottom with the next free four-digit ID. Existing rows are updated in place
when a norm changes status (accepted / superseded). Never delete a row.

| ID   | Title                                                  | Scope               | Enforcement                                  | Status   |
|------|--------------------------------------------------------|---------------------|----------------------------------------------|----------|
| 0001 | Read paper source before formalizing                   | Lean, blueprint     | `AGENTS.md` §Project Overview, manual review | accepted |
| 0002 | Prefer Mathlib over custom helpers                     | Lean                | `AGENTS.md` §Mathlib integration, anti-patterns audit | accepted |
| 0003 | Read CI failure logs before retrying                   | All agents          | `audit_ci_waste.py`, this charter §5         | accepted |
| 0004 | File a friction report on the second recurrence        | All agents          | `docs/evolution/friction/`, weekly meta-loop | accepted |
| 0005 | Resolve drift alarms by fixing causes, not thresholds  | All agents          | `audit_drift.py`, drift-alarm workflow       | accepted |

## How to add a norm

1. Copy `TEMPLATE.md` to `NNNN-kebab-case-title.md` using the next free ID.
2. Fill in **Rationale**, **Rule**, **Worked example**, and **Signals that
   this norm is failing**.
3. Append a row to the table above.
4. Update `AGENTS.md` if the norm should be visible to every coding agent.
5. If the norm can be mechanically checked, add or extend a script under
   `scripts/` and wire it into a workflow.

## How to retire a norm

Norms are not deleted. If a norm becomes obsolete:

1. Set the **Status** in its file to `superseded by NNNN` (or `retired`).
2. Add a closing paragraph explaining what changed about the repository so
   that the norm is no longer needed.
3. Update the row above to reflect the new status. Keep the row.
