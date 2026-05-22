#!/usr/bin/env python3
r"""Audit high-risk blueprint ``\lean{...}`` links.

This audit checks for blueprint-linked Lean declarations whose names contain
terms that often indicate proof-obligation packaging rather than a source
theorem:

``Bridge``, ``Residual``, ``Repair``, ``Package``, ``Input``, ``Producer``,
``Obligation``, ``Hypotheses``, ``Assumptions``, ``Witness``, ``Statement``,
``Slackness``, or ``Dominance``.

Such declarations are not automatically wrong.  Some are faithful construction
theorems or internal interfaces.  The required invariant is that every such
blueprint-linked declaration is explicitly covered in
``MIPStarRE/LDT/Test/AxiomAudit.lean``.  This keeps the classification
reviewable and prevents a high-risk name from entering the blueprint without a
corresponding axiom-closure assertion.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

from blueprint_lean_sync import BlueprintEntry, collect_blueprint_entries


HIGH_RISK_RE = re.compile(
    r"(Bridge|Residual|Repair|Package|Input|Producer|Obligation|"
    r"Hypotheses|Assumptions|Witness|Statement|Slackness|Dominance)"
)
ASSERTED_DECL_RE = re.compile(
    r"\bassert_[A-Za-z0-9_]+\s+([A-Za-z0-9_'.]+(?:\.[A-Za-z0-9_'.]+)*)"
)


@dataclass(frozen=True)
class HighRiskFinding:
    """One high-risk blueprint link not covered by ``AxiomAudit.lean``."""

    decl: str
    file: str
    line: int
    label: str | None
    env_type: str
    leanok: bool


@dataclass(frozen=True)
class HighRiskAuditResult:
    """Summary of the high-risk blueprint-link audit."""

    scanned_entries: int
    high_risk_entries: int
    audited_declarations: tuple[str, ...]
    findings: tuple[HighRiskFinding, ...]

    @property
    def ok(self) -> bool:
        return not self.findings


def strip_lean_line_comments(text: str) -> str:
    """Remove Lean line comments, preserving enough text for assertion parsing."""
    lines: list[str] = []
    for line in text.splitlines():
        lines.append(line.split("--", 1)[0])
    return "\n".join(lines)


def asserted_declarations(axiom_audit_path: Path) -> set[str]:
    """Return declarations explicitly passed to an ``assert_*`` command."""
    text = strip_lean_line_comments(
        axiom_audit_path.read_text(encoding="utf-8", errors="replace")
    )
    return set(ASSERTED_DECL_RE.findall(text))


def declaration_is_asserted(decl: str, asserted: set[str]) -> bool:
    """Return whether ``decl`` is explicitly audited.

    Prefer fully-qualified matches, but also accept an exact short-name match
    for declarations asserted inside an open namespace in ``AxiomAudit.lean``.
    """
    if decl in asserted:
        return True
    short = decl.rsplit(".", 1)[-1]
    return short in asserted


def run_audit(
    root: Path,
    *,
    leanok_only: bool = False,
) -> HighRiskAuditResult:
    """Run the high-risk blueprint-link audit under ``root``."""
    blueprint_src = root / "blueprint" / "src"
    axiom_audit_path = root / "MIPStarRE" / "LDT" / "Test" / "AxiomAudit.lean"
    entries = collect_blueprint_entries(blueprint_src)
    asserted = asserted_declarations(axiom_audit_path)

    findings: list[HighRiskFinding] = []
    high_risk_count = 0
    for entry in entries:
        if leanok_only and not (entry.has_leanok or entry.proof_has_leanok):
            continue
        if not HIGH_RISK_RE.search(entry.lean_decl):
            continue
        high_risk_count += 1
        if declaration_is_asserted(entry.lean_decl, asserted):
            continue
        findings.append(
            HighRiskFinding(
                decl=entry.lean_decl,
                file=entry.file,
                line=entry.line,
                label=entry.label,
                env_type=entry.env_type,
                leanok=entry.has_leanok or entry.proof_has_leanok,
            )
        )

    return HighRiskAuditResult(
        scanned_entries=len(entries),
        high_risk_entries=high_risk_count,
        audited_declarations=tuple(sorted(asserted)),
        findings=tuple(findings),
    )


def render_text(result: HighRiskAuditResult) -> str:
    """Render a human-readable audit report."""
    lines = [
        "Blueprint high-risk Lean-link audit",
        f"scanned entries: {result.scanned_entries}",
        f"high-risk entries: {result.high_risk_entries}",
        f"findings: {len(result.findings)}",
    ]
    for finding in result.findings:
        lines.append("")
        lines.append(
            f"{finding.file}:{finding.line}: {finding.decl}"
            f" in {finding.env_type} {finding.label or '<unlabelled>'}"
        )
        lines.append(
            "  Add an explicit assertion for this declaration to "
            "MIPStarRE/LDT/Test/AxiomAudit.lean, or remove the misleading "
            "blueprint link."
        )
    return "\n".join(lines)


def render_json(result: HighRiskAuditResult) -> str:
    """Render the audit result as JSON."""
    return json.dumps(asdict(result), indent=2, sort_keys=True)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument(
        "--leanok-only",
        action="store_true",
        help="check only high-risk declarations in entries carrying \\leanok",
    )
    parser.add_argument("--json", action="store_true", help="print JSON output")
    parser.add_argument("--ci", action="store_true", help="fail when findings exist")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""
    args = parse_args(sys.argv[1:] if argv is None else argv)
    result = run_audit(args.root.resolve(), leanok_only=args.leanok_only)
    if args.json:
        print(render_json(result))
    else:
        print(render_text(result))
    return 1 if args.ci and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
