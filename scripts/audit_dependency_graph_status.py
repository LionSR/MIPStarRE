#!/usr/bin/env python3
r"""Audit selected LDT dependency-graph node statuses.

The blueprint source is the authoritative mathematical object.  The generated
``dep_graph_document.html`` is nevertheless what a reader sees on GitHub Pages,
so it must not preserve stale green nodes after a source-boundary repair.  This
audit checks the small set of graph statuses that currently carry mathematical
meaning for the LDT frontier:

* retired successor-boundary nodes must not appear;
* source-frontier nodes with tracked proof debt must be present and must not be
  displayed as statement-complete or proof-complete;
* corrected Lean-only current-interface nodes that are now proved must be
  proof-filled;
* the now-proved Naimark tensor-product theorem must be proof-filled locally.

The check is intentionally narrow.  It is a consistency guard for the generated
graph, not a replacement for statement comparison against ``references/ldt-paper``.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


PROOF_FILLED_COLORS = {"#1CAC78", "#9CEC8B"}

ABSENT_LABELS = {
    "def:main-formal-successor-boundary",
    "def:main-formal-step6-successor-targets",
    "def:successor-obligation-reductions",
    "prop:main-induction-successor-degree-zero-family",
    "prop:main-formal-source-successor-construction",
}

NOT_PROOF_FILLED_LABELS = {
    "prop:main-formal-source-k-range-boundary",
    "prop:main-formal-source-obligation",
    "prop:main-formal-source-small-error-obligation",
    "prop:main-formal-source-two-space-role-register",
    "prop:main-induction-source-range-obligation",
    "thm:main-formal",
    "thm:main-induction",
}

NOT_GREEN_BORDER_LABELS = NOT_PROOF_FILLED_LABELS

PROOF_FILLED_LABELS = {
    "prop:main-induction-successor-answer-valued-pasting",
    "prop:main-induction-successor-small-error-construction",
    "prop:main-induction-successor-predecessor-induction",
    "thm:main-formal-current-interface",
    "thm:main-induction-current-interface",
    "thm:naimark",
}

GREEN_BORDER_LABELS = {
    "rem:lean-naimark-auxiliary-declarations",
    "thm:naimark",
}


@dataclass(frozen=True)
class GraphNode:
    """One node record extracted from the dependency graph DOT payload."""

    label: str
    color: str | None
    fillcolor: str | None
    style: str | None
    shape: str | None

    @property
    def has_green_border(self) -> bool:
        return self.color == "green"

    @property
    def is_proof_filled(self) -> bool:
        return (
            self.has_green_border
            and self.fillcolor in PROOF_FILLED_COLORS
            and self.style is not None
            and "filled" in self.style.split(",")
        )


@dataclass(frozen=True)
class GraphFinding:
    """One dependency-graph status discrepancy."""

    label: str
    kind: str
    message: str
    color: str | None = None
    fillcolor: str | None = None
    style: str | None = None


@dataclass(frozen=True)
class GraphAuditResult:
    """Summary of the dependency-graph status audit."""

    graph_path: str
    scanned_nodes: int
    findings: tuple[GraphFinding, ...]

    @property
    def ok(self) -> bool:
        return not self.findings


def extract_dot(text: str) -> str:
    """Return the DOT payload embedded in ``dep_graph_document.html``."""
    match = re.search(r"\.renderDot\(`(.*)`\)\s*\.on", text, re.S)
    if match is None:
        raise ValueError("could not find the dependency-graph DOT payload")
    return match.group(1)


def parse_attrs(text: str) -> dict[str, str]:
    """Parse a Graphviz attribute list used by LeanBlueprint."""
    attrs: dict[str, str] = {}
    attr_re = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(\"[^\"]*\"|[^,\]]+)")
    for match in attr_re.finditer(text):
        value = match.group(2).strip()
        if len(value) >= 2 and value[0] == value[-1] == '"':
            value = value[1:-1]
        attrs[match.group(1)] = value
    return attrs


def parse_nodes_from_dot(dot: str) -> dict[str, GraphNode]:
    """Extract node records from a Graphviz DOT payload."""
    nodes: dict[str, GraphNode] = {}
    for statement in dot.split(";"):
        statement = statement.strip()
        if "{" in statement:
            statement = statement.rsplit("{", 1)[1].strip()
        if "}" in statement:
            statement = statement.split("}", 1)[0].strip()
        if not statement or "->" in statement:
            continue
        match = re.fullmatch(r'"([^"]+)"\s*\[(.*)\]', statement, re.S)
        if match is None:
            continue
        attrs = parse_attrs(match.group(2))
        if "shape" not in attrs:
            continue
        label = match.group(1)
        nodes[label] = GraphNode(
            label=label,
            color=attrs.get("color"),
            fillcolor=attrs.get("fillcolor"),
            style=attrs.get("style"),
            shape=attrs.get("shape"),
        )
    return nodes


def audit_nodes(nodes: dict[str, GraphNode]) -> tuple[GraphFinding, ...]:
    """Check the LDT graph frontier-status invariants."""
    findings: list[GraphFinding] = []

    for label in sorted(ABSENT_LABELS):
        node = nodes.get(label)
        if node is not None:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="retired-node-present",
                    message="retired successor-boundary node is still present in the graph",
                    color=node.color,
                    fillcolor=node.fillcolor,
                    style=node.style,
                )
            )

    for label in sorted(NOT_PROOF_FILLED_LABELS):
        node = nodes.get(label)
        if node is None:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="frontier-node-missing",
                    message="frontier node with tracked proof debt is absent from the graph",
                )
            )
        elif node.is_proof_filled:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="frontier-proof-filled",
                    message="tracked proof-frontier node is displayed as proof-complete",
                    color=node.color,
                    fillcolor=node.fillcolor,
                    style=node.style,
                )
            )

    for label in sorted(NOT_GREEN_BORDER_LABELS):
        node = nodes.get(label)
        if node is not None and node.has_green_border:
            if label in NOT_PROOF_FILLED_LABELS:
                if node.is_proof_filled:
                    continue
                kind = "frontier-statement-green"
                message = "tracked proof-frontier node is displayed as statement-complete"
            else:
                kind = "current-interface-green"
                message = "corrected Lean-only interface is displayed as statement-complete"
            findings.append(
                GraphFinding(
                    label=label,
                    kind=kind,
                    message=message,
                    color=node.color,
                    fillcolor=node.fillcolor,
                    style=node.style,
                )
            )

    for label in sorted(PROOF_FILLED_LABELS):
        node = nodes.get(label)
        if node is None:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="missing-required-node",
                    message="required proved source node is missing from the graph",
                )
            )
        elif not node.is_proof_filled:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="proved-node-not-proof-filled",
                    message="proved source node is not displayed as proof-complete",
                    color=node.color,
                    fillcolor=node.fillcolor,
                    style=node.style,
                )
            )

    for label in sorted(GREEN_BORDER_LABELS):
        node = nodes.get(label)
        if node is None:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="missing-required-node",
                    message="required formalized node is missing from the graph",
                )
            )
        elif not node.has_green_border:
            findings.append(
                GraphFinding(
                    label=label,
                    kind="formalized-node-not-green",
                    message="formalized node is not displayed with a green statement border",
                    color=node.color,
                    fillcolor=node.fillcolor,
                    style=node.style,
                )
            )

    return tuple(findings)


def run_audit(graph_path: Path) -> GraphAuditResult:
    """Run the graph-status audit on one generated graph HTML file."""
    text = graph_path.read_text(encoding="utf-8", errors="replace")
    nodes = parse_nodes_from_dot(extract_dot(text))
    return GraphAuditResult(
        graph_path=str(graph_path),
        scanned_nodes=len(nodes),
        findings=audit_nodes(nodes),
    )


def render_text(result: GraphAuditResult) -> str:
    """Render a human-readable dependency-graph audit report."""
    lines = [
        "Dependency graph status audit",
        f"graph: {result.graph_path}",
        f"scanned nodes: {result.scanned_nodes}",
        f"findings: {len(result.findings)}",
    ]
    for finding in result.findings:
        lines.append("")
        lines.append(f"{finding.label}: {finding.kind}")
        lines.append(f"  {finding.message}")
        status = ", ".join(
            part for part in (
                f"color={finding.color}" if finding.color else "",
                f"fillcolor={finding.fillcolor}" if finding.fillcolor else "",
                f"style={finding.style}" if finding.style else "",
            )
            if part
        )
        if status:
            lines.append(f"  graph status: {status}")
    return "\n".join(lines)


def render_json(result: GraphAuditResult) -> str:
    """Render the audit result as JSON."""
    return json.dumps(asdict(result), indent=2, sort_keys=True)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--graph",
        type=Path,
        default=Path("blueprint/web/dep_graph_document.html"),
        help="path to the generated dep_graph_document.html file",
    )
    parser.add_argument("--json", action="store_true", help="print JSON output")
    parser.add_argument("--ci", action="store_true", help="fail when findings exist")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""
    args = parse_args(sys.argv[1:] if argv is None else argv)
    result = run_audit(args.graph.resolve())
    if args.json:
        print(render_json(result))
    else:
        print(render_text(result))
    return 1 if args.ci and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
