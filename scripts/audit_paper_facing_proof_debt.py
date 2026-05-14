#!/usr/bin/env python3
r"""Audit paper-facing blueprint statements for proof-debt inputs.

The faithful-formalization policy allows auxiliary bridge or repair lemmas,
but a Lean declaration advertised as a paper theorem, lemma, proposition, or
corollary should not acquire an additional public hypothesis whose purpose is
to supply an unproved part of the proof.  This script is a conservative
review aid for that boundary:

* read theorem-like ``\lean{...}`` references from the active blueprint;
* resolve those references to public Lean declarations under ``MIPStarRE/``;
* inspect only the public input portion of the declaration header after the
  declaration name and before the result type;
* report occurrences of blocking proof-debt vocabulary such as
  ``BridgeHypotheses``, ``Residual``, ``RepairInput``, ``Package``,
  ``Bundle``, ``Conditional``, ``Producer``, ``Obligation``, an ``Input``
  bundle, a wrapper, an ``Unfaithful`` marker type, or a generic
  ``Hypotheses`` / ``Assumptions`` bundle;
* with ``--broad-vocabulary``, also report the wider tracker vocabulary
  ``Statement``, ``Output``, ``Conclusion``, ``Witness``, ``Data``, and
  ``Compatibility`` in public inputs.  This mode is an inventory tool while
  those broad occurrences are classified and reduced; it is deliberately not
  the default blocking gate.
* classify quoted external theorem interfaces separately in broad mode, so
  external citations from the overview are not conflated with internal proof
  obligations.
* reject paper-facing blueprint entries that point to declaration names with
  conditional proof-debt forms such as ``*_of...Obligations``,
  ``*_of...Residual``, ``*_of...Repair``, ``*_of...Bundle``,
  ``*_of...Unfaithful``, ``*_assuming...``, ``conditional...``, or
  ``Conditional...``, even when the declaration header itself has no
  suspicious public input.
* classify known faithful boundary-input packages separately, with paper
  citations, so they do not become indistinguishable from proof debt.

The audit is report-only by default.  With ``--ci`` it exits non-zero when a
finding is present, unless ``--warn-only`` is also supplied.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

from blueprint_lean_sync import (  # noqa: E402
    BlueprintEntry,
    LEAN_DECL_RE,
    LeanDecl,
    collect_blueprint_entries,
    collect_lean_decls,
    strip_lean_comments_preserve_lines,
)
from lean_header_utils import advance_depth, line_number, starts_keyword


THEOREM_LIKE_ENVS = frozenset({"theorem", "lemma", "proposition", "corollary"})

STRICT_UPPER_TOKENS = (
    "Bridge",
    "Residual",
    "Repair",
    "Package",
    "Producer",
    "Input",
    "Hypotheses",
    "Assumptions",
    "Hypothesis",
    "Assumption",
    "Obligation",
    "Obligations",
    "Wrapper",
    "Bundle",
    "Conditional",
    "Unfaithful",
    "CompletionTransport",
)

BROAD_EXTRA_UPPER_TOKENS = (
    "Statement",
    "Output",
    "Conclusion",
    "Witness",
    "Data",
    "Compatibility",
)

STRICT_LOWER_TOKENS = (
    "bridge",
    "residual",
    "repair",
    "package",
    "producer",
    "input",
    "hypotheses",
    "assumptions",
    "hypothesis",
    "assumption",
    "obligation",
    "obligations",
    "wrapper",
    "bundle",
    "conditional",
    "unfaithful",
    "completionTransport",
)

BROAD_EXTRA_LOWER_TOKENS = (
    "statement",
    "output",
    "conclusion",
    "witness",
    "data",
    "compatibility",
)


def _debt_token_re(upper_tokens: tuple[str, ...], lower_tokens: tuple[str, ...]) -> re.Pattern[str]:
    """Build the public-input proof-debt token matcher from token lists."""

    upper_alternation = "|".join(re.escape(token) for token in upper_tokens)
    lower_alternation = "|".join(re.escape(token) for token in lower_tokens)
    return re.compile(
        r"(?<![A-Za-z0-9_'])"
        r"(?:"
        r"(?:[A-Za-z_][A-Za-z0-9_']*)?"
        r"(?:"
        + upper_alternation
        + r")"
        r"[A-Za-z0-9_']*"
        r"|"
        r"(?:h|has|mk|of)?"
        r"(?:"
        + lower_alternation
        + r")"
        r"[A-Za-z0-9_']*"
        r")"
        r"(?![A-Za-z0-9_'])"
    )


STRICT_DEBT_TOKEN_RE = _debt_token_re(STRICT_UPPER_TOKENS, STRICT_LOWER_TOKENS)
BROAD_DEBT_TOKEN_RE = _debt_token_re(
    STRICT_UPPER_TOKENS + BROAD_EXTRA_UPPER_TOKENS,
    STRICT_LOWER_TOKENS + BROAD_EXTRA_LOWER_TOKENS,
)

# The following tokens are deliberately not treated as proof-debt findings.
# Each entry is a small public structure whose fields are visible in the
# corresponding source statement, or are scalar side conditions used to make an
# implicit paper regime explicit.
#
# * CascadeHypotheses contains only the numeric regime used by the final error
#   cascade: k >= 1, m >= 1, 0 <= eps <= 1, d <= q, and q > 0.  These are not
#   bridge data.  The paper calculation at inductive_step.tex:187-234 uses the
#   unit-scale assumptions when comparing fractional powers and absorbing lower
#   powers into k^2 m^4; the blueprint states them explicitly in
#   ch10_induction.tex:545-564.
# * SliceBoundednessInput contains the boundedness item from
#   commutativity-G.tex:29-36 and ld-pasting.tex:28-35: positive witnesses Z^x,
#   the averaged residual bound, and the pointwise domination
#   Z^x >= E_u A^{u,x}_{g(u)}.  It must not contain an additional Lean-only
#   identification field; issue #1556 removed the former
#   dominationTargetAgrees bridge from this public input.
FAITHFUL_BOUNDARY_TOKENS = {
    "CascadeHypotheses": (
        "faithful encoding of the standing numeric regime for the error cascade; "
        "see blueprint/src/chapter/ch10_induction.tex:588-689 and "
        "references/ldt-paper/inductive_step.tex:187-234"
    ),
    "SliceBoundednessInput": (
        "faithful encoding of the paper boundedness hypothesis; see "
        "references/ldt-paper/commutativity-G.tex:29-36 and "
        "references/ldt-paper/ld-pasting.tex:28-35"
    ),
}

# These broad-mode findings are not internal bridge debt.  They are explicit
# interfaces for the external classical theorems quoted in the overview.  The
# corresponding blueprint entries must remain unmarked by \leanok unless the
# external theorem itself is formalized, but they should not be counted with
# internal proof obligations such as witnesses, data packages, or wrappers.
EXTERNAL_CITATION_TOKENS = {
    "RazSafraSoundnessStatement": (
        "external Raz--Safra theorem quoted in "
        "references/ldt-paper/introduction.tex:43-65; the blueprint entry is "
        "not marked as formalized"
    ),
    "PolishchukSpielmanClassicalSoundnessStatement": (
        "external Polishchuk--Spielman theorem quoted in "
        "references/ldt-paper/introduction.tex:69-92; the blueprint entry is "
        "not marked as formalized"
    ),
}

# Source-construction context is the formal counterpart of a paper passage that
# says "henceforth let ..." and then proves several local lemmas in that fixed
# context.  These tokens still appear in broad mode so reviewers can see the
# context boundary, but they are not unresolved proof-debt hypotheses.
SOURCE_CONTEXT_TOKENS = {
    "QLayerData": (
        "source construction context for the fixed rank-reduced Q family and "
        "auxiliary projectors; see "
        "references/ldt-paper/orthonormalization.tex:658-795"
    ),
    "RankReductionWitness": (
        "source construction context recording the conclusion of "
        "lem:projective-low-rank-sum; see "
        "references/ldt-paper/orthonormalization.tex:540-658"
    ),
    "QXPLayerData": (
        "source construction context for the matrix decomposition and "
        "X/XHat/P layer; see "
        "references/ldt-paper/orthonormalization.tex:775-940"
    ),
}

# Broad mode should classify mathematical interfaces, not double-count a local
# variable name whose type is already reported, for example
# ``(data : QXPLayerData Outcome ι)``.
IGNORED_BROAD_BINDER_TOKENS = frozenset({"data"})

CONDITIONAL_DECL_NAME_RE = re.compile(
    r"(?:"
    r"FromBridgeInputs"
    r"|BridgeHypotheses"
    r"|BridgeInputs"
    r"|(?:^|_)of(?:[A-Z][A-Za-z0-9_']*)?"
    r"(?:"
    r"Bridge|Obligations|Obligation|Residual|Repair|Package|Producer|Input"
    r"|Hypotheses|Hypothesis|Assumptions|Assumption"
    r"|Statement|Output|Conclusion|Witness|Wrapper|Bundle|Unfaithful"
    r"|Slackness|Dominance"
    r")"
    r"[A-Za-z0-9_']*"
    r"|(?:^|_)ofRepaired[A-Za-z0-9_']*"
    r"|(?:^|_)assuming[A-Za-z0-9_']*"
    r"|Assuming[A-Za-z0-9_']*"
    r"|(?:^|_)conditional[A-Za-z0-9_']*"
    r"|Conditional[A-Za-z0-9_']*"
    r")"
)

@dataclass(frozen=True)
class DebtFinding:
    """One proof-debt token in a paper-facing Lean declaration header."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str
    token_line: int
    header_excerpt: str


@dataclass(frozen=True)
class ClassifiedFinding:
    """One detected token with a mathematical classification and citation."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str
    token_line: int
    header_excerpt: str
    reason: str


@dataclass(frozen=True)
class ConditionalDeclarationNameFinding:
    """One conditional declaration name used for a paper-facing blueprint entry."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str


@dataclass(frozen=True)
class AuditResult:
    """Summary of the paper-facing proof-debt audit."""

    scanned_refs: int
    missing_refs: tuple[str, ...]
    findings: tuple[DebtFinding, ...]
    conditional_decl_findings: tuple[ConditionalDeclarationNameFinding, ...]
    faithful_boundary_findings: tuple[ClassifiedFinding, ...]
    external_citation_findings: tuple[ClassifiedFinding, ...]
    source_context_findings: tuple[ClassifiedFinding, ...]

    @property
    def ok(self) -> bool:
        return (
            not self.findings
            and not self.conditional_decl_findings
            and not self.missing_refs
        )


def paper_facing_entries(blueprint_src: Path) -> list[BlueprintEntry]:
    """Return theorem-like blueprint entries that carry a Lean reference."""
    return [
        entry
        for entry in collect_blueprint_entries(blueprint_src)
        if entry.env_type in THEOREM_LIKE_ENVS
    ]


def _header_after_decl_name(text: str) -> str:
    """Remove the declaration keyword and name from a Lean declaration header."""
    match = LEAN_DECL_RE.match(text)
    if not match:
        return text
    return text[match.end() :]


def _public_header_after_name(source: str, decl: LeanDecl) -> tuple[str, int]:
    """Return the public header, excluding the declaration name.

    The returned line number is the line of the first character in the returned
    text, so token line numbers can be computed without reparsing the file.
    """
    stripped_lines = strip_lean_comments_preserve_lines(source)
    candidate = "\n".join(stripped_lines[decl.line - 1 : decl.end_line])

    stack: list[str] = []
    end = len(candidate)
    i = 0
    while i < len(candidate):
        if candidate.startswith(":=", i) and not stack:
            end = i
            break
        if starts_keyword(candidate, i, "where") and not stack:
            end = i
            break
        advance_depth(candidate[i], stack)
        i += 1

    header = candidate[:end]
    after_name = _header_after_decl_name(header)
    skipped_lines = header[: len(header) - len(after_name)].count("\n")
    return after_name, decl.line + skipped_lines


def _public_inputs_before_result_type(header_after_name: str) -> str:
    """Return the public input part before the declaration result type.

    The audit is meant to detect extra hypotheses or input data on
    paper-facing declarations.  Mathematical result types may legitimately
    mention words such as ``Residual``; those are handled by statement review,
    not by this input-debt scanner.
    """
    stack: list[str] = []
    for i, char in enumerate(header_after_name):
        if char == ":" and not stack:
            return header_after_name[:i]
        advance_depth(char, stack)
    return header_after_name


def _line_excerpt(text: str, one_based_line: int) -> str:
    lines = text.splitlines()
    if one_based_line < 1 or one_based_line > len(lines):
        return ""
    return " ".join(lines[one_based_line - 1].strip().split())


def _faithful_boundary_reason(token: str) -> str | None:
    """Return the paper citation when ``token`` is a faithful boundary input."""
    return FAITHFUL_BOUNDARY_TOKENS.get(token)


def _external_citation_reason(token: str) -> str | None:
    """Return the citation when ``token`` names an external theorem interface."""
    return EXTERNAL_CITATION_TOKENS.get(token)


def _source_context_reason(token: str) -> str | None:
    """Return the citation when ``token`` names fixed source construction context."""
    return SOURCE_CONTEXT_TOKENS.get(token)


def _is_ignored_broad_binder_token(token: str, *, broad_vocabulary: bool) -> bool:
    """Return whether ``token`` is only a broad-mode local binder name."""
    return broad_vocabulary and token in IGNORED_BROAD_BINDER_TOKENS


def _classified_finding(
    entry: BlueprintEntry,
    decl: LeanDecl,
    *,
    token: str,
    token_line: int,
    header_excerpt: str,
    reason: str,
) -> ClassifiedFinding:
    """Return a classified finding for a detected public-input token."""
    return ClassifiedFinding(
        blueprint_file=entry.file,
        blueprint_line=entry.line,
        env_type=entry.env_type,
        label=entry.label,
        lean_decl=entry.lean_decl,
        lean_file=decl.file,
        lean_line=decl.line,
        token=token,
        token_line=token_line,
        header_excerpt=header_excerpt,
        reason=reason,
    )


def _conditional_decl_name_finding(
    entry: BlueprintEntry,
    decl: LeanDecl,
) -> ConditionalDeclarationNameFinding | None:
    """Return a finding when a paper-facing entry references a conditional name."""
    basename = entry.lean_decl.rsplit(".", 1)[-1]
    match = CONDITIONAL_DECL_NAME_RE.search(basename)
    if match is None:
        return None
    return ConditionalDeclarationNameFinding(
        blueprint_file=entry.file,
        blueprint_line=entry.line,
        env_type=entry.env_type,
        label=entry.label,
        lean_decl=entry.lean_decl,
        lean_file=decl.file,
        lean_line=decl.line,
        token=match.group(0),
    )


def _findings_for_entry(
    root: Path,
    entry: BlueprintEntry,
    decl: LeanDecl,
    *,
    broad_vocabulary: bool,
) -> tuple[
    list[DebtFinding],
    list[ClassifiedFinding],
    list[ClassifiedFinding],
    list[ClassifiedFinding],
]:
    lean_path = root / decl.file
    source = lean_path.read_text(encoding="utf-8", errors="replace")
    header, header_start_line = _public_header_after_name(source, decl)
    public_inputs = _public_inputs_before_result_type(header)

    findings: list[DebtFinding] = []
    faithful_boundary_findings: list[ClassifiedFinding] = []
    external_citation_findings: list[ClassifiedFinding] = []
    source_context_findings: list[ClassifiedFinding] = []
    debt_token_re = BROAD_DEBT_TOKEN_RE if broad_vocabulary else STRICT_DEBT_TOKEN_RE
    for match in debt_token_re.finditer(public_inputs):
        token = match.group(0)
        if _is_ignored_broad_binder_token(token, broad_vocabulary=broad_vocabulary):
            continue
        token_line = header_start_line + line_number(public_inputs, match.start()) - 1
        local_line = line_number(public_inputs, match.start())
        header_excerpt = _line_excerpt(public_inputs, local_line)
        reason = _faithful_boundary_reason(token)
        if reason is not None:
            faithful_boundary_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=reason,
                )
            )
            continue
        source_context_reason = _source_context_reason(token)
        if broad_vocabulary and source_context_reason is not None:
            source_context_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=source_context_reason,
                )
            )
            continue
        external_reason = _external_citation_reason(token)
        if broad_vocabulary and external_reason is not None:
            external_citation_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=external_reason,
                )
            )
            continue
        findings.append(
            DebtFinding(
                blueprint_file=entry.file,
                blueprint_line=entry.line,
                env_type=entry.env_type,
                label=entry.label,
                lean_decl=entry.lean_decl,
                lean_file=decl.file,
                lean_line=decl.line,
                token=token,
                token_line=token_line,
                header_excerpt=header_excerpt,
            )
        )
    return (
        findings,
        faithful_boundary_findings,
        external_citation_findings,
        source_context_findings,
    )


def run_audit(root: Path, *, broad_vocabulary: bool = False) -> AuditResult:
    """Run the paper-facing proof-debt audit for ``root``."""
    root = root.resolve()
    blueprint_src = root / "blueprint" / "src"
    lean_root = root / "MIPStarRE"

    entries = paper_facing_entries(blueprint_src)
    decls = collect_lean_decls(lean_root)

    missing: list[str] = []
    findings: list[DebtFinding] = []
    conditional_decl_findings: list[ConditionalDeclarationNameFinding] = []
    faithful_boundary_findings: list[ClassifiedFinding] = []
    external_citation_findings: list[ClassifiedFinding] = []
    source_context_findings: list[ClassifiedFinding] = []
    for entry in entries:
        decl = decls.get(entry.lean_decl)
        if decl is None:
            missing.append(entry.lean_decl)
            continue
        if conditional_finding := _conditional_decl_name_finding(entry, decl):
            conditional_decl_findings.append(conditional_finding)
        entry_findings, entry_faithful, entry_external, entry_source_context = _findings_for_entry(
            root,
            entry,
            decl,
            broad_vocabulary=broad_vocabulary,
        )
        findings.extend(entry_findings)
        faithful_boundary_findings.extend(entry_faithful)
        external_citation_findings.extend(entry_external)
        source_context_findings.extend(entry_source_context)

    return AuditResult(
        scanned_refs=len(entries),
        missing_refs=tuple(sorted(set(missing))),
        findings=tuple(findings),
        conditional_decl_findings=tuple(conditional_decl_findings),
        faithful_boundary_findings=tuple(faithful_boundary_findings),
        external_citation_findings=tuple(external_citation_findings),
        source_context_findings=tuple(source_context_findings),
    )


def _print_classified_findings(title: str, findings: tuple[ClassifiedFinding, ...]) -> None:
    """Print findings that carry a mathematical classification."""
    print(f"{title}: {len(findings)}")
    for finding in findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.token_line}: "
            f"{finding.lean_decl} contains {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )
        print(f"    {finding.reason}")
        if finding.header_excerpt:
            print(f"    {finding.header_excerpt}")


def print_text_report(result: AuditResult) -> None:
    """Print a human-readable audit report."""
    print(f"Scanned paper-facing Lean references: {result.scanned_refs}")
    if result.missing_refs:
        print(f"Missing Lean references: {len(result.missing_refs)}")
        for decl in result.missing_refs:
            print(f"  - {decl}")
    else:
        print("Missing Lean references: 0")

    print(f"Proof-debt header findings: {len(result.findings)}")
    for finding in result.findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.token_line}: "
            f"{finding.lean_decl} contains {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )
        if finding.header_excerpt:
            print(f"    {finding.header_excerpt}")

    print(f"Conditional declaration-name findings: {len(result.conditional_decl_findings)}")
    for finding in result.conditional_decl_findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.lean_line}: "
            f"{finding.lean_decl} has conditional name token {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )

    _print_classified_findings(
        "Faithful boundary input findings",
        result.faithful_boundary_findings,
    )
    _print_classified_findings(
        "External citation input findings",
        result.external_citation_findings,
    )
    _print_classified_findings(
        "Source construction context findings",
        result.source_context_findings,
    )


def _json_default(value: object) -> object:
    if isinstance(value, tuple):
        return list(value)
    raise TypeError(f"Object of type {type(value).__name__} is not JSON serializable")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root")
    parser.add_argument("--json", action="store_true", help="print JSON instead of text")
    parser.add_argument("--ci", action="store_true", help="exit non-zero on findings")
    parser.add_argument(
        "--broad-vocabulary",
        action="store_true",
        help=(
            "also scan broad tracker vocabulary such as Statement, Witness, "
            "Data, Output, Conclusion, and Compatibility"
        ),
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="with --ci, report findings but keep exit code 0",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    result = run_audit(args.root, broad_vocabulary=args.broad_vocabulary)

    if args.json:
        print(json.dumps(asdict(result), indent=2, sort_keys=True, default=_json_default))
    else:
        print_text_report(result)

    if args.ci and not args.warn_only and not result.ok:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
