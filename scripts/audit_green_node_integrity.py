#!/usr/bin/env python3
"""Audit green blueprint nodes for hidden obligation-style Lean links.

The script scans `\\leanok` blueprint environments.  It reports all declarations
whose names contain bridge, obligation, residual, repair, input, producer, or
hypothesis terminology, and it fails when a source-like node has an unexpected
warning declaration.  It also inspects the public Lean declaration header for
source-like nodes, so that a theorem with a neutral name but an obligation-shaped
hypothesis is not silently treated as genuinely green.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


WARNING_TERMS = (
    "Obligation",
    "obligation",
    "Bridge",
    "bridge",
    "Residual",
    "residual",
    "Repair",
    "repair",
    "Package",
    "package",
    "Input",
    "input",
    "Producer",
    "producer",
    "Hypotheses",
    "hypotheses",
    "Assumptions",
    "assumptions",
)

SOURCE_PREFIXES = ("thm:", "lem:", "prop:", "cor:", "clm:")

ALLOWED_SOURCE_WARNINGS = {
    (
        "lem:orthonormalization-main-lemma-formalized-envelope",
        "MIPStarRE.LDT.MakingMeasurementsProjective."
        "orthonormalizationMeasurement_of_consistency_from_projectivizationRepair",
    ),
    (
        "lem:locality-preserving-projectivization",
        "MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepair",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
}

ALLOWED_SOURCE_SIGNATURE_WARNINGS = {
    (
        "lem:comm-data-processed-g",
        "MIPStarRE.LDT.Commutativity.commDataProcessedG",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.Commutativity.gCommStability_scalar",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.Commutativity.gCommStabilityTwo_scalar",
    ),
    (
        "thm:com-main",
        "MIPStarRE.LDT.Commutativity.comMain",
    ),
    (
        "thm:ld-pasting",
        "MIPStarRE.LDT.Pasting.ldPasting",
    ),
    (
        "prop:main-induction-successor-answer-valued-pasting",
        "MIPStarRE.LDT.MainInductionStep."
        "answerLdPastingInInductionSectionOfSmallError",
    ),
    (
        "lem:ld-pasting-sub-measurement",
        "MIPStarRE.LDT.Pasting.ldPastingSubMeas",
    ),
    (
        "cor:commuting-with-G-complete",
        "MIPStarRE.LDT.Pasting.commutingWithGComplete",
    ),
    (
        "cor:commuting-with-G-incomplete",
        "MIPStarRE.LDT.Pasting.commutingWithGIncomplete",
    ),
    (
        "cor:G-hat-facts",
        "MIPStarRE.LDT.Pasting.gHatFacts",
    ),
    (
        "lem:commute-g-half-sandwich",
        "MIPStarRE.LDT.Pasting.commuteGHalfSandwich",
    ),
    (
        "lem:line-interpolation-averaging-estimates",
        "MIPStarRE.LDT.Pasting.avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError",
    ),
    (
        "lem:line-interpolation-averaging-estimates",
        "MIPStarRE.LDT.Pasting.avgOver_distinct_badMass_le_hBConsistencyError",
    ),
    (
        "lem:ld-sandwich-line-one-point",
        "MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint",
    ),
    (
        "lem:h-b-consistency",
        "MIPStarRE.LDT.Pasting.hBConsistency",
    ),
    (
        "cor:h-a-consistency",
        "MIPStarRE.LDT.Pasting.hAConsistency_submeas",
    ),
    (
        "lem:over-all-outcomes",
        "MIPStarRE.LDT.Pasting.overAllOutcomes",
    ),
    (
        "lem:from-H-to-G",
        "MIPStarRE.LDT.Pasting.fromHToG",
    ),
    (
        "cor:ld-pasting-N-completeness",
        "MIPStarRE.LDT.Pasting.ldPastingNCompleteness",
    ),
    (
        "thm:ld-pasting-in-induction-section",
        "MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection",
    ),
    (
        "thm:sigma-bound-main-formal",
        "MIPStarRE.LDT.Test.sigma_bound",
    ),
    (
        "thm:zeta-bounds-main-formal",
        "MIPStarRE.LDT.Test.zeta1_bound",
    ),
    (
        "thm:zeta-bounds-main-formal",
        "MIPStarRE.LDT.Test.zeta2_bound",
    ),
    (
        "thm:zeta-bounds-main-formal",
        "MIPStarRE.LDT.Test.zeta3_bound",
    ),
    (
        "thm:zeta-bounds-main-formal",
        "MIPStarRE.LDT.Test.zeta4_bound",
    ),
    (
        "thm:error-cascade-main-formal",
        "MIPStarRE.LDT.Test.errorCascade_le_mainFormalError",
    ),
}

ALLOWED_SOURCE_UNFAITHFUL = {
    (
        "thm:main-formal",
        "MIPStarRE.LDT.Test.mainFormal_sourceStatement",
    ),
    (
        "thm:main-formal-current-interface",
        "MIPStarRE.LDT.Test.mainFormal",
    ),
}


ENV_RE = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|remark|corollary)\}"
    r"(?:\[[^\]]*\])?\s*\\label\{([^}]*)\}",
    re.MULTILINE,
)

LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.DOTALL)

EVENT_RE = re.compile(
    r"(?m)^(?:"
    r"namespace\s+([A-Za-z0-9_'.]+)\s*$"
    r"|end\b(?:\s+([A-Za-z0-9_'.]+))?\s*$"
    r"|(?:@[^\n]*\n\s*)*(?:private\s+)?(?:noncomputable\s+)?"
    r"(?:def|theorem|lemma|structure|class)\s+([A-Za-z0-9_'.]+)"
    r")"
)


def mask_lean_comments(text: str) -> str:
    """Replace Lean comments by spaces, preserving line and column positions."""
    chars = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            line_end = text.find("\n", i)
            end = len(text) if line_end == -1 else line_end
            for j in range(i, end):
                chars[j] = " "
            i = end
            continue
        if text.startswith("/-", i):
            depth += 1
            chars[i] = " "
            chars[i + 1] = " "
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            chars[i] = " "
            chars[i + 1] = " "
            i += 2
            continue
        if depth > 0 and chars[i] != "\n":
            chars[i] = " "
        i += 1
    return "".join(chars)


def lean_declarations(block: str) -> list[str]:
    """Extract comma-separated Lean declarations from all `\\lean{...}` tags."""
    declarations: list[str] = []
    for match in LEAN_RE.finditer(block):
        declarations.extend(
            declaration.strip()
            for declaration in match.group(1).split(",")
            if declaration.strip()
        )
    return declarations


def mask_tex_comments(text: str) -> str:
    """Replace TeX line comments by spaces, preserving line structure."""
    lines: list[str] = []
    for line in text.splitlines(keepends=True):
        comment = line.find("%")
        if comment == -1:
            lines.append(line)
            continue
        newline = "\n" if line.endswith("\n") else ""
        body = line[:-1] if newline else line
        lines.append(body[:comment] + " " * (len(body) - comment) + newline)
    return "".join(lines)


def warning_declarations(declarations: list[str]) -> list[str]:
    """Return declarations containing one of the warning terms."""
    return [
        declaration
        for declaration in declarations
        if any(term in declaration for term in WARNING_TERMS)
    ]


def declaration_headers(root: Path) -> dict[str, list[tuple[Path, str]]]:
    """Index Lean declaration headers by qualified and unqualified names."""
    headers: dict[str, list[tuple[Path, str]]] = {}
    for path in sorted((root / "MIPStarRE").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        scan_text = mask_lean_comments(text)
        namespace_stack: list[str] = []
        for match in EVENT_RE.finditer(scan_text):
            namespace_name, end_name, declaration_name = match.groups()
            if namespace_name is not None:
                namespace_stack.extend(namespace_name.split("."))
                continue
            if end_name is not None:
                components = end_name.split(".")
                if namespace_stack[-len(components) :] == components:
                    del namespace_stack[-len(components) :]
                elif namespace_stack:
                    namespace_stack.pop()
                continue
            if declaration_name is None:
                # Bare `end` commonly closes a `section`; all namespace closures
                # in the current codebase are named.  Avoid corrupting the
                # namespace stack when the closed block is not a namespace.
                continue
            header_start = match.start()
            assignment = text.find(":=", match.end())
            where = text.find(" where", match.end(), assignment if assignment != -1 else len(text))
            stops = [stop for stop in (assignment, where) if stop != -1]
            header_end = min(stops) if stops else text.find("\n\n", match.end())
            if header_end == -1:
                header_end = min(len(text), header_start + 2000)
            header = text[header_start:header_end]
            qualified_name = ".".join(namespace_stack + [declaration_name])
            headers.setdefault(qualified_name, []).append((path, header))
            headers.setdefault(declaration_name, []).append((path, header))
    return headers


def preceding_docstring(text: str, start: int) -> str | None:
    """Return the docstring immediately preceding `start`, if there is one."""
    prefix = text[:start]
    stripped = prefix.rstrip()
    if not stripped.endswith("-/"):
        return None
    doc_start = matching_comment_start(stripped, len(stripped) - 2)
    if doc_start == -1:
        return None
    if not stripped.startswith("/--", doc_start):
        return None
    return stripped[doc_start:]


def matching_comment_start(text: str, close_start: int) -> int:
    """Return the opening `/-` matching the close marker at `close_start`."""
    depth = 1
    i = close_start - 1
    while i >= 1:
        token_start = i - 1
        if text.startswith("-/", token_start):
            depth += 1
            i -= 2
            continue
        if text.startswith("/-", token_start):
            depth -= 1
            if depth == 0:
                return token_start
            i -= 2
            continue
        i -= 1
    return -1


def declaration_docstrings(root: Path) -> dict[str, list[tuple[Path, str]]]:
    """Index immediate Lean docstrings by qualified and unqualified names."""
    docstrings: dict[str, list[tuple[Path, str]]] = {}
    for path in sorted((root / "MIPStarRE").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        scan_text = mask_lean_comments(text)
        namespace_stack: list[str] = []
        for match in EVENT_RE.finditer(scan_text):
            namespace_name, end_name, declaration_name = match.groups()
            if namespace_name is not None:
                namespace_stack.extend(namespace_name.split("."))
                continue
            if end_name is not None:
                components = end_name.split(".")
                if namespace_stack[-len(components) :] == components:
                    del namespace_stack[-len(components) :]
                elif namespace_stack:
                    namespace_stack.pop()
                continue
            if declaration_name is None:
                continue
            docstring = preceding_docstring(text, match.start())
            if docstring is None:
                continue
            qualified_name = ".".join(namespace_stack + [declaration_name])
            docstrings.setdefault(qualified_name, []).append((path, docstring))
            docstrings.setdefault(declaration_name, []).append((path, docstring))
    return docstrings


def header_warning_terms(declaration: str, headers: dict[str, list[tuple[Path, str]]]) -> list[str]:
    """Return warning terms appearing in the public header of a Lean declaration."""
    short_name = declaration.rsplit(".", 1)[-1]
    found: set[str] = set()
    declaration_headers = headers.get(declaration) or headers.get(short_name, [])
    for _path, header in declaration_headers:
        signature = header.split(short_name, 1)[1] if short_name in header else header
        found.update(term for term in WARNING_TERMS if term in signature)
    return sorted(found)


def has_unfaithful_marker(
    declaration: str, docstrings: dict[str, list[tuple[Path, str]]]
) -> bool:
    """Return true when the declaration's immediate docstring marks it unfaithful."""
    short_name = declaration.rsplit(".", 1)[-1]
    declaration_docstrings = docstrings.get(declaration) or docstrings.get(short_name, [])
    return any("**Unfaithful:**" in docstring for _path, docstring in declaration_docstrings)


def iter_leanok_blocks(chapter_dir: Path):
    for path in sorted(chapter_dir.glob("*.tex")):
        text = path.read_text(encoding="utf-8")
        for match in ENV_RE.finditer(text):
            env, label = match.group(1), match.group(2)
            end_marker = f"\\end{{{env}}}"
            end = text.find(end_marker, match.end())
            block = mask_tex_comments(text[match.start() : end if end != -1 else match.end()])
            if "\\leanok" not in block:
                continue
            yield path, env, label, block


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--ci", action="store_true")
    args = parser.parse_args()

    chapter_dir = args.root / "blueprint" / "src" / "chapter"
    if not chapter_dir.is_dir():
        print(f"error: no blueprint chapter directory at {chapter_dir}", file=sys.stderr)
        return 2

    leanok_count = 0
    source_count = 0
    aux_count = 0
    allowed_source: list[tuple[Path, str, str]] = []
    unexpected_source: list[tuple[Path, str, str]] = []
    allowed_signature: list[tuple[Path, str, str, list[str]]] = []
    unexpected_signature: list[tuple[Path, str, str, list[str]]] = []
    allowed_unfaithful: list[tuple[Path, str, str]] = []
    unexpected_unfaithful: list[tuple[Path, str, str]] = []
    aux_unfaithful: list[tuple[Path, str, str]] = []
    aux_warnings: list[tuple[Path, str, str]] = []
    source_warning_labels: set[str] = set()
    headers = declaration_headers(args.root)
    docstrings = declaration_docstrings(args.root)

    for path, _env, label, block in iter_leanok_blocks(chapter_dir):
        leanok_count += 1
        source_like = label.startswith(SOURCE_PREFIXES)
        if source_like:
            source_count += 1
        else:
            aux_count += 1

        for declaration in warning_declarations(lean_declarations(block)):
            row = (path, label, declaration)
            if source_like:
                source_warning_labels.add(label)
                if (label, declaration) in ALLOWED_SOURCE_WARNINGS:
                    allowed_source.append(row)
                else:
                    unexpected_source.append(row)
            else:
                aux_warnings.append(row)

        if source_like:
            for declaration in lean_declarations(block):
                terms = header_warning_terms(declaration, headers)
                if not terms:
                    continue
                source_warning_labels.add(label)
                row_with_terms = (path, label, declaration, terms)
                if (label, declaration) in ALLOWED_SOURCE_SIGNATURE_WARNINGS:
                    allowed_signature.append(row_with_terms)
                else:
                    unexpected_signature.append(row_with_terms)

        for declaration in lean_declarations(block):
            if not has_unfaithful_marker(declaration, docstrings):
                continue
            row = (path, label, declaration)
            if source_like:
                source_warning_labels.add(label)
                if (label, declaration) in ALLOWED_SOURCE_UNFAITHFUL:
                    allowed_unfaithful.append(row)
                else:
                    unexpected_unfaithful.append(row)
            else:
                aux_unfaithful.append(row)

    print(f"leanok environments: {leanok_count}")
    print(f"source-like labels: {source_count}")
    print(f"definition or remark labels: {aux_count}")
    print(
        "source-like labels without warning terms or unfaithful markers: "
        f"{source_count - len(source_warning_labels)}"
    )
    print(
        "source-like labels with warning terms or unfaithful markers: "
        f"{len(source_warning_labels)}"
    )
    print(f"allowed source-like warning links: {len(allowed_source)}")
    print(f"allowed source-like signature warnings: {len(allowed_signature)}")
    print(f"allowed source-like unfaithful markers: {len(allowed_unfaithful)}")
    print(f"auxiliary unfaithful markers: {len(aux_unfaithful)}")
    print(f"auxiliary warning links: {len(aux_warnings)}")

    if aux_warnings:
        print("auxiliary warning links:")
        for path, label, declaration in aux_warnings:
            print(f"- {path}:{label}: {declaration}")

    if allowed_unfaithful:
        print("allowed source-like unfaithful markers:")
        for path, label, declaration in allowed_unfaithful:
            print(f"- {path}:{label}: {declaration}")

    if aux_unfaithful:
        print("auxiliary unfaithful markers:")
        for path, label, declaration in aux_unfaithful:
            print(f"- {path}:{label}: {declaration}")

    if unexpected_source:
        print("unexpected source-like warning links:")
        for path, label, declaration in unexpected_source:
            print(f"- {path}:{label}: {declaration}")
        return 1 if args.ci else 0

    if unexpected_signature:
        print("unexpected source-like signature warnings:")
        for path, label, declaration, terms in unexpected_signature:
            print(f"- {path}:{label}: {declaration} ({', '.join(terms)})")
        return 1 if args.ci else 0

    if unexpected_unfaithful:
        print("unexpected source-like unfaithful markers:")
        for path, label, declaration in unexpected_unfaithful:
            print(f"- {path}:{label}: {declaration}")
        return 1 if args.ci else 0

    print(
        "OK: no unexpected warning links or unfaithful markers in green "
        "source-like blueprint nodes."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
