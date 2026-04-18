#!/usr/bin/env python3
r"""
Blueprint ↔ Lean code synchronisation checker.

Parses the blueprint .tex files for \lean{DeclName} and \leanok annotations,
then greps the Lean source tree for matching declarations.  Reports:

  1. Blueprint references whose Lean declaration cannot be found.
  2. \leanok tags on items whose declaration is missing from the Lean source.
  3. lean_decls entries that don't appear in any .tex file (stale entries).
  4. \lean{} refs that are not listed in lean_decls (missing entries).
  5. Summary statistics (formalization progress per chapter).

Exit code 0  → everything in sync (or --ci not passed).
Exit code 1  → mismatches found AND --ci flag is active.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|class|structure|inductive|axiom|opaque)\s+"
    r"([\w'+]+(?:\.[\w'+]+)*)"
    r"(?:\.\{[^}]+\})?",
    re.MULTILINE,
)
_TRACKED_REVERSE_DECL_KINDS = {"def", "theorem", "lemma"}
_DIFF_HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")

_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)", re.MULTILINE)
_SECTION_OPEN_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|local)\s+)*section(?:\s+([\w.]+))?",
    re.MULTILINE,
)
_NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\s+([\w.]+)", re.MULTILINE)
_BARE_END_RE = re.compile(r"^\s*end\s*$", re.MULTILINE)

_TEX_LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
_TEX_LEANOK_RE = re.compile(r"\\leanok")
_TEX_ENV_BEGIN_RE = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
    r"(?:\[.*?\])?"
    r"(?:\\label\{([^}]+)\})?"
)
_TEX_ENV_END_RE = re.compile(
    r"\\end\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
)
_TEX_PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
_TEX_PROOF_END_RE = re.compile(r"\\end\{proof\}")


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class BlueprintEntry:
    """A single blueprint environment that references a Lean declaration."""
    file: str
    line: int
    env_type: str          # definition, theorem, lemma, …
    label: str | None
    lean_decl: str         # the \lean{X} name
    has_leanok: bool       # whether \leanok appears on the statement
    proof_has_leanok: bool  # whether the proof block has \leanok


@dataclass
class LeanDecl:
    """A Lean declaration found in the source tree."""
    file: str
    line: int
    fqn: str  # fully-qualified name including namespace
    kind: str
    short_name: str
    end_line: int


@dataclass
class OrphanLeanok:
    """A \\leanok tag that appears before any matching \\lean{} tag."""
    file: str
    line: int
    context: str


@dataclass
class SyncReport:
    """Aggregated sync report."""
    blueprint_entries: list[BlueprintEntry] = field(default_factory=list)
    lean_decls: dict[str, LeanDecl] = field(default_factory=dict)
    # Problems
    missing_in_lean: list[BlueprintEntry] = field(default_factory=list)
    leanok_but_missing: list[BlueprintEntry] = field(default_factory=list)
    stale_lean_decls: list[str] = field(default_factory=list)
    missing_from_lean_decls_file: list[str] = field(default_factory=list)
    orphan_leanok_tags: list[OrphanLeanok] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not (
            self.missing_in_lean
            or self.leanok_but_missing
            or self.stale_lean_decls
            or self.missing_from_lean_decls_file
        )


@dataclass
class ProofFrame:
    """Track one open proof block and the blueprint entries it should credit."""

    attach_entry_start: int | None
    attach_entry_end: int | None
    attach_label: str | None
    has_leanok: bool = False


def _set_proof_has_leanok(entries: list[BlueprintEntry], start: int, end: int) -> None:
    """Mark a contiguous range of blueprint entries as proof-formalized."""

    for idx in range(start, end):
        e = entries[idx]
        entries[idx] = BlueprintEntry(
            file=e.file,
            line=e.line,
            env_type=e.env_type,
            label=e.label,
            lean_decl=e.lean_decl,
            has_leanok=e.has_leanok,
            proof_has_leanok=True,
        )


# ---------------------------------------------------------------------------
# Parse Lean source tree
# ---------------------------------------------------------------------------

def collect_file_lean_decls(lean_file: Path, lean_root: Path) -> list[LeanDecl]:
    """Parse one Lean file and return its declarations with approximate spans."""
    text = lean_file.read_text(errors="replace")
    lines = text.splitlines()
    rel = str(lean_file.relative_to(lean_root.parent))

    # Track namespace and section stacks separately, plus a combined
    # open-order stack to resolve bare `end` statements correctly.
    ns_stack: list[str] = []
    section_stack: list[str] = []
    # Each entry is ("ns", name) or ("sec", name) in order of opening.
    scope_order: list[tuple[str, str]] = []
    decls: list[LeanDecl] = []

    for i, line in enumerate(lines, 1):
        m = _NAMESPACE_OPEN_RE.match(line)
        if m:
            ns_stack.append(m.group(1))
            scope_order.append(("ns", m.group(1)))
            continue

        m = _SECTION_OPEN_RE.match(line)
        if m:
            name = m.group(1) or ""
            section_stack.append(name)
            scope_order.append(("sec", name))
            continue

        # Bare `end` (no name) pops the most recently opened scope,
        # whether it was a section or namespace.
        if _BARE_END_RE.match(line):
            if scope_order:
                kind, name = scope_order.pop()
                if kind == "sec" and section_stack:
                    section_stack.pop()
                elif kind == "ns" and ns_stack:
                    ns_stack.pop()
            continue

        m = _NAMESPACE_CLOSE_RE.match(line)
        if m:
            closed = m.group(1)
            # Use scope_order to determine which scope to close when
            # both a section and namespace share the same name.
            # Search scope_order from most recent to find the matching entry.
            found_kind = None
            for j in range(len(scope_order) - 1, -1, -1):
                if scope_order[j][1] == closed:
                    found_kind = scope_order[j][0]
                    scope_order.pop(j)
                    break

            if found_kind == "sec" and closed in section_stack:
                # Remove the last occurrence of `closed` from section_stack
                for j in range(len(section_stack) - 1, -1, -1):
                    if section_stack[j] == closed:
                        section_stack.pop(j)
                        break
            elif found_kind == "ns" and closed in ns_stack:
                if ns_stack and ns_stack[-1] == closed:
                    ns_stack.pop()
                else:
                    # Non-top namespace: slice and clean up scope_order
                    for j in range(len(ns_stack) - 1, -1, -1):
                        if ns_stack[j] == closed:
                            removed = set(ns_stack[j:])
                            ns_stack = ns_stack[:j]
                            scope_order = [
                                e for e in scope_order
                                if not (e[0] == "ns" and e[1] in removed)
                            ]
                            break
            elif found_kind is None:
                # Fallback: no scope_order entry found, try ns_stack directly
                if ns_stack and ns_stack[-1] == closed:
                    ns_stack.pop()
                elif section_stack and section_stack[-1] == closed:
                    section_stack.pop()
            continue

        m = _LEAN_DECL_RE.match(line)
        if m:
            kind = m.group(1)
            short_name = m.group(2)
            prefix = ".".join(ns_stack) + "." if ns_stack else ""
            fqn = prefix + short_name
            decls.append(
                LeanDecl(
                    file=rel,
                    line=i,
                    fqn=fqn,
                    kind=kind,
                    short_name=short_name,
                    end_line=len(lines),
                )
            )

    for idx, decl in enumerate(decls):
        if idx + 1 < len(decls):
            decl.end_line = decls[idx + 1].line - 1

    return decls


def collect_lean_decls(lean_root: Path) -> dict[str, LeanDecl]:
    """Walk all .lean files and return {fqn: LeanDecl}."""
    decls: dict[str, LeanDecl] = {}

    for lean_file in sorted(lean_root.rglob("*.lean")):
        for decl in collect_file_lean_decls(lean_file, lean_root):
            decls[decl.fqn] = decl
            # Also store without namespace prefix if the name already contains
            # dots (e.g. `Foo.bar` at top level), so both spellings match.
            if "." in decl.short_name and decl.fqn != decl.short_name:
                decls[decl.short_name] = decl

    return decls


# ---------------------------------------------------------------------------
# Parse blueprint .tex files
# ---------------------------------------------------------------------------

def collect_blueprint_entries(blueprint_src: Path) -> list[BlueprintEntry]:
    """Parse all chapter .tex files for \\lean{} and \\leanok."""
    entries: list[BlueprintEntry] = []
    chapter_dir = blueprint_src / "chapter"
    if not chapter_dir.exists():
        return entries

    for tex_file in sorted(chapter_dir.glob("*.tex")):
        text = tex_file.read_text(errors="replace")
        lines = text.splitlines()

        # State machine: track current environment and proof nesting.
        env_stack: list[dict] = []
        proof_stack: list[ProofFrame] = []
        last_env: dict | None = None  # last closed environment with \lean{} refs

        for i, line in enumerate(lines, 1):
            # Check for environment begin
            m = _TEX_ENV_BEGIN_RE.search(line)
            if m:
                env = {
                    "type": m.group(1),
                    "label": m.group(2),
                    "file": str(tex_file.relative_to(blueprint_src.parent)),
                    "line": i,
                    "lean_decls": [],
                    "has_leanok": bool(_TEX_LEANOK_RE.search(line)),
                }
                env_stack.append(env)
                # Check rest of line for \lean{} and \leanok
                for lm in _TEX_LEAN_RE.finditer(line):
                    for decl in lm.group(1).split(","):
                        decl = decl.strip()
                        if decl:
                            env["lean_decls"].append(decl)
                continue

            # Check for environment end
            m = _TEX_ENV_END_RE.search(line)
            if m and env_stack:
                env = env_stack.pop()
                env_entry_start = len(entries)
                for decl in env["lean_decls"]:
                    entries.append(BlueprintEntry(
                        file=env["file"],
                        line=env["line"],
                        env_type=env["type"],
                        label=env["label"],
                        lean_decl=decl,
                        has_leanok=env["has_leanok"],
                        proof_has_leanok=False,
                    ))
                env["_entry_start"] = env_entry_start
                env["_entry_end"] = len(entries)
                # Only track as last_env if it produced lean entries, so an
                # intervening remark without \lean{} doesn't steal the proof.
                if env_entry_start < len(entries):
                    last_env = env
                continue

            # Proof begin
            m = _TEX_PROOF_BEGIN_RE.search(line)
            if m:
                # Record the environment being proved at proof-open time so an
                # inner theorem/lemma proof cannot steal the outer attribution.
                proof_stack.append(
                    ProofFrame(
                        attach_entry_start=last_env.get("_entry_start") if last_env else None,
                        attach_entry_end=last_env.get("_entry_end") if last_env else None,
                        attach_label=last_env.get("label") if last_env else None,
                        has_leanok=bool(_TEX_LEANOK_RE.search(line)),
                    )
                )
                continue

            # Inside an environment: collect \lean{} and statement-level
            # \leanok before proof-level handling so nested lemma/theorem tags
            # do not leak to the surrounding proof.
            if env_stack:
                for lm in _TEX_LEAN_RE.finditer(line):
                    for decl in lm.group(1).split(","):
                        decl = decl.strip()
                        if decl:
                            env_stack[-1]["lean_decls"].append(decl)
                if _TEX_LEANOK_RE.search(line):
                    env_stack[-1]["has_leanok"] = True
                    continue

            # Inside a proof block: detect \leanok on its own line
            if proof_stack and _TEX_LEANOK_RE.search(line):
                proof_stack[-1].has_leanok = True
                continue

            # Proof end
            m = _TEX_PROOF_END_RE.search(line)
            if m and proof_stack:
                current_proof = proof_stack.pop()
                # Attach proof leanok to the environment that was current when
                # this proof opened, not whichever one closed most recently.
                if (
                    current_proof.has_leanok
                    and current_proof.attach_entry_start is not None
                    and current_proof.attach_entry_end is not None
                ):
                    _set_proof_has_leanok(
                        entries,
                        current_proof.attach_entry_start,
                        current_proof.attach_entry_end,
                    )
                continue

    return entries


# ---------------------------------------------------------------------------
# Orphan \leanok heuristics
# ---------------------------------------------------------------------------


def find_orphan_leanok_tags(blueprint_src: Path) -> list[OrphanLeanok]:
    """Heuristically flag ``\\leanok`` tags that appear before any ``\\lean{}`` tag."""
    chapter_dir = blueprint_src / "chapter"
    if not chapter_dir.exists():
        return []

    token_re = re.compile(
        r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
        r"(?:\[.*?\])?(?:\\label\{[^}]+\})?"
        r"|\\end\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
        r"|\\begin\{proof\}"
        r"|\\end\{proof\}"
        r"|\\lean\{[^}]+\}"
        r"|\\leanok\b"
    )

    orphans: list[OrphanLeanok] = []
    for tex_file in sorted(chapter_dir.glob("*.tex")):
        rel = str(tex_file.relative_to(blueprint_src.parent))
        env_stack: list[dict[str, bool]] = []
        in_proof = False
        proof_has_lean_context = False
        pending_proof_has_lean = False

        for i, line in enumerate(tex_file.read_text(errors="replace").splitlines(), 1):
            for token in token_re.finditer(line):
                text = token.group(0)
                if text.startswith("\\begin{proof}"):
                    in_proof = True
                    proof_has_lean_context = pending_proof_has_lean
                    continue
                if text.startswith("\\end{proof}"):
                    in_proof = False
                    proof_has_lean_context = False
                    pending_proof_has_lean = False
                    continue
                if text.startswith("\\begin{"):
                    env_stack.append({"has_lean": False})
                    continue
                if text.startswith("\\end{"):
                    popped_has_lean = env_stack.pop()["has_lean"] if env_stack else False
                    # Only refresh pending_proof_has_lean from envs that carried
                    # a \lean{} tag, so an intervening \begin{remark}\end{remark}
                    # between a statement and its proof cannot steal the proof.
                    if popped_has_lean:
                        pending_proof_has_lean = True
                    continue
                if text.startswith("\\lean{"):
                    if env_stack:
                        env_stack[-1]["has_lean"] = True
                    elif in_proof:
                        proof_has_lean_context = True
                    else:
                        pending_proof_has_lean = True
                    continue
                if text == "\\leanok":
                    if env_stack:
                        if not env_stack[-1]["has_lean"]:
                            orphans.append(OrphanLeanok(file=rel, line=i, context="statement"))
                    elif in_proof:
                        if not proof_has_lean_context:
                            orphans.append(OrphanLeanok(file=rel, line=i, context="proof"))
                    else:
                        orphans.append(OrphanLeanok(file=rel, line=i, context="outside"))

    return orphans


# ---------------------------------------------------------------------------
# Read lean_decls file
# ---------------------------------------------------------------------------


def read_lean_decls_file(path: Path) -> set[str]:
    if not path.exists():
        return set()
    decls = {line.strip() for line in path.read_text().splitlines() if line.strip()}
    if not decls:
        # leanblueprint web can clobber lean_decls to empty when kpsewhich is
        # missing; fall back to the committed version so the sync check still
        # works after that step.
        try:
            out = subprocess.check_output(
                ["git", "show", "HEAD:blueprint/lean_decls"],
                cwd=path.parent.parent,
                text=True,
                stderr=subprocess.DEVNULL,
            )
            decls = {l.strip() for l in out.splitlines() if l.strip()}
        except (subprocess.CalledProcessError, FileNotFoundError):
            pass
    return decls


def _git_diff_changed_lines(root: Path, rel_path: str, diff_base: str, diff_head: str) -> set[int]:
    """Return changed line numbers in the post-change file using `git diff --merge-base -U0`."""
    try:
        diff = subprocess.check_output(
            ["git", "diff", "--merge-base", "--unified=0", diff_base, diff_head, "--", rel_path],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as exc:
        raise RuntimeError(
            f"Could not diff {rel_path!r} between {diff_base} and {diff_head}"
        ) from exc

    changed_lines: set[int] = set()
    for line in diff.splitlines():
        m = _DIFF_HUNK_RE.match(line)
        if not m:
            continue
        start = int(m.group(1))
        count = int(m.group(2) or "1")
        if count == 0:
            continue
        changed_lines.update(range(start, start + count))
    return changed_lines


def _decl_blueprint_spellings(decl: LeanDecl) -> set[str]:
    names = {decl.fqn}
    if "." in decl.short_name:
        names.add(decl.short_name)
    return names


def find_changed_decls_missing_from_blueprint(
    root: Path,
    *,
    changed_files: list[str],
    diff_base: str,
    diff_head: str,
) -> list[LeanDecl]:
    """Return changed `def`/`theorem`/`lemma` declarations missing from blueprint."""
    lean_root = root / "MIPStarRE"
    blueprint_src = root / "blueprint" / "src"

    blueprint_decl_names = {
        entry.lean_decl for entry in collect_blueprint_entries(blueprint_src)
    }
    missing: list[LeanDecl] = []
    seen: set[str] = set()

    for rel_path in changed_files:
        if not rel_path.endswith(".lean"):
            continue
        abs_path = root / rel_path
        if not abs_path.is_file():
            continue
        try:
            abs_path.relative_to(lean_root)
        except ValueError:
            continue

        changed_lines = _git_diff_changed_lines(root, rel_path, diff_base, diff_head)
        if not changed_lines:
            continue

        for decl in collect_file_lean_decls(abs_path, lean_root):
            if decl.kind not in _TRACKED_REVERSE_DECL_KINDS:
                continue
            if not any(decl.line <= line <= decl.end_line for line in changed_lines):
                continue
            if _decl_blueprint_spellings(decl) & blueprint_decl_names:
                continue
            if decl.fqn in seen:
                continue
            seen.add(decl.fqn)
            missing.append(decl)

    return missing


def print_missing_blueprint_warnings(missing: list[LeanDecl]) -> None:
    """Print a warning-only report for changed declarations missing blueprint refs."""
    print()
    print("=" * 70)
    print("  CHANGED LEAN DECLARATIONS ↔ BLUEPRINT COVERAGE")
    print("=" * 70)
    print()

    if not missing:
        print("✓ No changed def/theorem/lemma declarations are missing blueprint entries.")
        print()
        return

    print(f"WARNING: Changed declarations not yet in blueprint ({len(missing)}):")
    for decl in missing:
        print(f"  - {decl.fqn}  ({decl.file}:{decl.line})")
        if os.getenv("GITHUB_ACTIONS") == "true":
            print(
                "::warning "
                f"file={decl.file},line={decl.line},title=Blueprint update suggested::"
                f"{decl.fqn} is changed in this PR but has no corresponding "
                "\\lean{} tag in blueprint/src/chapter."
            )
    print()


# ---------------------------------------------------------------------------
# Run sync check
# ---------------------------------------------------------------------------

def run_sync(
    root: Path,
    *,
    report_file: Path | None = None,
    update_lean_decls: bool = False,
) -> SyncReport:
    lean_root = root / "MIPStarRE"
    blueprint_src = root / "blueprint" / "src"
    lean_decls_path = root / "blueprint" / "lean_decls"

    if not lean_root.is_dir():
        raise FileNotFoundError(f"Lean source directory not found: {lean_root}")
    if not blueprint_src.is_dir():
        raise FileNotFoundError(f"Blueprint source directory not found: {blueprint_src}")

    report = SyncReport()

    # 1. Collect Lean declarations
    print("Scanning Lean source tree …")
    report.lean_decls = collect_lean_decls(lean_root)
    print(f"  Found {len(report.lean_decls)} declarations in Lean source")

    # 2. Collect blueprint entries
    print("Scanning blueprint .tex files …")
    report.blueprint_entries = collect_blueprint_entries(blueprint_src)
    print(f"  Found {len(report.blueprint_entries)} \\lean{{}} references in blueprint")
    report.orphan_leanok_tags = find_orphan_leanok_tags(blueprint_src)
    if report.orphan_leanok_tags:
        print(f"  Flagged {len(report.orphan_leanok_tags)} orphan \\leanok tag(s)")

    # 3. Cross-reference
    blueprint_decl_names: set[str] = set()
    for entry in report.blueprint_entries:
        blueprint_decl_names.add(entry.lean_decl)
        if entry.lean_decl not in report.lean_decls:
            report.missing_in_lean.append(entry)
            if entry.has_leanok or entry.proof_has_leanok:
                report.leanok_but_missing.append(entry)

    # 4. Optionally update lean_decls before diffing against it.  We capture the
    # pre-write contents first so the drift loops below still surface the
    # "developer added a blueprint ref but forgot to regenerate lean_decls"
    # warning even in the regeneration path.
    existing_lean_decls = read_lean_decls_file(lean_decls_path)
    if update_lean_decls:
        sorted_decls = sorted(blueprint_decl_names)
        lean_decls_path.write_text("\n".join(sorted_decls) + "\n")
        print(f"  Updated {lean_decls_path} with {len(sorted_decls)} entries")

    # 5. Check lean_decls file
    for name in sorted(existing_lean_decls - blueprint_decl_names):
        report.stale_lean_decls.append(name)
    for name in sorted(blueprint_decl_names - existing_lean_decls):
        report.missing_from_lean_decls_file.append(name)

    # 6. Print report
    _print_report(report, root)

    # 7. Write JSON report
    if report_file:
        _write_json_report(report, report_file, root)

    return report


def _chapter_stats(report: SyncReport) -> dict[str, dict]:
    """Per-chapter formalization progress."""
    stats: dict[str, dict] = {}
    for entry in report.blueprint_entries:
        chapter = entry.file
        if chapter not in stats:
            stats[chapter] = {
                "total": 0,
                "formalized": 0,
                "proof_formalized": 0,
                "missing_lean": 0,
            }
        s = stats[chapter]
        s["total"] += 1
        found = entry.lean_decl in report.lean_decls
        if entry.has_leanok and found:
            s["formalized"] += 1
        if entry.proof_has_leanok and found:
            s["proof_formalized"] += 1
        if not found:
            s["missing_lean"] += 1
    return stats


def _print_report(report: SyncReport, root: Path) -> None:
    print()
    print("=" * 70)
    print("  BLUEPRINT ↔ LEAN SYNC REPORT")
    print("=" * 70)

    # Per-chapter stats
    stats = _chapter_stats(report)
    print()
    print("Per-chapter formalization progress:")
    print(f"  {'Chapter':<50} {'Done':>5} / {'Total':>5}  {'%':>6}")
    print("  " + "-" * 68)
    total_done = 0
    total_all = 0
    for chapter in sorted(stats):
        s = stats[chapter]
        pct = 100 * s["formalized"] / s["total"] if s["total"] else 0
        short = chapter.replace("src/chapter/", "")
        print(f"  {short:<50} {s['formalized']:>5} / {s['total']:>5}  {pct:>5.1f}%")
        total_done += s["formalized"]
        total_all += s["total"]
    pct = 100 * total_done / total_all if total_all else 0
    print("  " + "-" * 68)
    print(f"  {'TOTAL':<50} {total_done:>5} / {total_all:>5}  {pct:>5.1f}%")

    # Missing in Lean
    if report.missing_in_lean:
        print()
        print(f"Blueprint refs with NO matching Lean declaration ({len(report.missing_in_lean)}):")
        seen: set[str] = set()
        for entry in report.missing_in_lean:
            if entry.lean_decl not in seen:
                seen.add(entry.lean_decl)
                ok_tag = " [has \\leanok!]" if (entry.has_leanok or entry.proof_has_leanok) else ""
                print(f"  ✗ {entry.lean_decl}{ok_tag}")
                print(f"    {entry.file}:{entry.line} ({entry.env_type})")

    # leanok but missing
    if report.leanok_but_missing:
        print()
        print(f"WARNING: \\leanok on items whose Lean decl is MISSING ({len(report.leanok_but_missing)}):")
        seen2: set[str] = set()
        for entry in report.leanok_but_missing:
            if entry.lean_decl not in seen2:
                seen2.add(entry.lean_decl)
                print(f"  ⚠ {entry.lean_decl}  ({entry.file}:{entry.line})")

    # Stale lean_decls
    if report.stale_lean_decls:
        print()
        print(f"Stale entries in lean_decls (not in any .tex) ({len(report.stale_lean_decls)}):")
        for name in report.stale_lean_decls:
            print(f"  − {name}")

    # Missing from lean_decls
    if report.missing_from_lean_decls_file:
        print()
        print(f"Blueprint refs missing from lean_decls file ({len(report.missing_from_lean_decls_file)}):")
        for name in report.missing_from_lean_decls_file:
            print(f"  + {name}")

    # Orphan leanok tags
    if report.orphan_leanok_tags:
        print()
        print(
            f"WARNING: orphan \\leanok tags (no preceding \\lean{{}} in the same statement/proof) "
            f"({len(report.orphan_leanok_tags)}):"
        )
        for orphan in report.orphan_leanok_tags:
            print(f"  ⚠ {orphan.file}:{orphan.line}  ({orphan.context})")

    # Summary
    print()
    if report.ok:
        print("✓ Blueprint and Lean code are in sync.")
    else:
        problems = (
            len(report.missing_in_lean)
            + len(report.stale_lean_decls)
            + len(report.missing_from_lean_decls_file)
        )
        print(f"✗ Found {problems} sync issue(s). See details above.")
    print()


def _write_json_report(report: SyncReport, path: Path, root: Path) -> None:
    data = {
        "sync_ok": report.ok,
        "total_blueprint_refs": len(report.blueprint_entries),
        "total_lean_decls": len(report.lean_decls),
        "missing_in_lean": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line, "has_leanok": e.has_leanok}
            for e in report.missing_in_lean
        ],
        "leanok_but_missing": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line}
            for e in report.leanok_but_missing
        ],
        "stale_lean_decls": report.stale_lean_decls,
        "missing_from_lean_decls_file": report.missing_from_lean_decls_file,
        "orphan_leanok_tags": [
            {"file": orphan.file, "line": orphan.line, "context": orphan.context}
            for orphan in report.orphan_leanok_tags
        ],
        "chapter_stats": _chapter_stats(report),
    }
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"JSON report written to {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check synchronisation between blueprint .tex and Lean source."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: auto-detected)",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="Write JSON report to this file",
    )
    parser.add_argument(
        "--update-lean-decls",
        action="store_true",
        help="Rewrite blueprint/lean_decls from current .tex refs",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit with code 1 on mismatches (for CI)",
    )
    parser.add_argument(
        "--warn-missing-blueprint",
        action="store_true",
        help=(
            "Warn about changed def/theorem/lemma declarations in changed Lean files "
            "that have no corresponding \\lean{} tag in blueprint chapters"
        ),
    )
    parser.add_argument(
        "--changed-files",
        nargs="*",
        default=None,
        help="Changed Lean files to inspect for reverse blueprint coverage",
    )
    parser.add_argument(
        "--diff-base",
        default=None,
        help="Git base revision for reverse blueprint coverage checks",
    )
    parser.add_argument(
        "--diff-head",
        default="HEAD",
        help="Git head revision for reverse blueprint coverage checks (default: HEAD)",
    )
    args = parser.parse_args()

    should_run_sync = (
        args.update_lean_decls
        or args.ci
        or args.report is not None
        or not args.warn_missing_blueprint
    )

    if should_run_sync:
        report = run_sync(
            args.root,
            report_file=args.report,
            update_lean_decls=args.update_lean_decls,
        )
        if args.ci and not report.ok:
            sys.exit(1)

    if args.warn_missing_blueprint:
        if not args.changed_files:
            parser.error("--warn-missing-blueprint requires --changed-files")
        if not args.diff_base:
            parser.error("--warn-missing-blueprint requires --diff-base")
        missing = find_changed_decls_missing_from_blueprint(
            args.root,
            changed_files=args.changed_files,
            diff_base=args.diff_base,
            diff_head=args.diff_head,
        )
        print_missing_blueprint_warnings(missing)


if __name__ == "__main__":
    main()
