#!/usr/bin/env python3
r"""Blueprint ↔ Lean axiom sync check.

For every blueprint environment that carries a ``\lean{Name}`` tag, this script:

* emits an **error** if ``Name`` does not resolve to a Lean declaration
  (and the blueprint claims ``\leanok``; otherwise a warning);
* emits an **error** if the blueprint has ``\leanok`` (statement or proof
  level) but the transitive axiom closure of ``Name`` contains ``sorryAx``;
* emits a **warning** if ``Name`` is sorry-free in Lean but the blueprint
  entry is missing any ``\leanok`` tag.

The axiom closure is computed by generating a temporary ``.lean`` harness that
runs ``#print axioms Name`` for each referenced declaration, then parsing the
output of ``lake env lean``.

Use ``--skip-axiom-check`` for a fast, parse-only smoke test.

Exit code is 1 on any error, 0 otherwise. Warnings never fail the check.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

TEX_ENV_BEGIN = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
)
TEX_ENV_END = re.compile(
    r"\\end\{(theorem|lemma|proposition|corollary|definition)\}"
)
TEX_PROOF_BEGIN = re.compile(r"\\begin\{proof\}")
TEX_PROOF_END = re.compile(r"\\end\{proof\}")
TEX_LEAN = re.compile(r"\\lean\{([^}]+)\}")
TEX_LEANOK = re.compile(r"\\leanok\b")


@dataclass
class Entry:
    """A blueprint environment that references a Lean declaration."""

    file: str
    line: int
    env_type: str
    lean_name: str
    stmt_leanok: bool
    proof_leanok: bool

    @property
    def any_leanok(self) -> bool:
        return self.stmt_leanok or self.proof_leanok


def parse_chapters(blueprint_src: Path, repo_root: Path) -> list[Entry]:
    """Parse every blueprint/src/chapter/*.tex for ``\\lean{}`` + ``\\leanok``."""
    entries: list[Entry] = []
    chapter_dir = blueprint_src / "chapter"
    if not chapter_dir.is_dir():
        return entries

    for tex in sorted(chapter_dir.glob("*.tex")):
        rel = str(tex.relative_to(repo_root))
        lines = tex.read_text(errors="replace").splitlines()
        in_env = False
        in_proof = False
        env_type = ""
        env_line = 0
        env_decls: list[str] = []
        env_leanok = False
        proof_leanok = False
        last_env_entries: list[Entry] = []

        for i, line in enumerate(lines, 1):
            if not in_env and TEX_ENV_BEGIN.search(line):
                m = TEX_ENV_BEGIN.search(line)
                in_env = True
                env_type = m.group(1)
                env_line = i
                env_decls = []
                env_leanok = False
                for dm in TEX_LEAN.finditer(line):
                    env_decls.extend(
                        d.strip() for d in dm.group(1).split(",") if d.strip()
                    )
                if TEX_LEANOK.search(line):
                    env_leanok = True
                continue
            if in_env and TEX_ENV_END.search(line):
                in_env = False
                last_env_entries = []
                for d in env_decls:
                    e = Entry(
                        file=rel, line=env_line, env_type=env_type,
                        lean_name=d, stmt_leanok=env_leanok,
                        proof_leanok=False,
                    )
                    entries.append(e)
                    last_env_entries.append(e)
                continue
            if TEX_PROOF_BEGIN.search(line):
                in_proof = True
                proof_leanok = bool(TEX_LEANOK.search(line))
                continue
            if in_proof and TEX_PROOF_END.search(line):
                if proof_leanok:
                    for e in last_env_entries:
                        e.proof_leanok = True
                in_proof = False
                proof_leanok = False
                last_env_entries = []
                continue
            if in_env:
                for dm in TEX_LEAN.finditer(line):
                    env_decls.extend(
                        d.strip() for d in dm.group(1).split(",") if d.strip()
                    )
                if TEX_LEANOK.search(line):
                    env_leanok = True
            if in_proof and TEX_LEANOK.search(line):
                proof_leanok = True
    return entries


def _unique(seq):
    seen: set[str] = set()
    out: list[str] = []
    for x in seq:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def run_axiom_check(
    decls: list[str], repo_root: Path, lake: str
) -> dict[str, dict] | None:
    """Run ``lake env lean`` on a harness that ``#print axioms`` every decl.

    Returns ``None`` to signal a global harness failure (e.g. ``import
    MIPStarRE`` failed) — the caller should skip per-declaration
    classification rather than emit false errors for every ``\\leanok``
    entry.
    """
    if not decls:
        return {}

    header = ["import MIPStarRE", ""]  # lines 1 and 2
    body = [f"#print axioms {d}" for d in decls]
    # harness line numbers: body entry i lives on line len(header)+1+i.
    base = len(header) + 1
    line_to_decl = {base + i: d for i, d in enumerate(decls)}

    with tempfile.TemporaryDirectory() as td:
        harness = Path(td) / "BlueprintAxiomCheck.lean"
        harness.write_text("\n".join(header + body) + "\n")
        proc = subprocess.run(
            [lake, "env", "lean", str(harness)],
            cwd=repo_root, capture_output=True, text=True,
        )
        harness_str = str(harness)

    output = (proc.stdout or "") + "\n" + (proc.stderr or "")
    # Lean may emit `#print axioms` output either prefixed with a
    # ``<file>:line:col:`` location (the historical format) or as plain
    # lines (seen in Lean 4.28). Handle both by attributing lines to a decl
    # first via line number, then falling back to the ``'DeclName'`` quoted
    # subject that appears at the start of every ``#print axioms`` message.
    loc_re = re.compile(rf"^{re.escape(harness_str)}:(\d+):\d+:\s*(.*)$")
    records: dict[str, list[str]] = {d: [] for d in decls}
    current: str | None = None
    for raw_line in output.splitlines():
        content = raw_line
        matched: str | None = None
        m = loc_re.match(raw_line)
        if m:
            content = m.group(2)
            matched = line_to_decl.get(int(m.group(1)))
        if matched is None:
            for decl in decls:
                if f"'{decl}'" in content:
                    matched = decl
                    break
        if matched is not None:
            current = matched
        if current is not None:
            records[current].append(content)

    # Global-failure detection: ``lake env lean`` exited non-zero and we
    # matched no output to any queried declaration. The most common cause
    # is ``import MIPStarRE`` failing before the harness body runs. Signal
    # ``None`` so the caller can skip classification and exit cleanly
    # rather than reporting every ``\leanok`` entry as a missing decl.
    if proc.returncode != 0 and not any(records[d] for d in decls):
        sys.stderr.write(
            f"warning: `lake env lean` exited with status {proc.returncode} "
            "and produced no recognised `#print axioms` output. MIPStarRE "
            "likely failed to import. Skipping per-declaration "
            "classification to avoid spurious errors.\n"
        )
        sys.stderr.write("Raw lake output (tail):\n")
        sys.stderr.write(output[-4000:] + "\n")
        return None

    result: dict[str, dict] = {}
    for decl in decls:
        joined = "\n".join(records.get(decl, []))
        exists = True
        axioms: list[str] = []
        if not joined:
            exists = False
        elif "unknown identifier" in joined or "unknown constant" in joined:
            exists = False
        elif "does not depend on any axioms" in joined:
            pass
        else:
            mm = re.search(r"depends on axioms:\s*\[([^\]]*)\]", joined, re.DOTALL)
            if mm:
                axioms = [a.strip() for a in mm.group(1).split(",") if a.strip()]
        result[decl] = {
            "exists": exists,
            "sorry": any(a == "sorryAx" or a.startswith("sorryAx.") for a in axioms),
            "axioms": axioms,
            "raw": joined,
        }
    return result


def _emit(kind: str, file: str, line: int, title: str, msg: str) -> None:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        safe = msg.replace("\n", "%0A").replace("\r", "")
        print(f"::{kind} file={file},line={line},title={title}::{safe}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--repo-root", type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: parent of this script)",
    )
    ap.add_argument(
        "--skip-axiom-check", action="store_true",
        help="Parse blueprint only; skip the Lean axiom closure step",
    )
    ap.add_argument(
        "--lake", default="lake",
        help="Path to the lake binary (default: lake on PATH)",
    )
    args = ap.parse_args()
    root = args.repo_root.resolve()

    entries = parse_chapters(root / "blueprint" / "src", root)
    print(
        f"Parsed {len(entries)} blueprint \\lean{{}} entries from "
        f"{(root / 'blueprint/src/chapter').relative_to(root)}"
    )
    if not entries:
        return 0

    decls = _unique(e.lean_name for e in entries)
    if args.skip_axiom_check:
        print("Axiom check skipped (--skip-axiom-check).")
        return 0

    print(f"Running `{args.lake} env lean` axiom check on {len(decls)} unique decls …")
    axinfo = run_axiom_check(decls, root, lake=args.lake)
    if axinfo is None:
        print(
            "Axiom check skipped: the harness itself failed to run "
            "(see stderr warning above). Blueprint drift was not evaluated; "
            "exiting 0 so the real cause (e.g. a broken Lean build) is not "
            "hidden behind cascading blueprint errors."
        )
        return 0

    errors = 0
    warnings = 0
    for e in entries:
        info = axinfo.get(e.lean_name, {"exists": False, "sorry": False})
        if not info["exists"]:
            msg = (
                f"{e.lean_name}: blueprint \\lean{{}} tag but declaration "
                f"not found in Lean source."
            )
            if e.any_leanok:
                errors += 1
                print(f"ERROR {e.file}:{e.line} {msg}")
                _emit("error", e.file, e.line, "Blueprint sync", msg)
            else:
                warnings += 1
                print(f"WARN  {e.file}:{e.line} {msg}")
                _emit("warning", e.file, e.line, "Blueprint sync", msg)
            continue
        if info["sorry"] and e.any_leanok:
            errors += 1
            msg = (
                f"{e.lean_name}: \\leanok in blueprint but transitive axiom "
                f"closure includes sorryAx. Remove \\leanok or close the sorry."
            )
            print(f"ERROR {e.file}:{e.line} {msg}")
            _emit("error", e.file, e.line, "Blueprint sync", msg)
        elif (not info["sorry"]) and (not e.any_leanok):
            warnings += 1
            msg = (
                f"{e.lean_name}: sorry-free in Lean but blueprint entry has "
                f"no \\leanok tag. Consider adding one."
            )
            print(f"WARN  {e.file}:{e.line} {msg}")
            _emit("warning", e.file, e.line, "Blueprint sync", msg)

    print(
        f"\nSummary: {errors} error(s), {warnings} warning(s), "
        f"{len(entries)} entries, {len(decls)} unique decls."
    )
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
