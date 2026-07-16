#!/usr/bin/env python3
"""Assemble the body of Challenge.lean from the extractor's TSV.

Input: the TSV produced by ``extract_closure.lean`` (one declaration per row:
name, module path, start line, end line).  For each declaration this script
re-reads its source lines and records the namespace stack active at that
point (tracking ``namespace``/``section``/``end`` lines), orders declarations
topologically (module import rank, then line number), and emits the snippets
grouped under merged namespace blocks with provenance comments.

The ``EXTRAS``/``MODULE_PRELUDES`` tables carry elaboration context (attribute
commands, ``CoeFun`` instances, ``variable``/``open`` blocks) that the kernel
closure cannot see; the script fails if a table key no longer matches any
extracted declaration.  See README.md in this directory for the full
regeneration pipeline.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# extra context commands needed for re-elaboration but absent from the kernel
# closure (attributes, CoeFun instances that elaboration unfolds), keyed by the
# declaration after which they must appear
EXTRAS: dict[str, list[str]] = {
    "MIPStarRE.LDT.FieldModel": [
        "",
        "-- source: MIPStarRE/LDT/Basic/ParametersBase.lean (attribute command)",
        "attribute [instance_reducible, instance] FieldModel.instField FieldModel.instFintype",
        "  FieldModel.instDecidableEq",
    ],
    "MIPStarRE.LDT.Polynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LowDegreePolynomial.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=",
        "  ⟨Polynomial.toFun⟩",
    ],
    "MIPStarRE.LDT.AxisLinePolynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LinePolynomials.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=",
        "  ⟨AxisLinePolynomial.toFun⟩",
    ],
    "MIPStarRE.LDT.AxisParallelCovariantMeasurement": [
        "",
        "-- source: MIPStarRE/LDT/Test/StrategyCore.lean (elaboration context)",
        "instance {params : Parameters} [FieldModel params.q] {ι : Type*}",
        "    [Fintype ι] [DecidableEq ι] :",
        "    CoeFun (AxisParallelCovariantMeasurement params ι)",
        "      (fun _ => AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) where",
        "  coe M := M.toIdxProjMeas",
    ],
    "MIPStarRE.LDT.DiagonalCovariantMeasurement": [
        "",
        "-- source: MIPStarRE/LDT/Test/StrategyCore.lean (elaboration context)",
        "instance {params : Parameters} [FieldModel params.q] {ι : Type*}",
        "    [Fintype ι] [DecidableEq ι] :",
        "    CoeFun (DiagonalCovariantMeasurement params ι)",
        "      (fun _ => DiagonalLine params → ProjMeas (DiagonalLinePolynomial params) ι) where",
        "  coe M := M.toIdxProjMeas",
    ],
    "MIPStarRE.LDT.DiagonalLinePolynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LinePolynomials.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=",
        "  ⟨DiagonalLinePolynomial.toFun⟩",
    ],
}

# per-module elaboration context (opens/variables) inserted once before the
# module's first snippet, inside the given namespace stack, wrapped in
# `section ... end`
MODULE_PRELUDES: dict[str, tuple[list[str], list[str]]] = {
    "MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean": (
        ["MIPStarRE.LDT", "ProjStrat"],
        [
            "open MIPStarRE.Quantum",
            "variable {params : Parameters} [FieldModel params.q]",
            "variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]",
            "variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]",
        ],
    ),
    "MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean": (
        ["MIPStarRE.Quantum"],
        [
            "open scoped Matrix.Norms.Elementwise",
            "open WithLp",
            "variable {d : Type*} [Fintype d]",
        ],
    ),
}

Entry = tuple[str, str, int, int, list[str]]


class Assembler:
    def __init__(self, repo_root: Path) -> None:
        self.repo_root = repo_root
        self._file_cache: dict[str, list[str]] = {}
        self.out: list[str] = []
        self.cur_ns: list[str] = []
        self.open_prelude: tuple[str, list[str]] | None = None

    def get_lines(self, path: str) -> list[str]:
        if path not in self._file_cache:
            text = (self.repo_root / path).read_text(encoding="utf-8")
            self._file_cache[path] = text.splitlines()
        return self._file_cache[path]

    def ns_stack_at(self, path: str, line_no: int) -> list[str]:
        """Namespace stack (list of names) active just before 1-indexed line_no."""
        stack: list[tuple[str, str | None]] = []
        for raw in self.get_lines(path)[: line_no - 1]:
            s = raw.strip()
            m = re.match(r"namespace\s+([\w.À-￿']+)", s)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"section\s*([\w.À-￿']*)", s)
            if m and s.startswith("section"):
                stack.append(("sec", m.group(1) or None))
                continue
            m = re.match(r"end\s*([\w.À-￿']*)\s*(?:--.*)?$", s)
            if m and s.startswith("end") and stack:
                stack.pop()
        return [n for kind, n in stack if kind == "ns" and n is not None]

    def imports_of(self, path: str) -> list[str]:
        # imports are only legal at the top of a Lean file, so scanning the
        # whole file for ^import is safe and robust against comment headers
        return [
            m.group(1).replace(".", "/") + ".lean"
            for raw in self.get_lines(path)
            if (m := re.match(r"import\s+([\w.]+)", raw))
        ]

    def module_ranks(self, mods: set[str]) -> dict[str, int]:
        rank: dict[str, int] = {}

        def visit(p: str, depth: int = 0) -> None:
            if p in rank or depth > 200:
                return
            rank[p] = -1  # in progress
            local = [d for d in self.imports_of(p) if d.startswith("MIPStarRE/")]
            for d in local:
                if rank.get(d) != -1:
                    visit(d, depth + 1)
            rank[p] = max((rank.get(d, 0) for d in local), default=0) + 1

        for p in sorted(mods):
            visit(p)
        return rank

    def switch_ns(self, target: list[str]) -> None:
        common = 0
        while (
            common < min(len(self.cur_ns), len(target))
            and self.cur_ns[common] == target[common]
        ):
            common += 1
        for n in reversed(self.cur_ns[common:]):
            self.out.append(f"end {n}")
        for n in target[common:]:
            self.out.append(f"namespace {n}")
        self.cur_ns = target

    def close_prelude(self) -> None:
        if self.open_prelude:
            self.switch_ns(self.open_prelude[1])
            self.out.append("end  -- module scope")
            self.open_prelude = None

    def emit(self, entries: list[Entry], generated: list[tuple[str, str]]) -> str:
        # compiler-generated declarations (no source range) regenerate
        # identically during elaboration; record them up front as comments so
        # they never interact with namespace or prelude state
        if generated:
            self.out.append("-- Compiler-generated declarations in the closure (no source")
            self.out.append("-- range); they regenerate identically during elaboration:")
            for name, path in generated:
                self.out.append(f"--   {name}  (from {path})")

        emitted_ranges: set[tuple[str, int]] = set()
        prev_path: str | None = None
        for name, path, a, b, src in entries:
            if (path, a) in emitted_ranges:  # deriving twins share the range
                continue
            emitted_ranges.add((path, a))
            if path != prev_path:
                self.close_prelude()
                if path in MODULE_PRELUDES:
                    base_ns, lines = MODULE_PRELUDES[path]
                    self.switch_ns(base_ns)
                    self.out.append("")
                    self.out.append(f"-- elaboration context of {path}")
                    self.out.append("section")
                    self.out.extend(lines)
                    self.open_prelude = (path, base_ns)
                prev_path = path
            self.switch_ns(self.ns_stack_at(path, a))
            self.out.append("")
            self.out.append(f"-- source: {path}:{a}-{b}  ({name})")
            self.out.extend(src)
            self.out.extend(EXTRAS.get(name, []))
        self.close_prelude()
        self.switch_ns([])
        return "\n".join(self.out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tsv", type=Path, help="TSV from extract_closure.lean")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    args = parser.parse_args()

    asm = Assembler(args.root)
    entries: list[Entry] = []
    generated: list[tuple[str, str]] = []
    for row in args.tsv.read_text(encoding="utf-8").splitlines():
        if not row or "\t" not in row:
            continue
        name, path, a, b = row.split("\t")
        if a == "NORANGE":
            generated.append((name, path))
            continue
        start, end = int(a), int(b)
        entries.append((name, path, start, end, asm.get_lines(path)[start - 1 : end]))

    rank = asm.module_ranks({e[1] for e in entries})
    entries.sort(key=lambda e: (rank.get(e[1], 999), e[2]))

    body = asm.emit(entries, generated)

    unused_extras = set(EXTRAS) - {name for name, *_ in entries}
    unused_preludes = set(MODULE_PRELUDES) - {e[1] for e in entries}
    if unused_extras or unused_preludes:
        print(
            "stale context tables — "
            f"unmatched EXTRAS keys: {sorted(unused_extras)}; "
            f"unmatched MODULE_PRELUDES keys: {sorted(unused_preludes)}",
            file=sys.stderr,
        )
        return 1

    print(body)
    return 0


if __name__ == "__main__":
    sys.exit(main())
