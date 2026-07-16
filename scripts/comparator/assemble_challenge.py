#!/usr/bin/env python3
"""Assemble a draft Challenge.lean from extract_out.tsv (topological order).

For each declaration, re-read its source lines and record the namespace stack
active at that point (tracking `namespace`/`section`/`end` lines).  Emit
snippets grouped under merged namespace blocks, with provenance comments.
"""
import re, sys

import os
REPO = os.getcwd()  # run from the repository root
TSV = sys.argv[1]

files = {}
def get_lines(path):
    if path not in files:
        files[path] = open(f"{REPO}/{path}").read().splitlines()
    return files[path]

def ns_stack_at(path, line_no):
    """Namespace stack (list of names) active just before 1-indexed line_no."""
    stack = []  # entries: ('ns', name) or ('sec', name-or-None)
    for i, raw in enumerate(get_lines(path)[: line_no - 1], 1):
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
    return [n for k, n in stack if k == "ns"]

entries = []
for row in open(TSV):
    row = row.rstrip("\n")
    if not row or "\t" not in row:
        continue
    name, path, a, b = row.split("\t")
    if a == "NORANGE":
        # compiler-generated declarations (congruence lemmas, autoParam
        # helpers) have no source range; they regenerate identically in the
        # challenge environment, so a note suffices
        entries.append((name, path, None, None,
                        [f"-- {name} is compiler-generated (no source range); "
                         "it regenerates identically during elaboration"]))
        continue
    a, b = int(a), int(b)
    src = get_lines(path)[a - 1 : b]
    entries.append((name, path, a, b, src))

# --- topological order: module import DAG rank, then line number ---
def imports_of(path):
    # imports are only legal at the top of a Lean file, so scanning the whole
    # file for ^import is safe and robust against comment headers
    return [m.group(1).replace(".", "/") + ".lean"
            for raw in get_lines(path)
            if (m := re.match(r"import\s+([\w.]+)", raw))]

mods = {e[1] for e in entries if e[2] is not None}
rank = {}
def visit(p, depth=0):
    if p in rank or depth > 200:
        return
    rank[p] = -1  # in progress
    for d in imports_of(p):
        if d.startswith("MIPStarRE/") and rank.get(d) != -1:
            visit(d, depth + 1)
    rank[p] = max((rank.get(d, 0) for d in imports_of(p)
                   if d.startswith("MIPStarRE/")), default=0) + 1

for p in sorted(mods):
    visit(p)
entries.sort(key=lambda e: (rank.get(e[1], 999), e[2] or 0))

out = []
cur_ns = []
def switch_ns(target):
    global cur_ns
    # close/open namespaces to reach target stack
    common = 0
    while common < min(len(cur_ns), len(target)) and cur_ns[common] == target[common]:
        common += 1
    for n in reversed(cur_ns[common:]):
        out.append(f"end {n}")
    for n in target[common:]:
        out.append(f"namespace {n}")
    cur_ns = target

# extra context commands needed for re-elaboration but absent from the kernel
# closure (attributes, CoeFun instances that elaboration unfolds), keyed by the
# declaration after which they must appear
EXTRAS = {
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
# module's first snippet, inside `base_ns`, wrapped in `section ... end`
MODULE_PRELUDES = {
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

emitted_ranges = set()
open_prelude = None  # (path, base_ns) of the module section currently open

def close_prelude():
    global open_prelude
    if open_prelude:
        switch_ns(open_prelude[1])
        out.append("end  -- module scope")
        open_prelude = None

prev_path = None
for name, path, a, b, src in entries:
    if (path, a) in emitted_ranges:  # deriving-generated twins share the range
        continue
    emitted_ranges.add((path, a))
    if path != prev_path:
        close_prelude()
        if path in MODULE_PRELUDES:
            base_ns, lines = MODULE_PRELUDES[path]
            switch_ns(base_ns)
            out.append("")
            out.append(f"-- elaboration context of {path}")
            out.append("section")
            out.extend(lines)
            open_prelude = (path, base_ns)
        prev_path = path
    ns = ns_stack_at(path, a) if a else []
    switch_ns(ns)
    out.append("")
    out.append(f"-- source: {path}:{a}-{b}  ({name})")
    out.extend(src)
    out.extend(EXTRAS.get(name, []))
close_prelude()
switch_ns([])

unused_extras = set(EXTRAS) - {name for name, *_ in entries}
unused_preludes = set(MODULE_PRELUDES) - {e[1] for e in entries}
if unused_extras or unused_preludes:
    sys.exit(f"stale context tables — unmatched EXTRAS keys: {sorted(unused_extras)}; "
             f"unmatched MODULE_PRELUDES keys: {sorted(unused_preludes)}")

print("\n".join(out))
