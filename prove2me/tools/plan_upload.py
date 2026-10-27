#!/usr/bin/env python3
"""Plan the Prove2Me LIDT upload from the sanctioned extractor outputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import unicodedata
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
GRAPH = ROOT / "prove2me" / "extracted" / "decl_graph.jsonl"
SKETCH_DIR = ROOT / "prove2me" / "extracted" / "sketch"
SKETCH_MANIFEST = ROOT / "prove2me" / "extracted" / "sketch_modules.tsv"
PLAN = ROOT / "prove2me" / "generated" / "upload_plan.json"
PLAN_TSV = ROOT / "prove2me" / "generated" / "upload_plan.tsv"
RENAME_TSV = ROOT / "prove2me" / "generated" / "rename_map.tsv"
QPBT_NEEDS = Path("/home/drx/p2m/status/qpbt-needs-from-lidt.txt")
QPBT_NAMES = Path("/home/drx/p2m/status/lidt-names.tsv")
SIMP_DECLS = ROOT / "prove2me" / "extracted" / "simp_decls.txt"
SOURCE_SHA = "f382c801026f53a9efc260fdee707cb35e0adb15"
MAIN_TARGET = "MIPStarRE.LDT.Test.mainFormal"
SUPPORT_MODULE_PREFIXES = ("MIPStarRE.LDT.Tactic.",)
PLATFORM_NAME_OVERRIDES = {
    # Anonymous instance names include source-module hygiene. Moving their
    # commands under prove2me/platform deterministically changes that suffix.
    "MIPStarRE.LDT.CommutativityPoints.instFintypeDiagonalLine":
        "LIDT.MIPStarRE.LDT.CommutativityPoints.instFintypeDiagonalLine_prove2me",
    "MIPStarRE.LDT.GlobalVariance.instFintypeAxisParallelLine":
        "LIDT.MIPStarRE.LDT.GlobalVariance.instFintypeAxisParallelLine_prove2me",
    "MIPStarRE.LDT.GlobalVariance.instNonemptyPolynomial":
        "LIDT.MIPStarRE.LDT.GlobalVariance.instNonemptyPolynomial_prove2me",
    "MIPStarRE.LDT.instDecidableEqAxisLinePolynomial":
        "LIDT.MIPStarRE.LDT.instDecidableEqAxisLinePolynomial_prove2me",
    "MIPStarRE.LDT.instDecidableEqPolynomial":
        "LIDT.MIPStarRE.LDT.instDecidableEqPolynomial_prove2me",
    "MIPStarRE.LDT.instFintypeAxisLinePolynomial":
        "LIDT.MIPStarRE.LDT.instFintypeAxisLinePolynomial_prove2me",
    "MIPStarRE.LDT.instFintypeDiagonalLinePolynomial":
        "LIDT.MIPStarRE.LDT.instFintypeDiagonalLinePolynomial_prove2me",
    "MIPStarRE.LDT.instFintypePolynomial":
        "LIDT.MIPStarRE.LDT.instFintypePolynomial_prove2me",
    "MIPStarRE.LDT.instFintypeRole_1":
        "LIDT.MIPStarRE.LDT.instFintypeRole_prove2me",
}


@dataclass(frozen=True)
class Position:
    line: int
    col: int
    offset: int

    @classmethod
    def from_json(cls, value: dict[str, int]) -> "Position":
        return cls(value["line"], value["col"], value["offset"])

    def as_json(self) -> dict[str, int]:
        return {"line": self.line, "col": self.col, "offset": self.offset}


@dataclass
class Command:
    command_id: str
    module: str
    index: int
    name_text: str | None
    start: Position
    end: Position
    val_start: Position | None
    val_kind: str | None
    docstring: dict[str, Any] | None
    private_tok: dict[str, Any] | None
    rows: list[str]
    anchor: str | None = None

    def as_json(self) -> dict[str, Any]:
        return {
            "commandId": self.command_id,
            "module": self.module,
            "index": self.index,
            "nameText": self.name_text,
            "declStart": self.start.as_json(),
            "declEnd": self.end.as_json(),
            "valStart": self.val_start.as_json() if self.val_start else None,
            "valKind": self.val_kind,
            "docstring": self.docstring,
            "privateTok": self.private_tok,
            "rows": self.rows,
            "anchor": self.anchor,
        }


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def source_path(module: str) -> Path:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise FileNotFoundError(f"missing source for {module}: {path}")
    return path


def read_needs() -> list[str]:
    lines = [line.strip() for line in QPBT_NEEDS.read_text(encoding="utf-8").splitlines()]
    if not lines or lines[-1] != "END":
        raise RuntimeError(f"incomplete QPBT declaration list: {QPBT_NEEDS}")
    names = [line for line in lines[:-1] if line]
    if len(names) != len(set(names)):
        raise RuntimeError("QPBT declaration list contains duplicates")
    return names


def parse_imports(module: str) -> list[str]:
    imports: list[str] = []
    for line in source_path(module).read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped == "module" or stripped.startswith("--"):
            continue
        match = re.fullmatch(r"(?:(?:public|meta)\s+)*import\s+([^\s]+)", stripped)
        if match:
            imports.append(match.group(1))
            continue
        break
    return imports


def name_matches(name: str, name_text: str) -> bool:
    return name == name_text or name.endswith("." + name_text)


def choose_anchor(command: Command, rows: dict[str, dict[str, Any]]) -> str | None:
    candidates = [rows[name] for name in command.rows]
    if not candidates:
        return None
    if command.name_text is None:
        instances = [row for row in candidates if row["isInstance"]]
        pool = instances or candidates
    else:
        matches = [row for row in candidates if name_matches(row["userName"], command.name_text)]
        pool = matches or candidates
    kind_rank = {"theorem": 0, "def": 0, "opaque": 0, "inductive": 0,
                 "ctor": 1, "rec": 2}
    pool.sort(key=lambda row: (
        kind_rank.get(row["kind"], 3),
        row["userName"].count("."),
        len(row["userName"]),
        row["name"],
    ))
    return pool[0]["name"]


def topo_sort(items: Iterable[str], dependencies: dict[str, set[str]]) -> list[str]:
    item_set = set(items)
    deps = {item: set(dependencies.get(item, set())) & item_set for item in item_set}
    reverse: dict[str, set[str]] = defaultdict(set)
    indegree = {item: len(reqs) for item, reqs in deps.items()}
    for item, reqs in deps.items():
        for req in reqs:
            reverse[req].add(item)
    ready = sorted(item for item, degree in indegree.items() if degree == 0)
    result: list[str] = []
    while ready:
        item = ready.pop(0)
        result.append(item)
        for consumer in sorted(reverse.get(item, set())):
            indegree[consumer] -= 1
            if indegree[consumer] == 0:
                ready.append(consumer)
                ready.sort()
    if len(result) != len(item_set):
        cycle = sorted(item for item, degree in indegree.items() if degree)
        raise RuntimeError(f"dependency cycle among {len(cycle)} items: {cycle[:12]}")
    return result


GREEK = {
    "α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "ε": "eps",
    "ζ": "zeta", "η": "eta", "θ": "theta", "ι": "iota", "κ": "kappa",
    "λ": "lambda", "μ": "mu", "ν": "nu", "ξ": "xi", "π": "pi",
    "ρ": "rho", "σ": "sigma", "τ": "tau", "φ": "phi", "χ": "chi",
    "ψ": "psi", "ω": "omega", "Γ": "Gamma", "Δ": "Delta", "Θ": "Theta",
    "Λ": "Lambda", "Ξ": "Xi", "Π": "Pi", "Σ": "Sigma", "Φ": "Phi",
    "Ψ": "Psi", "Ω": "Omega",
}
SUBSCRIPT = {"₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4",
             "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9"}


def ascii_segment(segment: str) -> str:
    out: list[str] = []
    for char in segment:
        if char.isascii() and (char.isalnum() or char == "_"):
            out.append(char)
        elif char == "'":
            out.append("_prime")
        elif char in GREEK:
            out.append("_" + GREEK[char])
        elif char in SUBSCRIPT:
            out.append("_" + SUBSCRIPT[char])
        else:
            label = unicodedata.name(char, "").lower().replace(" ", "_").replace("-", "_")
            out.append("_" + (label or f"u{ord(char):04x}"))
    value = re.sub(r"_+", "_", "".join(out)).strip("_")
    if not value:
        value = "decl"
    if value[0].isdigit():
        value = "n_" + value
    return value


def ascii_name(name: str) -> str:
    return ".".join(ascii_segment(segment) for segment in name.split("."))


def command_name(command: Command, rows: dict[str, dict[str, Any]]) -> str:
    if command.anchor is None:
        raise RuntimeError(f"command has no anchor: {command.command_id}")
    return rows[command.anchor]["userName"]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-qpbt-names", action="store_true")
    args = parser.parse_args()

    graph_rows = read_jsonl(GRAPH)
    rows = {row["name"]: row for row in graph_rows}
    by_user: dict[str, list[str]] = defaultdict(list)
    for row in graph_rows:
        by_user[row["userName"]].append(row["name"])

    modules = sorted({row["module"] for row in graph_rows})
    if not SKETCH_MANIFEST.is_file():
        raise RuntimeError(f"Stage 2 is not complete: missing {SKETCH_MANIFEST}")
    manifest_modules = [
        line.split("\t", 1)[0]
        for line in SKETCH_MANIFEST.read_text(encoding="utf-8").splitlines() if line
    ]
    sketch_files = {path.stem for path in SKETCH_DIR.glob("*.jsonl")}
    missing_sketch = sorted(set(manifest_modules) - sketch_files)
    if missing_sketch:
        raise RuntimeError(f"Stage 2 is incomplete; missing {len(missing_sketch)} modules")

    commands: dict[str, Command] = {}
    module_commands: dict[str, list[str]] = defaultdict(list)
    row_to_command: dict[str, str] = {}
    orphan_rows: dict[str, list[str]] = defaultdict(list)
    source_ref_names: dict[str, set[str]] = defaultdict(set)
    for module in modules:
        facts = read_jsonl(SKETCH_DIR / f"{module}.jsonl")
        decls = [fact for fact in facts if fact["kind"] == "decl"]
        refs = [fact for fact in facts if fact["kind"] == "ref"]
        for index, fact in enumerate(decls):
            command_id = f"{module}#{index:04d}"
            command = Command(
                command_id=command_id,
                module=module,
                index=index,
                name_text=fact["nameText"],
                start=Position.from_json(fact["declStart"]),
                end=Position.from_json(fact["declEnd"]),
                val_start=Position.from_json(fact["valStart"]) if fact["valStart"] else None,
                val_kind=fact["valKind"],
                docstring=None if fact["docstring"] is None else fact["docstring"],
                private_tok=None if fact["privateTok"] is None else fact["privateTok"],
                rows=[],
            )
            commands[command_id] = command
            module_commands[module].append(command_id)
        for row in (row for row in graph_rows if row["module"] == module and row["startLine"] > 0):
            containing = [command for command in (commands[cid] for cid in module_commands[module])
                          if command.start.line <= row["startLine"] <= command.end.line]
            if not containing:
                orphan_rows[module].append(row["name"])
                continue
            if len(containing) != 1:
                raise RuntimeError(
                    f"expected one Stage 2 command for {row['name']} at {module}:{row['startLine']}; "
                    f"found {len(containing)}")
            containing[0].rows.append(row["name"])
            row_to_command[row["name"]] = containing[0].command_id
        for command_id in module_commands[module]:
            commands[command_id].anchor = choose_anchor(commands[command_id], rows)
        for ref in refs:
            ref_start = ref["start"]["offset"]
            ref_end = ref["end"]["offset"]
            containing = [
                command for command in (commands[cid] for cid in module_commands[module])
                if command.start.offset <= ref_start < ref_end <= command.end.offset
            ]
            if len(containing) == 1:
                source_ref_names[containing[0].command_id].add(ref["const"])

    needs = read_needs()

    def resolve(name: str) -> str:
        if name in rows:
            return name
        matches = by_user.get(name, [])
        if len(matches) == 1:
            return matches[0]
        raise RuntimeError(f"cannot uniquely resolve declaration {name!r}: {matches}")

    if not SIMP_DECLS.is_file():
        raise RuntimeError(f"missing supplemental simp-declaration extraction: {SIMP_DECLS}")
    simp_rows = {
        resolve(line.strip())
        for line in SIMP_DECLS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    source_ref_rows: dict[str, set[str]] = defaultdict(set)
    for command_id, names in source_ref_names.items():
        for name in names:
            if name in rows:
                source_ref_rows[command_id].add(name)
            elif len(by_user.get(name, [])) == 1:
                source_ref_rows[command_id].add(by_user[name][0])

    requested_rows = {name: resolve(name) for name in needs}
    support_modules = {
        module for module in modules if module.startswith(SUPPORT_MODULE_PREFIXES)}
    root_rows = [
        resolve(MAIN_TARGET),
        *requested_rows.values(),
        *(row["name"] for row in graph_rows if row["isInstance"]),
        *simp_rows,
        *(row["name"] for row in graph_rows if row["module"] in support_modules),
    ]

    constructors: dict[str, set[str]] = defaultdict(set)
    for row in graph_rows:
        if row["kind"] != "ctor":
            continue
        for dependency in row["typeDeps"]:
            if dependency in rows and rows[dependency]["kind"] == "inductive":
                constructors[dependency].add(row["name"])

    reachable_rows: set[str] = set()
    work = deque(root_rows)
    while work:
        name = work.popleft()
        if name in reachable_rows:
            continue
        reachable_rows.add(name)
        row = rows.get(name)
        if row is None:
            continue
        work.extend(row["typeDeps"])
        work.extend(row["valueDeps"])
        if name in row_to_command:
            work.extend(source_ref_rows[row_to_command[name]])
        if row["kind"] == "inductive":
            work.extend(constructors[name])

    reachable_commands = {
        row_to_command[name] for name in reachable_rows if name in row_to_command
    }
    orphan_spans: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for module, names in orphan_rows.items():
        grouped: dict[tuple[int, int], list[str]] = defaultdict(list)
        for name in names:
            grouped[(rows[name]["startLine"], rows[name]["endLine"])].append(name)
        data = source_path(module).read_bytes()
        source_lines = data.splitlines(keepends=True)
        line_offsets = [0]
        for line in source_lines:
            line_offsets.append(line_offsets[-1] + len(line))
        for (start_line, end_line), span_rows in sorted(grouped.items()):
            if start_line <= 0 or end_line < start_line or end_line > len(source_lines):
                raise RuntimeError(f"invalid orphan span {module}:{start_line}-{end_line}")
            orphan_spans[module].append({
                "startLine": start_line,
                "endLine": end_line,
                "startOffset": line_offsets[start_line - 1],
                "endOffset": line_offsets[end_line],
                "rows": sorted(span_rows),
            })

    material_cache: dict[str, set[str]] = {}

    def material_commands(name: str, visiting: set[str] | None = None) -> set[str]:
        if name in material_cache:
            return material_cache[name]
        if name in row_to_command:
            result = {row_to_command[name]}
            material_cache[name] = result
            return result
        row = rows.get(name)
        if row is None:
            return set()
        visiting = set() if visiting is None else set(visiting)
        if name in visiting:
            return set()
        visiting.add(name)
        result: set[str] = set()
        for dependency in [*row["typeDeps"], *row["valueDeps"]]:
            result.update(material_commands(dependency, visiting))
        material_cache[name] = result
        return result

    command_type_deps: dict[str, set[str]] = defaultdict(set)
    command_value_deps: dict[str, set[str]] = defaultdict(set)
    for command_id in reachable_commands:
        command = commands[command_id]
        for row_name in command.rows:
            if row_name not in reachable_rows:
                continue
            for dependency in rows[row_name]["typeDeps"]:
                command_type_deps[command_id].update(material_commands(dependency))
            for dependency in rows[row_name]["valueDeps"]:
                command_value_deps[command_id].update(material_commands(dependency))
        for dependency in source_ref_rows[command_id]:
            command_value_deps[command_id].update(material_commands(dependency))
        command_type_deps[command_id].discard(command_id)
        command_value_deps[command_id].discard(command_id)
        command_type_deps[command_id].intersection_update(reachable_commands)
        command_value_deps[command_id].intersection_update(reachable_commands)

    def is_theorem_command(command_id: str) -> bool:
        command = commands[command_id]
        if command.anchor is None:
            return False
        anchor = rows[command.anchor]
        if anchor["kind"] == "theorem":
            return True
        source_kinds = {rows[name]["kind"] for name in command.rows if name in reachable_rows}
        return source_kinds == {"theorem"}

    def_commands = {cid for cid in reachable_commands if not is_theorem_command(cid)}
    simp_commands = {
        row_to_command[name] for name in simp_rows
        if name in row_to_command and row_to_command[name] in reachable_commands
        and is_theorem_command(row_to_command[name])
    }
    embedded_commands: set[str] = set(simp_commands)
    embed_work = deque(sorted(def_commands | simp_commands))
    seen_embed_sources: set[str] = set()
    while embed_work:
        command_id = embed_work.popleft()
        if command_id in seen_embed_sources:
            continue
        seen_embed_sources.add(command_id)
        for dependency in command_type_deps[command_id] | command_value_deps[command_id]:
            if is_theorem_command(dependency) and dependency not in embedded_commands:
                embedded_commands.add(dependency)
                embed_work.append(dependency)
            elif dependency in def_commands:
                embed_work.append(dependency)

    theorem_candidates = {
        cid for cid in reachable_commands
        if is_theorem_command(cid) and cid not in embedded_commands
    }
    mandatory_commands = {row_to_command[resolve(MAIN_TARGET)]}
    for row_name in requested_rows.values():
        if row_name in row_to_command:
            command_id = row_to_command[row_name]
            if command_id in theorem_candidates:
                mandatory_commands.add(command_id)

    source_text = {module: source_path(module).read_bytes() for module in modules}
    consumers: dict[str, set[str]] = defaultdict(set)
    for consumer in reachable_commands:
        for dependency in command_type_deps[consumer] | command_value_deps[consumer]:
            consumers[dependency].add(consumer)

    proof_lines: dict[str, int] = {}
    paper_signal: dict[str, bool] = {}
    cross_file_signal: dict[str, bool] = {}
    for command_id in theorem_candidates:
        command = commands[command_id]
        proof_lines[command_id] = (
            max(0, command.end.line - command.val_start.line) if command.val_start else 0)
        snippet = source_text[command.module][command.start.offset:command.end.offset].lower()
        paper_signal[command_id] = any(marker in snippet for marker in (
            b"paper", b"thm:", b"lem:", b"prop:", b"references/ldt-paper"))
        cross_file_signal[command_id] = any(
            commands[consumer].module != command.module for consumer in consumers[command_id])

    def is_private(command_id: str) -> bool:
        return any(rows[name]["isPrivate"] for name in commands[command_id].rows
                   if name in reachable_rows and rows[name]["kind"] == "theorem")

    nodes = set(mandatory_commands)
    for command_id in theorem_candidates:
        if is_private(command_id):
            continue
        lines = proof_lines[command_id]
        promoted = (commands[command_id].docstring is not None or
                    paper_signal[command_id] or cross_file_signal[command_id])
        if lines > 40 or (11 <= lines <= 40 and promoted):
            nodes.add(command_id)

    changed = True
    while changed:
        changed = False
        for node in list(nodes):
            for dependency in command_type_deps[node]:
                if dependency in theorem_candidates and dependency not in nodes:
                    nodes.add(dependency)
                    changed = True
        for command_id in theorem_candidates - nodes:
            if is_private(command_id) or not (11 <= proof_lines[command_id] <= 40):
                continue
            node_consumers = {consumer for consumer in consumers[command_id] if consumer in nodes}
            if len(node_consumers) >= 2:
                nodes.add(command_id)
                changed = True

    inline_commands = theorem_candidates - nodes
    classifications: dict[str, str] = {}
    for command_id in def_commands:
        classifications[command_id] = "def-material"
    for command_id in embedded_commands:
        classifications[command_id] = "def-embedded-theorem"
    for command_id in nodes:
        classifications[command_id] = "node"
    for command_id in inline_commands:
        classifications[command_id] = "inline-helper"

    deprivatized = {
        command_id for command_id in nodes
        if commands[command_id].private_tok is not None or is_private(command_id)
    }
    qpbt_exposed_commands: set[str] = set()
    for row_name in requested_rows.values():
        row = rows[row_name]
        if row["startLine"] != 0 or not row["isPrivate"]:
            continue
        candidates = {
            command_id for command_id in material_commands(row_name)
            if commands[command_id].private_tok is not None
        }
        if len(candidates) != 1:
            raise RuntimeError(
                f"cannot identify one private parent command for required companion {row_name}: "
                f"{sorted(candidates)}")
        qpbt_exposed_commands.update(candidates)

    cross_file_exposed_commands: set[str] = set()
    for consumer in nodes | inline_commands:
        for dependency in command_type_deps[consumer] | command_value_deps[consumer]:
            if (dependency in def_commands | embedded_commands and
                    commands[dependency].private_tok is not None):
                cross_file_exposed_commands.add(dependency)

    bundle_commands: dict[str, set[str]] = defaultdict(set)
    for command_id in def_commands | embedded_commands:
        bundle_commands[commands[command_id].module].add(command_id)
    for module in support_modules:
        bundle_commands[module]
    bundle_name = {module: "LIDT_" + module.replace(".", "_") for module in bundle_commands}
    bundle_dependencies: dict[str, set[str]] = defaultdict(set)
    for module, command_ids in bundle_commands.items():
        for command_id in command_ids:
            for dependency in command_type_deps[command_id] | command_value_deps[command_id]:
                dep_module = commands[dependency].module
                if dependency in def_commands or dependency in embedded_commands:
                    if dep_module != module:
                        bundle_dependencies[module].add(dep_module)
                elif dependency in nodes or dependency in inline_commands:
                    raise RuntimeError(
                        f"definition bundle {module} depends on non-embedded theorem "
                        f"{command_name(commands[dependency], rows)}")

    used_platform_names: dict[str, str] = {}
    platform_name: dict[str, str] = {}
    rename_map: dict[str, str] = {}
    for command_id in sorted(nodes):
        original = command_name(commands[command_id], rows)
        candidate = ascii_name("LIDT." + original)
        if candidate in used_platform_names and used_platform_names[candidate] != original:
            digest = hashlib.sha256(original.encode()).hexdigest()[:10]
            candidate = candidate + "_" + digest
        used_platform_names[candidate] = original
        platform_name[command_id] = candidate
        wrapped = "LIDT." + original
        if candidate != wrapped:
            rename_map[wrapped] = candidate

    node_dependencies: dict[str, set[str]] = defaultdict(set)
    node_inline_closure: dict[str, set[str]] = defaultdict(set)
    node_def_modules: dict[str, set[str]] = defaultdict(set)
    node_type_nodes: dict[str, set[str]] = defaultdict(set)
    for node in nodes:
        work_commands = deque(sorted(command_type_deps[node] | command_value_deps[node]))
        seen_commands: set[str] = set()
        while work_commands:
            dependency = work_commands.popleft()
            if dependency == node or dependency in seen_commands:
                continue
            seen_commands.add(dependency)
            if dependency in def_commands or dependency in embedded_commands:
                node_def_modules[node].add(commands[dependency].module)
            elif dependency in nodes:
                node_dependencies[node].add(dependency)
            elif dependency in inline_commands:
                node_inline_closure[node].add(dependency)
                work_commands.extend(command_type_deps[dependency])
                work_commands.extend(command_value_deps[dependency])
        for dependency in command_type_deps[node]:
            if dependency in nodes:
                node_type_nodes[node].add(dependency)
            elif dependency in inline_commands:
                raise RuntimeError(
                    f"node statement for {command_name(commands[node], rows)} depends on inline theorem "
                    f"{command_name(commands[dependency], rows)}")

    node_order = topo_sort(nodes, node_dependencies)

    project_imports = {module: parse_imports(module) for module in manifest_modules}
    project_module_set = set(manifest_modules)
    external_import_cache: dict[str, set[str]] = {}

    def external_imports(module: str, visiting: set[str] | None = None) -> set[str]:
        if module in external_import_cache:
            return external_import_cache[module]
        visiting = set() if visiting is None else set(visiting)
        if module in visiting:
            return set()
        visiting.add(module)
        result: set[str] = set()
        for imported in project_imports[module]:
            if imported in project_module_set:
                result.update(external_imports(imported, visiting))
            else:
                result.add(imported)
        external_import_cache[module] = result
        return result

    project_closure_cache: dict[str, set[str]] = {}

    def project_closure(module: str, visiting: set[str] | None = None) -> set[str]:
        if module in project_closure_cache:
            return project_closure_cache[module]
        visiting = set() if visiting is None else set(visiting)
        if module in visiting:
            return set()
        visiting.add(module)
        result: set[str] = set()
        for imported in project_imports[module]:
            if imported in project_module_set:
                result.add(imported)
                result.update(project_closure(imported, visiting))
        project_closure_cache[module] = result
        return result

    for module in bundle_commands:
        for imported in project_closure(module):
            if imported in bundle_commands and imported != module:
                bundle_dependencies[module].add(imported)
    for node in nodes:
        relevant_modules = {commands[node].module}
        relevant_modules.update(commands[helper].module for helper in node_inline_closure[node])
        for module in relevant_modules:
            for imported in project_closure(module):
                if imported in bundle_commands:
                    node_def_modules[node].add(imported)

    definition_order = topo_sort(bundle_commands, bundle_dependencies)

    module_metadata = {
        module: {
            "source": str(source_path(module).relative_to(ROOT)),
            "projectImports": [name for name in project_imports[module]
                               if name in project_module_set],
            "supportDefinitionModules": sorted(
                imported for imported in project_closure(module)
                if imported in support_modules and imported in bundle_commands),
            "externalImports": sorted(external_imports(module)),
        }
        for module in modules
    }

    commands_json: dict[str, Any] = {}
    for command_id in sorted(reachable_commands):
        command = commands[command_id]
        entry = command.as_json()
        entry.update({
            "classification": classifications[command_id],
            "proofLines": proof_lines.get(command_id),
            "isPrivate": is_private(command_id) if is_theorem_command(command_id) else False,
            "deprivatize": command_id in deprivatized,
            "deprivatizeForQpbt": command_id in qpbt_exposed_commands,
            "typeCommandDeps": sorted(command_type_deps[command_id]),
            "valueCommandDeps": sorted(command_value_deps[command_id]),
        })
        commands_json[command_id] = entry

    node_json: dict[str, Any] = {}
    for command_id in sorted(nodes):
        command = commands[command_id]
        original = command_name(command, rows)
        node_json[command_id] = {
            "originalName": original,
            "platformName": platform_name[command_id],
            "slug": platform_name[command_id].replace(".", "_"),
            "module": command.module,
            "source": module_metadata[command.module]["source"],
            "sourceLines": [command.start.line, command.end.line],
            "proofLines": proof_lines[command_id],
            "definitionModules": sorted(node_def_modules[command_id]),
            "theoremDependencies": sorted(node_dependencies[command_id]),
            "typeTheoremDependencies": sorted(node_type_nodes[command_id]),
            "inlineCommands": sorted(node_inline_closure[command_id]),
            "deprivatize": command_id in deprivatized,
            "isMainTarget": original == MAIN_TARGET,
            "isQpbtRequired": original in requested_rows or any(
                row_name in requested_rows.values() for row_name in command.rows),
        }

    def bundle_source_lines(module: str) -> list[int]:
        starts = [commands[command_id].start.line for command_id in bundle_commands[module]]
        ends = [commands[command_id].end.line for command_id in bundle_commands[module]]
        starts.extend(span["startLine"] for span in orphan_spans.get(module, []))
        ends.extend(span["endLine"] for span in orphan_spans.get(module, []))
        if not starts:
            return [1, len(source_path(module).read_text(encoding="utf-8").splitlines())]
        return [min(starts), max(ends)]

    definitions_json = {
        module: {
            "definitionName": bundle_name[module],
            "slug": bundle_name[module],
            "source": module_metadata[module]["source"],
            "sourceLines": bundle_source_lines(module),
            "commands": sorted(bundle_commands[module], key=lambda cid: commands[cid].index),
            "definitionDependencies": sorted(bundle_dependencies[module]),
            "deprivatizeCommands": sorted(
                bundle_commands[module] &
                (qpbt_exposed_commands | cross_file_exposed_commands)),
        }
        for module in sorted(bundle_commands)
    }

    plan = {
        "schemaVersion": 1,
        "sourceCommit": SOURCE_SHA,
        "uploadNamespace": "LIDT",
        "tag": "LIDT",
        "mainTarget": MAIN_TARGET,
        "counts": {
            "graphRows": len(graph_rows),
            "participatingModules": len(manifest_modules),
            "rootRows": len(root_rows),
            "reachableRows": len(reachable_rows),
            "spanlessReachableRows": sum(rows[name]["startLine"] == 0 for name in reachable_rows
                                         if name in rows),
            "reachableCommands": len(reachable_commands),
            "definitionBundles": len(bundle_commands),
            "defMaterialCommands": len(def_commands),
            "defEmbeddedTheoremCommands": len(embedded_commands),
            "theoremNodes": len(nodes),
            "inlineHelpers": len(inline_commands),
            "deprivatizedNodes": len(deprivatized),
            "qpbtExposedCommands": len(qpbt_exposed_commands),
            "crossFileExposedCommands": len(cross_file_exposed_commands),
            "renamedNodes": len(rename_map),
            "qpbtRequired": len(needs),
            "simpDeclarations": len(simp_rows),
            "sourceReferenceEdges": sum(len(deps) for deps in source_ref_rows.values()),
        },
        "roots": sorted(set(root_rows)),
        "reachableRows": sorted(reachable_rows),
        "rowToCommand": row_to_command,
        "commands": commands_json,
        "modules": module_metadata,
        "orphanSpans": orphan_spans,
        "definitions": definitions_json,
        "nodes": node_json,
        "definitionOrder": definition_order,
        "nodeOrder": node_order,
        "renameMap": rename_map,
        "qpbt": {
            "requested": needs,
            "resolvedRows": requested_rows,
        },
    }

    PLAN.parent.mkdir(parents=True, exist_ok=True)
    PLAN.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tsv_lines = ["class\toriginal_name\tplatform_name\tmodule\tproof_lines\tflags"]
    for module in definition_order:
        tsv_lines.append(
            f"definition\t{module}\t{bundle_name[module]}\t{module}\t-\t-")
    for command_id in node_order:
        node = node_json[command_id]
        flags = ",".join(flag for flag, enabled in (
            ("main", node["isMainTarget"]),
            ("qpbt", node["isQpbtRequired"]),
            ("deprivatized", node["deprivatize"]),
        ) if enabled)
        tsv_lines.append(
            f"theorem\t{node['originalName']}\t{node['platformName']}\t{node['module']}\t"
            f"{node['proofLines']}\t{flags or '-'}")
    PLAN_TSV.write_text("\n".join(tsv_lines) + "\n", encoding="utf-8")

    rename_lines = ["wrapped_source_name\tplatform_name"]
    rename_lines.extend(f"{source}\t{target}" for source, target in sorted(rename_map.items()))
    RENAME_TSV.write_text("\n".join(rename_lines) + "\n", encoding="utf-8")

    qpbt_lines = [
        "original_name\tplatform_name\timport_module\tentry_kind\ttheorem_id\tnote"
    ]
    mapped_names: set[str] = set()
    for module in definition_order:
        qpbt_lines.append(
            f"{module}\t{bundle_name[module]}\tDefinitions.Def_{bundle_name[module]}\t"
            "definition\t\tmodule bundle")
        mapped_names.add(module)
    for command_id in node_order:
        node = node_json[command_id]
        qpbt_lines.append(
            f"{node['originalName']}\t{node['platformName']}\t"
            f"Theorems.Thm_{node['slug']}\ttheorem\t\tuploaded theorem node")
        mapped_names.add(node["originalName"])
    for original in needs:
        if original in mapped_names:
            continue
        row_name = requested_rows[original]
        row = rows[row_name]
        if row_name in row_to_command:
            command_id = row_to_command[row_name]
            classification = classifications[command_id]
            if classification == "node":
                platform = platform_name[command_id]
                import_module = "Theorems.Thm_" + platform.replace(".", "_")
                kind = "theorem"
            else:
                module = commands[command_id].module
                platform = PLATFORM_NAME_OVERRIDES.get(original, "LIDT." + row["userName"])
                import_module = "Definitions.Def_" + bundle_name[module]
                kind = classification
            note = (
                "anonymous instance relocated by generated-module hygiene"
                if original in PLATFORM_NAME_OVERRIDES else ""
            )
        else:
            module = row["module"]
            if module not in bundle_name:
                raise RuntimeError(f"spanless QPBT declaration has no bundle: {original}")
            platform = PLATFORM_NAME_OVERRIDES.get(original, "LIDT." + row["userName"])
            import_module = "Definitions.Def_" + bundle_name[module]
            kind = "generated-companion"
            note = "regenerated by its source declaration"
            if row["isPrivate"]:
                platform = "LIDT." + row["userName"]
                note = "regenerated from a parent declaration made public in the upload bundle"
        qpbt_lines.append(
            f"{original}\t{platform}\t{import_module}\t{kind}\t\t{note}")
    if args.write_qpbt_names:
        QPBT_NAMES.parent.mkdir(parents=True, exist_ok=True)
        QPBT_NAMES.write_text("\n".join(qpbt_lines) + "\n", encoding="utf-8")

    print(json.dumps(plan["counts"], sort_keys=True))
    print(f"wrote {PLAN.relative_to(ROOT)}")
    print(f"wrote {PLAN_TSV.relative_to(ROOT)}")
    print(f"wrote {RENAME_TSV.relative_to(ROOT)}")
    if args.write_qpbt_names:
        print(f"wrote {QPBT_NAMES}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
