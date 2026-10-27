#!/usr/bin/env python3
"""Generate the namespaced Prove2Me tree by skeleton subtraction."""

from __future__ import annotations

import json
import re
import shutil
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
SKETCH_DIR = ROOT / "prove2me" / "extracted" / "sketch"
SYNTAX_DIR = ROOT / "prove2me" / "extracted" / "syntax"
OUT = ROOT / "prove2me" / "platform"
PAYLOADS = ROOT / "prove2me" / "generated" / "payloads.json"
SOURCE_REPO = "https://github.com/LionSR/MIPStarRE"
SOURCE_SHA = "f382c801026f53a9efc260fdee707cb35e0adb15"
CREDIT = (
    "Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji "
    "(arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, "
    "Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982)."
)
SECTION_LINE = re.compile(
    r"(?:(?:noncomputable|meta|private|public)\s+)*section(?:\s+[A-Za-z0-9_']+)?"
)
SUPPLEMENTAL_COMPANIONS = {
    "MIPStarRE.Quantum.FiniteHilbert": r"""
/- The QPBT consumer reaches Mathlib's compiler-generated equation theorem for
`Matrix.toEuclideanLin`. Compiler companions are normally regenerated with
their parent declaration, but this parent belongs to Mathlib rather than the
vendored project. Re-export the exact equation under the upload namespace. -/
namespace Matrix.toEuclideanLin

universe u v w

@[defeq] theorem eq_1
    {𝕜 : Type u} [RCLike 𝕜] {m : Type v} {n : Type w}
    [Fintype n] [DecidableEq n] :
    @_root_.Matrix.toEuclideanLin 𝕜 _ m n _ _ =
      @_root_.Matrix.toLpLin m n 𝕜 _ _ _ 2 2 := by
  exact _root_.Matrix.toEuclideanLin.eq_1

end Matrix.toEuclideanLin
""".strip(),
}
PLATFORM_MODULE_BODIES = {
    "MIPStarRE.LDT.Tactic.AvgCongr": r"""
/- Prove2Me definition submissions do not admit custom parser or tactic
registrations. Reachable `avg_congr` invocations are lowered at their exact
parser ranges. The QPBT consumer separately reaches the compiler-generated
`SizeOf` instance for this source-private helper, so retain its parent type. -/
inductive AvgCongrPeelKind where
  | plain
  | onSupport
""".strip(),
    "MIPStarRE.LDT.Tactic.QuantumNonneg": r"""
/- Prove2Me definition submissions do not admit custom parser or macro
registrations. Every reachable `quantum_nonneg` invocation is lowered at its
exact parser range; this empty compatibility bundle preserves source imports. -/
""".strip(),
}
PLATFORM_TACTIC_REPLACEMENTS = {
    ("MIPStarRE.LDT.Preliminaries.Defs", 134):
        "exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg "
        "((A q).outcome_pos a) ((B q).outcome_pos a)",
    ("MIPStarRE.LDT.Preliminaries.Defs", 160):
        "exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg "
        "((A q).total_nonneg) ((B q).outcome_pos a)",
    ("MIPStarRE.LDT.Preliminaries.Defs", 186):
        "exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg "
        "((A q).outcome_pos a) ((B q).outcome_pos a)",
    ("MIPStarRE.LDT.Preliminaries.Defs", 211):
        "exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg "
        "((A q).total_nonneg) ((B q).outcome_pos a)",
    ("MIPStarRE.LDT.Preliminaries.ComparisonCore", 260):
        "exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd ψ "
        "(_root_.LIDT.MIPStarRE.LDT.opTensor X Y) "
        "(_root_.LIDT.MIPStarRE.LDT.opTensor_nonneg hX hY)",
    ("MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Axis", 136):
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; "
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u",
    ("MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Axis", 243):
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro i; rfl",
    ("MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic", 528):
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; "
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u",
    ("MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic", 569):
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; "
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u",
    ("MIPStarRE.LDT.MainInductionStep.Theorems.PastingAssembly.Basic", 615):
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; "
        "refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u",
}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def source_bytes(module: str) -> bytes:
    return source_path(module).read_bytes()


def header_end(data: bytes) -> int:
    offset = 0
    end = 0
    for line in data.splitlines(keepends=True):
        stripped = line.strip()
        if (not stripped or stripped == b"module" or stripped.startswith(b"--") or
                re.fullmatch(rb"(?:(?:public|meta)\s+)*import\s+[^\s]+", stripped)):
            offset += len(line)
            end = offset
            continue
        break
    return end


def apply_edits(data: bytes, edits: Iterable[tuple[int, int, bytes]]) -> bytes:
    result = data
    ordered = sorted(edits, key=lambda edit: (edit[0], edit[1]), reverse=True)
    previous_start = len(data) + 1
    for start, end, replacement in ordered:
        if end > previous_start:
            raise RuntimeError(f"overlapping edits at byte range {start}:{end}")
        result = result[:start] + replacement + result[end:]
        previous_start = start
    return result


def code_mask_bytes(data: bytes) -> bytes:
    output = bytearray(data)
    index = 0
    block_depth = 0
    in_string = False
    while index < len(data):
        if block_depth:
            if data.startswith(b"/-", index):
                block_depth += 1
                output[index:index + 2] = b"  "
                index += 2
            elif data.startswith(b"-/", index):
                block_depth -= 1
                output[index:index + 2] = b"  "
                index += 2
            else:
                if data[index] != 0x0A:
                    output[index] = 0x20
                index += 1
        elif in_string:
            if data[index] == 0x5C and index + 1 < len(data):
                output[index:index + 2] = b"  "
                index += 2
            elif data[index] == 0x22:
                in_string = False
                output[index] = 0x20
                index += 1
            else:
                if data[index] != 0x0A:
                    output[index] = 0x20
                index += 1
        elif data.startswith(b"--", index):
            newline = data.find(b"\n", index)
            end = len(data) if newline == -1 else newline
            output[index:end] = b" " * (end - index)
            index = end
        elif data.startswith(b"/-", index):
            block_depth = 1
            output[index:index + 2] = b"  "
            index += 2
        elif data[index] == 0x22:
            in_string = True
            output[index] = 0x20
            index += 1
        else:
            index += 1
    return bytes(output)


def self_reference_edits(
    data: bytes, command: dict[str, Any], original_name: str, binding: str,
) -> list[tuple[int, int, bytes]]:
    if command["valStart"] is None or command["nameText"] is None:
        return []
    start = command["valStart"]["offset"]
    end = command["declEnd"]["offset"]
    masked = code_mask_bytes(data)
    needle = command["nameText"].encode("utf-8")
    edits: list[tuple[int, int, bytes]] = []
    index = start
    while True:
        found = masked.find(needle, index, end)
        if found == -1:
            break
        after = found + len(needle)
        before_byte = masked[found - 1] if found > 0 else None
        after_byte = masked[after] if after < len(masked) else None
        before_ident = before_byte is not None and (
            chr(before_byte).isalnum() or before_byte in b"_'" or before_byte >= 0x80)
        after_ident = after_byte is not None and (
            chr(after_byte).isalnum() or after_byte in b"_'" or after_byte >= 0x80)
        if not before_ident and not after_ident:
            token_start = found
            while token_start > start:
                byte = masked[token_start - 1]
                if chr(byte).isalnum() or byte in b"_'." or byte >= 0x80:
                    token_start -= 1
                else:
                    break
            token = data[token_start:after].decode("utf-8")
            if token == command["nameText"] or token.removeprefix("_root_.") == original_name:
                edits.append((token_start, after, binding.encode()))
        index = after
    return edits


def range_offsets(value: dict[str, Any] | None) -> tuple[int, int] | None:
    if value is None:
        return None
    return value["start"]["offset"], value["end"]["offset"]


def import_lines(imports: Iterable[str]) -> str:
    names = sorted(set(imports))
    return "\n".join(f"import {name}" for name in names) + ("\n\n" if names else "")


def scoped_notation_preamble(*parts: str | bytes) -> str:
    encoded = [part.encode("utf-8") if isinstance(part, str) else part for part in parts]
    return "open scoped _root_.Matrix\n\n" if any("ᴴ".encode() in part for part in encoded) else ""


def root_qualify_matrix_scopes(text: str) -> str:
    def qualify(match: re.Match[str]) -> str:
        scopes = re.sub(r"(?<![A-Za-z0-9_'.])Matrix(?=\.|\b)", "_root_.Matrix", match.group(2))
        return match.group(1) + scopes

    return re.sub(r"(?m)^(\s*open scoped\s+)([^\n]+)$", qualify, text)


def filter_explicit_project_opens(text: str, project_names: set[str]) -> str:
    pattern = re.compile(
        r"(?m)^([ \t]*open[ \t]+([A-Za-z0-9_'.]+)[ \t]*(?:\n[ \t]*)?)\(([^)]*)\)"
    )

    def filter_names(match: re.Match[str]) -> str:
        namespace = match.group(2).removeprefix("_root_.")
        if not namespace.startswith("MIPStarRE."):
            return match.group(0)
        names = match.group(3).split()
        kept = [name for name in names if f"{namespace}.{name}" in project_names]
        if not kept:
            return ""
        return match.group(1) + "(" + " ".join(kept) + ")"

    return pattern.sub(filter_names, text)


def inline_module_order(
    plan: dict[str, Any], inline_by_module: dict[str, set[str]],
) -> list[str]:
    selected = {command_id for ids in inline_by_module.values() for command_id in ids}
    dependencies: dict[str, set[str]] = {module: set() for module in inline_by_module}
    for module, command_ids in inline_by_module.items():
        for command_id in command_ids:
            command = plan["commands"][command_id]
            for dependency in command["typeCommandDeps"] + command["valueCommandDeps"]:
                if dependency in selected:
                    dependency_module = plan["commands"][dependency]["module"]
                    if dependency_module != module:
                        dependencies[module].add(dependency_module)
    order: list[str] = []
    remaining = set(inline_by_module)
    while remaining:
        ready = sorted(module for module in remaining if dependencies[module] <= set(order))
        if not ready:
            raise RuntimeError(f"cyclic inline helper modules: {sorted(remaining)}")
        order.extend(ready)
        remaining.difference_update(ready)
    return order


def source_namespace_paths(module: str) -> set[str]:
    paths: set[str] = set()
    current: list[str] = []
    frames: list[tuple[str, int]] = []
    for raw_line in source_path(module).read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        namespace_match = re.fullmatch(r"namespace\s+([A-Za-z0-9_'.]+)", line)
        if namespace_match:
            pieces = namespace_match.group(1).split(".")
            current.extend(pieces)
            frames.append(("namespace", len(pieces)))
            paths.add(".".join(current))
        elif line == "@[expose] public section" or SECTION_LINE.fullmatch(line):
            frames.append(("section", 0))
        elif re.fullmatch(r"end(?:\s+[A-Za-z0-9_'.]+)?", line) and frames:
            kind, count = frames.pop()
            if kind == "namespace" and count:
                del current[-count:]
    return paths


def project_import_closure(plan: dict[str, Any], module: str) -> set[str]:
    result: set[str] = set()
    work = list(plan["modules"][module]["projectImports"])
    while work:
        imported = work.pop()
        if imported in result or imported not in plan["modules"]:
            continue
        result.add(imported)
        work.extend(plan["modules"][imported]["projectImports"])
    return result


def namespace_stubs(plan: dict[str, Any], modules: Iterable[str], *, wrapped: bool) -> str:
    paths: set[str] = set()
    for module in modules:
        candidates = project_import_closure(plan, module) | {module}
        for candidate in candidates:
            if candidate not in plan["definitions"]:
                paths.update(source_namespace_paths(candidate))
    if not paths:
        return ""
    prefix = "LIDT." if wrapped else ""
    return "\n".join(
        f"namespace {prefix}{path}\nend {prefix}{path}" for path in sorted(paths)
    ) + "\n\n"


def facts_for(module: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    facts = read_jsonl(SKETCH_DIR / f"{module}.jsonl")
    return ([fact for fact in facts if fact["kind"] == "decl"],
            [fact for fact in facts if fact["kind"] == "ref"])


def syntax_facts_for(module: str) -> list[dict[str, Any]]:
    path = SYNTAX_DIR / f"{module}.jsonl"
    return read_jsonl(path) if path.is_file() else []


def syntax_identifier_target(name: str) -> str | None:
    if name.startswith("_root_.MIPStarRE."):
        return "_root_.LIDT." + name.removeprefix("_root_.")
    if name in {
        "MIPStarRE.LDT.avgOver_congr",
        "MIPStarRE.LDT.avgOver_congr_on_support",
    }:
        return "_root_.LIDT." + name
    return None


def syntax_fact_target(module: str, fact: dict[str, Any]) -> str | None:
    if fact["kind"] == "platformTactic":
        key = (module, fact["start"]["line"] + 1)
        if key not in PLATFORM_TACTIC_REPLACEMENTS:
            raise RuntimeError(f"missing platform tactic lowering for {key}: {fact['name']}")
        return PLATFORM_TACTIC_REPLACEMENTS[key]
    return syntax_identifier_target(fact["name"])


def unclosed_module_sections(body: bytes) -> int:
    module_scope_sections = {
        "@[expose] public section",
        "public meta section",
    }
    frames: list[str] = []
    for raw_line in body.decode("utf-8").splitlines():
        line = raw_line.strip()
        if line in module_scope_sections:
            frames.append("module")
        elif re.fullmatch(r"namespace\s+[A-Za-z0-9_'.]+", line):
            frames.append("scope")
        elif SECTION_LINE.fullmatch(line):
            frames.append("scope")
        elif re.fullmatch(r"end(?:\s+[A-Za-z0-9_'.]+)?", line) and frames:
            frames.pop()
    return sum(frame == "module" for frame in frames)


def command_key(fact: dict[str, Any]) -> tuple[int, int]:
    return fact["declStart"]["offset"], fact["declEnd"]["offset"]


def plan_command_key(command: dict[str, Any]) -> tuple[int, int]:
    return command["declStart"]["offset"], command["declEnd"]["offset"]


def ref_target(
    const: str,
    rename_map: dict[str, str],
    *,
    source_token: str | None = None,
    project_names: set[str] | None = None,
) -> str | None:
    direct = rename_map.get("LIDT." + const)
    if direct:
        return "_root_." + direct
    for wrapped, target in rename_map.items():
        original = wrapped.removeprefix("LIDT.")
        if const.endswith("." + original):
            return "_root_." + target
    if (source_token is not None and source_token.startswith("_root_.") and
            project_names is not None and const in project_names):
        return "_root_.LIDT." + source_token.removeprefix("_root_.")
    return None


def skeleton_body(
    module: str,
    selected_keys: set[tuple[int, int]],
    rename_map: dict[str, str],
    *,
    project_names: set[str],
    deprivatize_keys: set[tuple[int, int]] | None = None,
    orphan_spans: list[dict[str, Any]] | None = None,
    keep_orphans: bool = False,
) -> bytes:
    data = source_bytes(module)
    body_start = header_end(data)
    decls, refs = facts_for(module)
    edits: list[tuple[int, int, bytes]] = []
    deleted_keys: set[tuple[int, int]] = set()
    for fact in decls:
        start, end = command_key(fact)
        if (start, end) not in selected_keys:
            edits.append((start, end, b""))
            deleted_keys.add((start, end))
    if not keep_orphans:
        for span in orphan_spans or []:
            edits.append((span["startOffset"], span["endOffset"], b""))
    deprivatize_keys = deprivatize_keys or set()
    for fact in decls:
        key = command_key(fact)
        if key in selected_keys and key in deprivatize_keys:
            private_range = range_offsets(fact["privateTok"])
            if private_range:
                edits.append((*private_range, b""))
    for ref in refs:
        start = ref["start"]["offset"]
        end = ref["end"]["offset"]
        if any(a <= start and end <= b for a, b in deleted_keys):
            continue
        token = data[start:end].decode("utf-8")
        target = ref_target(
            ref["const"], rename_map, source_token=token, project_names=project_names)
        if target:
            edits.append((start, end, target.encode()))
    ref_ranges = {(ref["start"]["offset"], ref["end"]["offset"]) for ref in refs}
    for fact in syntax_facts_for(module):
        start = fact["start"]["offset"]
        end = fact["end"]["offset"]
        if any(a <= start and end <= b for a, b in deleted_keys):
            continue
        if (start, end) in ref_ranges:
            continue
        target = syntax_fact_target(module, fact)
        if target:
            edits.append((start, end, target.encode()))
    try:
        transformed = apply_edits(data, edits)
    except RuntimeError as error:
        raise RuntimeError(f"{module}: {error}") from error
    body = transformed[body_start:]
    open_module_sections = unclosed_module_sections(body)
    if open_module_sections:
        body = body.rstrip() + b"\n\n" + b"end\n" * open_module_sections
    return body


def context_before(
    module: str, target_start: int, orphan_spans: list[dict[str, Any]],
) -> bytes:
    data = source_bytes(module)
    body_start = header_end(data)
    decls, _ = facts_for(module)
    prefix = data[body_start:target_start]
    edits: list[tuple[int, int, bytes]] = []
    for fact in decls:
        start, end = command_key(fact)
        if end <= target_start:
            edits.append((start - body_start, end - body_start, b""))
        elif start < target_start:
            raise RuntimeError(f"target starts inside another declaration in {module}")
    for span in orphan_spans:
        start, end = span["startOffset"], span["endOffset"]
        if end <= target_start:
            edits.append((start - body_start, end - body_start, b""))
        elif start < target_start:
            raise RuntimeError(f"target starts inside generated material in {module}")
    return apply_edits(prefix, edits)


def platformize_context(context: bytes) -> str:
    text = context.decode("utf-8")
    lines = text.splitlines()
    frames: list[tuple[str, list[str], int]] = []
    closed_ranges: list[tuple[int, int]] = []
    namespace_at_line: dict[int, list[str]] = {}
    section_at_line: set[int] = set()
    for index, line in enumerate(lines):
        stripped = line.strip()
        namespace_match = re.fullmatch(r"namespace\s+([A-Za-z0-9_'.]+)", stripped)
        section_match = re.fullmatch(r"section(?:\s+[A-Za-z0-9_']+)?", stripped)
        end_match = re.fullmatch(r"end(?:\s+[A-Za-z0-9_'.]+)?", stripped)
        if namespace_match:
            pieces = namespace_match.group(1).split(".")
            frames.append(("namespace", pieces, index))
            namespace_at_line[index] = pieces
        elif section_match:
            frames.append(("section", [], index))
            section_at_line.add(index)
        elif end_match and frames:
            _, _, start = frames.pop()
            closed_ranges.append((start, index))
    active_starts = {start for _, _, start in frames}

    def is_closed(index: int) -> bool:
        return any(start <= index <= end for start, end in closed_ranges)

    output: list[str] = ["open LIDT"]
    active_namespaces: list[list[str]] = []
    for index, line in enumerate(lines):
        if is_closed(index):
            continue
        stripped = line.strip()
        if index in namespace_at_line and index in active_starts:
            active_namespaces.append(namespace_at_line[index])
            full = [part for names in active_namespaces for part in names]
            output.append("open LIDT." + ".".join(full))
        elif index in section_at_line and index in active_starts:
            continue
        else:
            output.append(line)
    value = "\n".join(output).strip()
    return value + ("\n" if value else "")


def fact_for_command(module: str, command: dict[str, Any]) -> dict[str, Any]:
    key = plan_command_key(command)
    decls, _ = facts_for(module)
    matches = [fact for fact in decls if command_key(fact) == key]
    if len(matches) != 1:
        raise RuntimeError(f"cannot resolve command fact {command['commandId']}")
    return matches[0]


def binding_ref(
    module: str,
    command: dict[str, Any],
    original_name: str,
) -> dict[str, Any]:
    data = source_bytes(module)
    _, refs = facts_for(module)
    start, end = plan_command_key(command)
    name_text = command["nameText"] or original_name.rsplit(".", 1)[-1]
    candidates: list[dict[str, Any]] = []
    for ref in refs:
        ref_start = ref["start"]["offset"]
        ref_end = ref["end"]["offset"]
        if not (start <= ref_start < ref_end <= end):
            continue
        token = data[ref_start:ref_end].decode("utf-8")
        const = ref["const"]
        if (const == original_name or const.endswith("." + original_name) or
                token == name_text or token.endswith("." + name_text)):
            candidates.append(ref)
    if not candidates:
        raise RuntimeError(f"no binding reference for {original_name} in {module}")
    candidates.sort(key=lambda ref: ref["start"]["offset"])
    return candidates[0]


def solution_head_edits(
    data: bytes,
    command: dict[str, Any],
    binding_range: tuple[int, int],
) -> list[tuple[int, int, bytes]]:
    """Normalize the source declaration head to Prove2Me's `theorem solution`."""
    start = command["declStart"]["offset"]
    doc_range = range_offsets(command["docstring"])
    head_start = doc_range[1] if doc_range else start
    head_end = binding_range[0]
    head = data[head_start:head_end]
    keyword_matches = list(re.finditer(rb"(?<![A-Za-z0-9_'])(theorem|lemma)(?![A-Za-z0-9_'])", head))
    if len(keyword_matches) != 1:
        raise RuntimeError(
            f"expected one theorem/lemma keyword in declaration head: {head!r}")
    keyword = keyword_matches[0]
    edits: list[tuple[int, int, bytes]] = []
    keyword_start = head_start + keyword.start()
    keyword_end = head_start + keyword.end()
    if keyword.group() == b"lemma":
        edits.append((keyword_start, keyword_end, b"theorem"))

    prefix = head[:keyword.start()]
    protected_matches = list(
        re.finditer(rb"(?<![A-Za-z0-9_'])protected[ \t]+$", prefix))
    if protected_matches:
        protected = protected_matches[-1]
        edits.append((head_start + protected.start(), keyword_start, b""))
    return edits


def extract_command(
    plan: dict[str, Any],
    command_id: str,
    binding: str,
    *,
    stub: bool,
) -> tuple[str, list[str]]:
    command = plan["commands"][command_id]
    node = plan["nodes"][command_id]
    module = command["module"]
    data = source_bytes(module)
    start, end = plan_command_key(command)
    cutoff = command["valStart"]["offset"] if stub else end
    edits: list[tuple[int, int, bytes]] = []
    doc_range = range_offsets(command["docstring"])
    if doc_range:
        edits.append((*doc_range, b""))
    private_range = range_offsets(command["privateTok"])
    if private_range:
        edits.append((*private_range, b""))
    binding_fact = binding_ref(module, command, node["originalName"])
    binding_range = (binding_fact["start"]["offset"], binding_fact["end"]["offset"])
    edits.append((*binding_range, binding.encode()))
    if binding == "solution":
        edits.extend(solution_head_edits(data, command, binding_range))
        edits.extend(self_reference_edits(data, command, node["originalName"], binding))
    _, refs = facts_for(module)
    project_names = set(plan["reachableRows"])
    for ref in refs:
        ref_start = ref["start"]["offset"]
        ref_end = ref["end"]["offset"]
        if (ref_start, ref_end) == binding_range or not (start <= ref_start < ref_end <= cutoff):
            continue
        token = data[ref_start:ref_end].decode("utf-8")
        if (ref["const"] == node["originalName"] or
                ref["const"].endswith("." + node["originalName"])):
            target = binding
        else:
            target = ref_target(
                ref["const"], plan["renameMap"], source_token=token,
                project_names=project_names)
            is_field_projection = ref_start > 0 and data[ref_start - 1:ref_start] == b"."
            if (target is None and ref["const"] in project_names and
                    not ref["const"].startswith("_private.") and not is_field_projection):
                target = "_root_.LIDT." + ref["const"]
        if target:
            edits.append((ref_start, ref_end, target.encode()))
    ref_ranges = {(ref["start"]["offset"], ref["end"]["offset"]) for ref in refs}
    for fact in syntax_facts_for(module):
        fact_start = fact["start"]["offset"]
        fact_end = fact["end"]["offset"]
        if not (start <= fact_start < fact_end <= cutoff):
            continue
        if (fact_start, fact_end) in ref_ranges:
            continue
        target = syntax_fact_target(module, fact)
        if target:
            edits.append((fact_start, fact_end, target.encode()))
    segment = apply_edits(data[start:cutoff], [
        (edit_start - start, edit_end - start, replacement)
        for edit_start, edit_end, replacement in edits
        if start <= edit_start and edit_end <= cutoff
    ]).decode("utf-8")
    if stub:
        segment = segment.rstrip() + " := by sorry"
    hoisted: list[str] = []
    while True:
        include = re.match(r"\s*include\s+([^\n]+?)\s+in\s*\n?", segment)
        if not include:
            break
        hoisted.append("include " + include.group(1).strip())
        segment = segment[include.end():]
    return segment.strip() + "\n", hoisted


def title_from_name(name: str) -> str:
    leaf = name.rsplit(".", 1)[-1]
    words = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", leaf).replace("_", " ").split()
    return " ".join(word.capitalize() if word.islower() else word for word in words)[:200]


def clean_docstring(module: str, command: dict[str, Any]) -> str:
    doc_range = range_offsets(command["docstring"])
    if not doc_range:
        return ""
    data = source_bytes(module)
    value = data[doc_range[0]:doc_range[1]].decode("utf-8")
    value = re.sub(r"^/--\s*", "", value)
    value = re.sub(r"\s*-/\s*$", "", value)
    value = re.sub(r"\*\*(?:Source|Paper origin|Unfaithful|Local fix|Scope restriction):\**", "", value)
    return value.strip()


def theorem_natural(node: dict[str, Any], command: dict[str, Any]) -> str:
    doc = clean_docstring(command["module"], command)
    summary = doc.split("\n\n", 1)[0] if doc else title_from_name(node["originalName"])
    summary = re.sub(r"`([^`]+)`", r"\1", summary)
    return (
        f"{summary}\n\n"
        "Under the parameters, finite-dimensional spaces, typeclass assumptions, and hypotheses "
        "specified in the formal statement, the asserted conclusion is:\n\n"
        "$$\\text{the proposition stated by this LIDT declaration holds.}$$\n\n"
        "This result is an importable step in the formal dependency graph for the quantum "
        "soundness proof of the classical low individual degree test.\n\n"
        f"{CREDIT}\n\n"
        f"**Formalization Note.** The source declaration is `{node['originalName']}`; its Lean "
        "statement gives the exact quantifier order and all boundary hypotheses."
    )


def definition_natural(module: str, count: int) -> str:
    return (
        f"This private definition bundle contains {count} source commands from `{module}`. "
        "It establishes the data structures, operators, instances, and theorem-valued "
        "construction facts required by downstream LIDT declarations.\n\n"
        "The bundle preserves the source module's exact Lean definitions inside the `LIDT` "
        "namespace and is intended as reusable formal infrastructure for the low individual "
        f"degree test soundness argument.\n\n{CREDIT}"
    )


def source_link(path: str, start: int | None = None, end: int | None = None) -> str:
    base = f"{SOURCE_REPO}/blob/{SOURCE_SHA}/{path}"
    if start is not None and end is not None:
        return f"{base}#L{start}-L{end}"
    return base


def generate() -> dict[str, Any]:
    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    project_names = set(plan["reachableRows"])
    if OUT.exists():
        for directory in (OUT / "Definitions", OUT / "Theorems", OUT / "Solutions"):
            if directory.exists():
                shutil.rmtree(directory)
        for generated_file in (OUT / "AllImports.lean", OUT / "All.lean"):
            if generated_file.exists():
                generated_file.unlink()
    for directory in (OUT / "Definitions", OUT / "Theorems", OUT / "Solutions"):
        directory.mkdir(parents=True, exist_ok=True)

    definition_payloads: list[dict[str, Any]] = []
    theorem_payloads: list[dict[str, Any]] = []
    solution_payloads: list[dict[str, Any]] = []

    for module in plan["definitionOrder"]:
        bundle = plan["definitions"][module]
        selected = {
            plan_command_key(plan["commands"][command_id])
            for command_id in bundle["commands"]
        }
        deprivatize = {
            plan_command_key(plan["commands"][command_id])
            for command_id in bundle["deprivatizeCommands"]
        }
        imports = {
            *("Definitions.Def_" + plan["definitions"][dependency]["definitionName"]
              for dependency in bundle["definitionDependencies"]),
            *plan["modules"][module]["externalImports"],
        }
        if module in PLATFORM_MODULE_BODIES:
            body = PLATFORM_MODULE_BODIES[module].encode()
        else:
            body = skeleton_body(
                module, selected, plan["renameMap"], project_names=project_names,
                deprivatize_keys=deprivatize,
                orphan_spans=plan["orphanSpans"].get(module, []), keep_orphans=True)
        text = (
            f"-- Generated from {plan['modules'][module]['source']} by skeleton subtraction.\n"
            + import_lines(imports)
            + scoped_notation_preamble(body)
            + "namespace LIDT\n\n"
            + namespace_stubs(plan, [module], wrapped=False)
            + body.decode("utf-8").strip()
            + ("\n\n" + SUPPLEMENTAL_COMPANIONS[module]
               if module in SUPPLEMENTAL_COMPANIONS else "")
            + "\n\nend LIDT\n"
        )
        text = filter_explicit_project_opens(
            root_qualify_matrix_scopes(text), project_names)
        path = OUT / "Definitions" / f"Def_{bundle['definitionName']}.lean"
        path.write_text(text, encoding="utf-8")
        definition_payloads.append({
            "module": module,
            "definition_name": bundle["definitionName"],
            "definition_title": f"LIDT definitions: {module.removeprefix('MIPStarRE.').replace('.', ' / ')}",
            "definition_path": str(path.relative_to(ROOT)),
            "definition": text,
            "natural_language_statement": definition_natural(module, len(bundle["commands"])),
            "source": source_link(bundle["source"], *bundle["sourceLines"]),
            "tags": ["LIDT"],
            "private": True,
        })

    for command_id in plan["nodeOrder"]:
        node = plan["nodes"][command_id]
        command = plan["commands"][command_id]
        definition_imports = {
            "Definitions.Def_" + plan["definitions"][module]["definitionName"]
            for module in node["definitionModules"]
        }
        theorem_imports = {
            "Theorems.Thm_" + plan["nodes"][dependency]["slug"]
            for dependency in node["typeTheoremDependencies"]
        }
        external_imports = set(plan["modules"][node["module"]]["externalImports"])
        preamble_imports = definition_imports | theorem_imports | external_imports
        context = platformize_context(
            context_before(
                node["module"], command["declStart"]["offset"],
                plan["orphanSpans"].get(node["module"], [])))
        formal, hoisted = extract_command(
            plan, command_id, node["platformName"], stub=True)
        preamble = (
            import_lines(preamble_imports)
            + scoped_notation_preamble(context, formal)
            + namespace_stubs(plan, [node["module"]], wrapped=True)
            + context)
        preamble = root_qualify_matrix_scopes(preamble)
        if hoisted:
            preamble += "\n".join(hoisted) + "\n"
        theorem_text = preamble.rstrip() + "\n\n" + formal
        theorem_path = OUT / "Theorems" / f"Thm_{node['slug']}.lean"
        theorem_path.write_text(theorem_text, encoding="utf-8")

        inline_by_module: dict[str, set[str]] = defaultdict(set)
        for inline_id in node["inlineCommands"]:
            inline_by_module[plan["commands"][inline_id]["module"]].add(inline_id)
        helper_fragments: list[str] = []
        for module in inline_module_order(plan, inline_by_module):
            selected = {
                plan_command_key(plan["commands"][inline_id])
                for inline_id in inline_by_module[module]
            }
            fragment = skeleton_body(
                module, selected, plan["renameMap"], project_names=project_names,
                orphan_spans=plan["orphanSpans"].get(module, [])
            ).decode("utf-8").strip()
            if fragment:
                helper_fragments.append(
                    f"/- Source helpers from {plan['modules'][module]['source']}. -/\n{fragment}")
        solution_definition_imports = {
            "Definitions.Def_" + plan["definitions"][module]["definitionName"]
            for module in node["definitionModules"]
        }
        solution_theorem_imports = {
            "Theorems.Thm_" + plan["nodes"][dependency]["slug"]
            for dependency in node["theoremDependencies"]
        }
        helper_external_imports = set(external_imports)
        for module in inline_by_module:
            helper_external_imports.update(plan["modules"][module]["externalImports"])
        solution_imports = (
            solution_definition_imports | solution_theorem_imports | helper_external_imports)
        solution_command, solution_hoisted = extract_command(
            plan, command_id, "solution", stub=False)
        solution_context = context
        if solution_hoisted:
            solution_context += "\n".join(solution_hoisted) + "\n"
        helpers = "\n\n".join(helper_fragments)
        solution_text = (
            f"-- Generated proof for {node['originalName']}.\n"
            + import_lines(solution_imports)
            + scoped_notation_preamble(helpers, solution_context, solution_command)
            + namespace_stubs(
                plan, [node["module"], *sorted(inline_by_module)], wrapped=True)
            + "namespace LIDT\n\n"
            + helpers
            + ("\n\n" if helpers else "")
            + "end LIDT\n\n"
            + solution_context.rstrip()
            + "\n\n"
            + solution_command
        )
        solution_text = root_qualify_matrix_scopes(solution_text)
        solution_path = OUT / "Solutions" / f"Sol_{node['slug']}.lean"
        solution_path.write_text(solution_text, encoding="utf-8")

        title = title_from_name(node["originalName"])
        source = source_link(node["source"], *node["sourceLines"])
        theorem_payloads.append({
            "command_id": command_id,
            "theorem_name": node["platformName"],
            "theorem_title": title,
            "preamble": preamble.rstrip(),
            "formal_statement": formal.rstrip(),
            "natural_language_statement": theorem_natural(node, command),
            "source": source,
            "tags": ["LIDT"],
            "private": True,
            "theorem_path": str(theorem_path.relative_to(ROOT)),
        })
        solution_payloads.append({
            "command_id": command_id,
            "theorem_name": node["platformName"],
            "solution_path": str(solution_path.relative_to(ROOT)),
            "explanation": (
                f"This submission transports the checked source proof of `{node['originalName']}` "
                "into the namespaced LIDT dependency graph. The proof uses the imported, already "
                "verified child declarations recorded by the source elaboration graph and preserves "
                "the original hypotheses and conclusion without modification."
            ),
        })

    imports_only = [
        *("Definitions.Def_" + plan["definitions"][module]["definitionName"]
          for module in plan["definitionOrder"]),
        *("Theorems.Thm_" + plan["nodes"][command_id]["slug"]
          for command_id in plan["nodeOrder"]),
    ]
    (OUT / "AllImports.lean").write_text(
        import_lines(imports_only).rstrip() + "\n", encoding="utf-8")
    (OUT / "All.lean").write_text(
        import_lines(["AllImports"]) + "namespace LIDT\n\nend LIDT\n",
        encoding="utf-8")

    payloads = {
        "schemaVersion": 1,
        "sourceCommit": SOURCE_SHA,
        "tag": "LIDT",
        "private": True,
        "definitions": definition_payloads,
        "theorems": theorem_payloads,
        "solutions": solution_payloads,
    }
    PAYLOADS.write_text(json.dumps(payloads, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payloads


def main() -> int:
    payloads = generate()
    print(json.dumps({
        "definitions": len(payloads["definitions"]),
        "theorems": len(payloads["theorems"]),
        "solutions": len(payloads["solutions"]),
    }, sort_keys=True))
    print(f"wrote {OUT.relative_to(ROOT)}")
    print(f"wrote {PAYLOADS.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
