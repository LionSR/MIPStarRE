#!/usr/bin/env python3
"""Compile the generated upload text and compare staged theorem types."""

from __future__ import annotations

import json
import hashlib
import os
import re
import shutil
import subprocess
import sys
import threading
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
PAYLOADS_PATH = ROOT / "prove2me" / "generated" / "payloads.json"
PLATFORM = ROOT / "prove2me" / "platform"
LOG = ROOT / "prove2me" / "generated" / "validation.log"
TYPE_AUDIT_ORIGINAL_LEAN = ROOT / "prove2me" / "generated" / "type_audit_original.lean"
TYPE_AUDIT_STAGED_LEAN = ROOT / "prove2me" / "generated" / "type_audit_staged.lean"
TYPE_AUDIT_JSONL = ROOT / "prove2me" / "generated" / "type_audit.jsonl"
TYPE_AUDIT_REPORT = ROOT / "prove2me" / "generated" / "type_audit_report.json"
VALIDATION_RECEIPT = ROOT / "prove2me" / "generated" / "validation_receipt.json"
QPBT_NAMES = Path("/home/drx/p2m/status/lidt-names.tsv")
QPBT_NEEDS = Path("/home/drx/p2m/status/qpbt-needs-from-lidt.txt")
QPBT_CHECK = ROOT / "prove2me" / "generated" / "qpbt_import_check.lean"


def lake_env_value(name: str) -> str:
    result = subprocess.run(
        ["lake", "env", "printenv", name],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return result.stdout.strip()


def lean_binary() -> str:
    result = subprocess.run(
        ["lake", "env", "which", "lean"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return result.stdout.strip().splitlines()[-1]


def restricted_env() -> dict[str, str]:
    env = os.environ.copy()
    original = lake_env_value("LEAN_PATH").split(os.pathsep)
    root_build = str((ROOT / ".lake" / "build" / "lib" / "lean").resolve())
    retained = [entry for entry in original if entry and str(Path(entry).resolve()) != root_build]
    env["LEAN_PATH"] = os.pathsep.join([
        str(PLATFORM / ".lake" / "build" / "lib" / "lean"), str(PLATFORM), *retained])
    return env


def compile_file(
    lean: str,
    env: dict[str, str],
    path: Path,
    log_handle: Any,
    log_lock: threading.Lock | None = None,
) -> None:
    relative = path.relative_to(PLATFORM).with_suffix(".olean")
    output = PLATFORM / ".lake" / "build" / "lib" / "lean" / relative
    output.parent.mkdir(parents=True, exist_ok=True)
    print(f"compile {path.relative_to(ROOT)}", flush=True)
    result = subprocess.run(
        [lean, "-o", str(output), str(path)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if log_lock is None:
        log_handle.write(result.stdout)
        log_handle.flush()
    else:
        with log_lock:
            log_handle.write(result.stdout)
            log_handle.flush()
    if result.returncode != 0:
        raise RuntimeError(f"Lean failed for {path}; see {LOG}")


def compile_dag(
    lean: str,
    env: dict[str, str],
    paths: dict[str, Path],
    dependencies: dict[str, set[str]],
    log_handle: Any,
    log_lock: threading.Lock,
    *,
    jobs: int,
) -> None:
    pending = set(paths)
    completed: set[str] = set()
    running: dict[Any, str] = {}
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            ready = sorted(
                item for item in pending
                if dependencies.get(item, set()) <= completed
            )
            for item in ready[:jobs - len(running)]:
                pending.remove(item)
                future = executor.submit(
                    compile_file, lean, env, paths[item], log_handle, log_lock)
                running[future] = item
            if not running:
                blocked = sorted(pending)[:10]
                raise RuntimeError(f"compile dependency cycle or missing dependency: {blocked}")
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                item = running.pop(future)
                future.result()
                completed.add(item)


def compile_aux(lean: str, env: dict[str, str], path: Path, log_handle: Any) -> None:
    output = path.with_suffix(".olean")
    result = subprocess.run(
        [lean, "-o", str(output), str(path)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=log_handle,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"Lean failed for {path}; see {LOG}")


def write_qpbt_check() -> int:
    lines = QPBT_NAMES.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    name_index = header.index("platform_name")
    module_index = header.index("import_module")
    kind_index = header.index("entry_kind")
    original_index = header.index("original_name")
    imports: set[str] = set()
    names: list[str] = []
    mapped_originals: set[str] = set()
    for line in lines[1:]:
        fields = line.split("\t")
        mapped_originals.add(fields[original_index])
        imports.add(fields[module_index])
        if fields[kind_index] != "definition" and fields[name_index]:
            names.append(fields[name_index])
    required = {
        line.strip() for line in QPBT_NEEDS.read_text(encoding="utf-8").splitlines()
        if line.strip() and line.strip() != "END"
    }
    missing = sorted(required - mapped_originals)
    if missing:
        raise RuntimeError(f"LIDT names map omits {len(missing)} QPBT declarations: {missing[:10]}")
    code = "\n".join(f"import {module}" for module in sorted(imports)) + "\n\n"
    code += "\n".join(f"#check {name}" for name in names) + "\n"
    QPBT_CHECK.write_text(code, encoding="utf-8")
    return len(names)


def code_only(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                output.extend("  ")
                index += 2
            elif text[index] == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            if newline == -1:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        elif text.startswith("/-", index):
            block_depth = 1
            output.extend("  ")
            index += 2
        elif text[index] == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def validate_text(payloads: dict[str, Any]) -> None:
    def validate_imports(label: str, text: str) -> None:
        code = code_only(text)
        imports = re.findall(r"(?m)^import\s+([^\s]+)\s*$", code)
        forbidden = [name for name in imports if name.startswith(("MIPStarRE", "MIPRE"))]
        if forbidden:
            raise RuntimeError(f"{label} imports original or external project modules: {forbidden}")
        if "_root_.MIPStarRE." in code:
            raise RuntimeError(f"{label} escapes the LIDT namespace to the original project")

    for definition in payloads["definitions"]:
        text = definition["definition"]
        validate_imports(f"definition {definition['definition_name']}", text)
        if re.search(r"\b(?:sorry|admit|axiom)\b", code_only(text)):
            raise RuntimeError(f"proof hole in definition {definition['definition_name']}")
        if "namespace LIDT" not in text or "end LIDT" not in text:
            raise RuntimeError(f"missing LIDT wrapper in {definition['definition_name']}")
        if not definition["private"] or definition["tags"] != ["LIDT"]:
            raise RuntimeError(f"unsafe metadata for definition {definition['definition_name']}")
    theorem_by_name = {item["theorem_name"]: item for item in payloads["theorems"]}
    for theorem in payloads["theorems"]:
        validate_imports(f"theorem {theorem['theorem_name']}", theorem["preamble"])
        formal = theorem["formal_statement"]
        if len(re.findall(r"\bsorry\b", formal)) != 1 or not formal.rstrip().endswith("by sorry"):
            raise RuntimeError(f"invalid theorem stub for {theorem['theorem_name']}")
        if theorem["theorem_name"] not in formal:
            raise RuntimeError(f"theorem name missing from stub: {theorem['theorem_name']}")
        if not theorem["private"] or theorem["tags"] != ["LIDT"]:
            raise RuntimeError(f"unsafe metadata for theorem {theorem['theorem_name']}")
    for solution in payloads["solutions"]:
        path = ROOT / solution["solution_path"]
        text = path.read_text(encoding="utf-8")
        validate_imports(f"solution {solution['theorem_name']}", text)
        code = code_only(text)
        if re.search(r"\b(?:sorry|admit|axiom)\b", code):
            raise RuntimeError(f"proof hole in solution {solution['theorem_name']}")
        solution_heads = re.findall(r"\btheorem\s+solution\b", code)
        if len(solution_heads) != 1:
            raise RuntimeError(
                f"expected one theorem solution for {solution['theorem_name']}; "
                f"found {len(solution_heads)}")
        if re.search(r"\b(?:lemma|protected\s+theorem)\s+solution\b", code):
            raise RuntimeError(f"invalid solution declaration head for {solution['theorem_name']}")
        own_import = "Theorems.Thm_" + solution["theorem_name"].replace(".", "_")
        solution_imports = re.findall(r"(?m)^import\s+([^\s]+)\s*$", code)
        if own_import in solution_imports:
            raise RuntimeError(f"solution imports its own target: {solution['theorem_name']}")
        if solution["theorem_name"] not in theorem_by_name:
            raise RuntimeError(f"solution has no theorem payload: {solution['theorem_name']}")


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def write_type_audits(plan: dict[str, Any]) -> None:
    pairs = [
        (plan["nodes"][command_id]["originalName"],
         plan["nodes"][command_id]["platformName"])
        for command_id in plan["nodeOrder"]
    ]
    original_names = ",\n  ".join(lean_string(original) for original, _ in pairs)
    staged_names = ",\n  ".join(lean_string(staged) for _, staged in pairs)

    def audit_code(imports: list[str], names: str) -> str:
        return "\n".join(imports) + f"""

open Lean Meta

run_meta do
  let names : Array String := #[
  {names}
  ]
  let env ← getEnv
  for name in names do
    let some info := env.find? name.toName
      | throwError "missing declaration {{name}}"
    let type ← withOptions (fun opts =>
      (opts.setBool `pp.fullNames true).setBool `pp.universes true) do
        ppExpr info.type
    IO.println (Json.mkObj [
      ("name", Json.str name),
      ("type", Json.str type.pretty)
    ]).compress
"""

    TYPE_AUDIT_ORIGINAL_LEAN.write_text(
        audit_code(["import MIPStarRE"], original_names), encoding="utf-8")
    TYPE_AUDIT_STAGED_LEAN.write_text(
        audit_code([
            "import Theorems.Thm_" + plan["nodes"][command_id]["slug"]
            for command_id in plan["nodeOrder"]
        ], staged_names), encoding="utf-8")


def normalize_type(value: str, rename_map: dict[str, str], *, staged: bool) -> str:
    result = value
    if staged:
        for source, target in sorted(rename_map.items(), key=lambda item: len(item[1]), reverse=True):
            result = result.replace(target, source)
        result = result.replace("LIDT.", "")
    result = re.sub(r"u_[0-9]+", "u", result)
    result = re.sub(r"\s+", " ", result).strip()
    return result


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def platform_digest() -> str:
    digest = hashlib.sha256()
    for path in sorted(PLATFORM.rglob("*.lean")):
        digest.update(str(path.relative_to(PLATFORM)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def run_type_audit(lean: str, plan: dict[str, Any]) -> None:
    write_type_audits(plan)

    def run_one(path: Path, env: dict[str, str]) -> list[dict[str, str]]:
        result = subprocess.run(
            [lean, str(path)], cwd=ROOT, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if result.returncode != 0:
            TYPE_AUDIT_JSONL.write_text(result.stdout + result.stderr, encoding="utf-8")
            raise RuntimeError(f"type audit elaboration failed; see {TYPE_AUDIT_JSONL}")
        return [
            json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")
        ]

    original_env = os.environ.copy()
    original_env["LEAN_PATH"] = lake_env_value("LEAN_PATH")
    original_records = run_one(TYPE_AUDIT_ORIGINAL_LEAN, original_env)
    staged_records = run_one(TYPE_AUDIT_STAGED_LEAN, restricted_env())
    if len(original_records) != len(staged_records):
        raise RuntimeError(
            f"type audits emitted different counts: {len(original_records)} and "
            f"{len(staged_records)}")
    records = []
    for original_record, staged_record in zip(original_records, staged_records, strict=True):
        records.append({
            "originalName": original_record["name"],
            "stagedName": staged_record["name"],
            "originalType": original_record["type"],
            "stagedType": staged_record["type"],
        })
    TYPE_AUDIT_JSONL.write_text(
        "\n".join(json.dumps(record, ensure_ascii=False) for record in records) + "\n",
        encoding="utf-8")
    failures = []
    for record in records:
        original = normalize_type(record["originalType"], plan["renameMap"], staged=False)
        staged = normalize_type(record["stagedType"], plan["renameMap"], staged=True)
        if original != staged:
            failures.append({
                "originalName": record["originalName"],
                "stagedName": record["stagedName"],
                "originalType": original,
                "stagedType": staged,
            })
    report = {"checked": len(records), "failures": failures}
    TYPE_AUDIT_REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                                 encoding="utf-8")
    if len(records) != len(plan["nodeOrder"]):
        raise RuntimeError(
            f"type audit emitted {len(records)} of {len(plan['nodeOrder'])} records")
    if failures:
        raise RuntimeError(f"{len(failures)} staged theorem types differ; see {TYPE_AUDIT_REPORT}")


def main() -> int:
    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    payloads = json.loads(PAYLOADS_PATH.read_text(encoding="utf-8"))
    validate_text(payloads)
    lean = lean_binary()
    env = restricted_env()
    jobs = int(os.environ.get("LIDT_VALIDATION_JOBS", "8"))
    build_dir = PLATFORM / ".lake" / "build"
    if build_dir.exists():
        shutil.rmtree(build_dir)
    LOG.parent.mkdir(parents=True, exist_ok=True)
    with LOG.open("w", encoding="utf-8") as log_handle:
        log_lock = threading.Lock()
        definition_paths = {
            module: PLATFORM / "Definitions" / f"Def_{plan['definitions'][module]['definitionName']}.lean"
            for module in plan["definitionOrder"]
        }
        definition_dependencies = {
            module: set(plan["definitions"][module]["definitionDependencies"])
            for module in plan["definitionOrder"]
        }
        compile_dag(
            lean, env, definition_paths, definition_dependencies,
            log_handle, log_lock, jobs=jobs)
        theorem_paths = {
            command_id: PLATFORM / "Theorems" / f"Thm_{plan['nodes'][command_id]['slug']}.lean"
            for command_id in plan["nodeOrder"]
        }
        theorem_dependencies = {
            command_id: set(plan["nodes"][command_id]["typeTheoremDependencies"])
            for command_id in plan["nodeOrder"]
        }
        compile_dag(
            lean, env, theorem_paths, theorem_dependencies,
            log_handle, log_lock, jobs=jobs)
        solution_paths = {
            command_id: PLATFORM / "Solutions" / f"Sol_{plan['nodes'][command_id]['slug']}.lean"
            for command_id in plan["nodeOrder"]
        }
        compile_dag(
            lean, env, solution_paths,
            {command_id: set() for command_id in plan["nodeOrder"]},
            log_handle, log_lock, jobs=jobs)
        compile_file(lean, env, PLATFORM / "AllImports.lean", log_handle)
        compile_file(lean, env, PLATFORM / "All.lean", log_handle)
        qpbt_checked = write_qpbt_check()
        compile_aux(lean, env, QPBT_CHECK, log_handle)
    run_type_audit(lean, plan)
    VALIDATION_RECEIPT.write_text(json.dumps({
        "schemaVersion": 1,
        "planSha256": sha256(PLAN_PATH),
        "payloadsSha256": sha256(PAYLOADS_PATH),
        "platformSha256": platform_digest(),
        "definitions": len(plan["definitionOrder"]),
        "theorems": len(plan["nodeOrder"]),
        "solutions": len(plan["nodeOrder"]),
        "qpbtDeclarationsChecked": qpbt_checked,
        "typeAuditFailures": 0,
    }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "definitions": len(plan["definitionOrder"]),
        "theorems": len(plan["nodeOrder"]),
        "solutions": len(plan["nodeOrder"]),
        "typeAudit": "exact modulo LIDT namespace, ASCII rename map, and universe labels",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"validation failed: {error}", file=sys.stderr)
        raise
