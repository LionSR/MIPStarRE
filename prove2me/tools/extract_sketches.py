#!/usr/bin/env python3
"""Run the sanctioned Stage 2 extractor over every Stage 1 module."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
GRAPH = ROOT / "prove2me" / "extracted" / "decl_graph.jsonl"
OUT_DIR = ROOT / "prove2me" / "extracted" / "sketch"
EXTRACTOR = ROOT / "prove2me" / "tools" / "extract_sketch_info.lean"
MANIFEST = ROOT / "prove2me" / "extracted" / "sketch_modules.tsv"


def module_source(module: str) -> Path:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if path.is_file():
        return path
    raise FileNotFoundError(f"no source file for module {module}: {path}")


def project_imports(module: str) -> list[str]:
    imports: list[str] = []
    for line in module_source(module).read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped == "module" or stripped.startswith("--"):
            continue
        match = re.fullmatch(r"(?:(?:public|meta)\s+)*import\s+([^\s]+)", stripped)
        if match:
            imported = match.group(1)
            if imported.startswith("MIPStarRE"):
                imports.append(imported)
            continue
        break
    return imports


def main() -> int:
    if not GRAPH.is_file():
        print(f"missing Stage 1 graph: {GRAPH}", file=sys.stderr)
        return 1

    modules: set[str] = set()
    for line in GRAPH.read_text(encoding="utf-8").splitlines():
        if line:
            modules.add(json.loads(line)["module"])
    work = list(modules)
    while work:
        module = work.pop()
        for imported in project_imports(module):
            if imported not in modules:
                modules.add(imported)
                work.append(imported)

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    manifest_lines: list[str] = []
    for index, module in enumerate(sorted(modules), start=1):
        source = module_source(module)
        output = OUT_DIR / f"{module}.jsonl"
        manifest_lines.append(f"{module}\t{source.relative_to(ROOT)}\t{output.relative_to(ROOT)}")
        if output.is_file():
            print(f"[{index}/{len(modules)}] keep {module}", flush=True)
            continue

        temp = output.with_suffix(".jsonl.tmp")
        print(f"[{index}/{len(modules)}] extract {module}", flush=True)
        with temp.open("w", encoding="utf-8") as handle:
            result = subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    str(EXTRACTOR),
                    str(source),
                    "MIPStarRE",
                ],
                cwd=ROOT,
                stdout=handle,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
        if result.returncode != 0:
            temp.unlink(missing_ok=True)
            print(result.stderr, file=sys.stderr)
            return result.returncode
        temp.replace(output)

    MANIFEST.write_text("\n".join(manifest_lines) + "\n", encoding="utf-8")
    print(f"wrote Stage 2 facts for {len(modules)} modules", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
