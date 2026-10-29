#!/usr/bin/env python3
"""Patch and release the final LIDT descriptions without exposing credentials."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
FINAL = Path("/home/drx/p2m/status/final")
RECORDS = ROOT / "prove2me" / "records"
STATE_PATH = RECORDS / "lidt_publish_state.json"
LOG_PATH = RECORDS / "lidt_publish.log"
API_KEY_PATH = Path("/home/drx/.config/prove2me/api_key")
BASE = "https://prove2.me/api/v1"
REASON = "Full statement and description before publication"
MAIN_ID = "b2e0f20e-0ffa-46f6-b8a9-3853a661b399"
TERMS_RE = re.compile(r"\b(?:terms?|licen[cs](?:e|ing|ed)|accept(?:ance|ed)?)\b", re.I)
RETRYABLE = {429, 500, 502, 503, 504}


class TermsError(RuntimeError):
    pass


class ApiError(RuntimeError):
    def __init__(self, method: str, path: str, code: int, payload: Any):
        self.method = method
        self.path = path
        self.code = code
        self.payload = payload
        super().__init__(f"{method} {path} returned HTTP {code}")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def entries() -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for filename, kind, id_key in (
        ("lidt-theorems-final.json", "theorem", "theorem_id"),
        ("lidt-bundles-final.json", "definition", "definition_id"),
    ):
        data = load_json(FINAL / filename)
        for name, item in sorted(data.items()):
            result.append({
                "kind": kind,
                "name": name,
                "id": item[id_key],
                "text": item["natural_language_statement"],
                "targetHash": digest(item["natural_language_statement"]),
            })
    return result


def key_for(item: dict[str, Any]) -> str:
    return f"{item['kind']}:{item['id']}"


def initial_state(items: list[dict[str, Any]]) -> dict[str, Any]:
    if STATE_PATH.is_file():
        state = load_json(STATE_PATH)
    else:
        state = {
            "schemaVersion": 1,
            "createdAt": now(),
            "project": "LIDT",
            "reason": REASON,
            "entries": {},
            "calls": [],
            "termsOrLicensingErrors": [],
        }
    for item in items:
        state["entries"].setdefault(key_for(item), {
            "kind": item["kind"],
            "name": item["name"],
            "id": item["id"],
            "targetHash": item["targetHash"],
        })
        state["entries"][key_for(item)]["targetHash"] = item["targetHash"]
    return state


def save_state(state: dict[str, Any]) -> None:
    RECORDS.mkdir(parents=True, exist_ok=True)
    tmp = STATE_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(STATE_PATH)


def log_line(text: str) -> None:
    RECORDS.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as handle:
        handle.write(f"{now()} {text}\n")


def response_summary(payload: Any) -> dict[str, Any]:
    if isinstance(payload, dict):
        summary: dict[str, Any] = {"keys": sorted(payload.keys())}
        for key in ("theorem_id", "definition_id", "theorem_name", "definition_name",
                    "visibility", "status", "message", "error"):
            if key in payload and isinstance(payload[key], (str, int, float, bool)):
                value = payload[key]
                if key in {"message", "error"}:
                    value = str(value)[:240]
                summary[key] = value
        return summary
    return {"type": type(payload).__name__}


def error_payload(raw: str) -> Any:
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return {"text": raw[:500]}


class Client:
    def __init__(self, state: dict[str, Any]) -> None:
        self.state = state
        self.token: str | None = None
        self.token_expires = 0.0
        self.call_number = len(state["calls"])

    def record_call(self, method: str, path: str, auth: bool, code: int,
                    payload: Any, error: str | None = None) -> None:
        self.call_number += 1
        record: dict[str, Any] = {
            "number": self.call_number,
            "at": now(),
            "method": method,
            "path": path,
            "authenticated": auth,
            "status": code,
            "response": response_summary(payload),
        }
        if error:
            record["error"] = error[:240]
        self.state["calls"].append(record)
        save_state(self.state)

    def check_terms_error(self, payload: Any, code: int) -> None:
        if code < 400:
            return
        text = json.dumps(payload, ensure_ascii=False) if payload is not None else ""
        if TERMS_RE.search(text):
            self.state["termsOrLicensingErrors"].append({
                "at": now(),
                "status": code,
                "response": response_summary(payload),
            })
            save_state(self.state)
            raise TermsError(f"API returned a terms or licensing error (HTTP {code})")

    def refresh(self) -> None:
        key = API_KEY_PATH.read_text(encoding="utf-8").strip()
        request = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": key}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=120) as response:
                payload = json.load(response)
                code = response.status
            self.record_call("POST", "/agent/refresh", False, code, payload)
        except urllib.error.HTTPError as error:
            raw = error.read().decode("utf-8", errors="replace")
            payload = error_payload(raw)
            self.record_call("POST", "/agent/refresh", False, error.code, payload)
            self.check_terms_error(payload, error.code)
            raise RuntimeError("access-token refresh failed") from error
        token = payload.get("access_token") if isinstance(payload, dict) else None
        if not token:
            raise RuntimeError("access-token refresh returned no token")
        self.token = token
        self.token_expires = time.time() + 3300

    def request(self, method: str, path: str, *, body: dict[str, Any] | None = None,
                auth: bool = True, allow: set[int] | None = None) -> tuple[int, Any]:
        for attempt in range(8):
            if auth and (self.token is None or time.time() >= self.token_expires):
                self.refresh()
            headers: dict[str, str] = {}
            if auth:
                headers["Authorization"] = f"Bearer {self.token}"
            data = None
            if body is not None:
                data = json.dumps(body, ensure_ascii=False).encode("utf-8")
                headers["Content-Type"] = "application/json"
            request = urllib.request.Request(BASE + path, data=data, headers=headers, method=method)
            try:
                with urllib.request.urlopen(request, timeout=180) as response:
                    raw = response.read()
                    payload = json.loads(raw.decode("utf-8")) if raw else {}
                    code = response.status
                self.record_call(method, path, auth, code, payload)
                return code, payload
            except urllib.error.HTTPError as error:
                raw = error.read().decode("utf-8", errors="replace")
                payload = error_payload(raw)
                self.record_call(method, path, auth, error.code, payload)
                self.check_terms_error(payload, error.code)
                if error.code == 401 and auth and attempt == 0:
                    self.token = None
                    continue
                if error.code in RETRYABLE and attempt < 7:
                    time.sleep(min(60, 2 ** attempt))
                    continue
                if allow and error.code in allow:
                    return error.code, payload
                raise ApiError(method, path, error.code, payload) from error
            except (TimeoutError, urllib.error.URLError) as error:
                self.record_call(method, path, auth, 0, {}, error=type(error).__name__)
                if attempt == 7:
                    raise
                time.sleep(min(60, 2 ** attempt))
        raise RuntimeError(f"request retries exhausted for {method} {path}")


def update_entry_state(state: dict[str, Any], item: dict[str, Any], **values: Any) -> None:
    state["entries"].setdefault(key_for(item), {}).update(values)
    state["entries"][key_for(item)]["updatedAt"] = now()
    save_state(state)


def endpoint(item: dict[str, Any], singular: str | None = None) -> str:
    kind = singular or ("theorems" if item["kind"] == "theorem" else "definitions")
    return f"/{kind}/{item['id']}"


def patch_phase(client: Client, state: dict[str, Any], items: list[dict[str, Any]]) -> None:
    for item in items:
        current = state["entries"].get(key_for(item), {})
        if current.get("patch", {}).get("status") == "PATCHED":
            continue
        body = {
            "natural_language_statement": item["text"],
            "reason": REASON,
        }
        try:
            code, payload = client.request("PATCH", f"/theorems/{item['id']}", body=body,
                                           allow={400, 404, 405} if item["kind"] == "definition" else None)
        except ApiError:
            raise
        if code in {400, 404, 405} and item["kind"] == "definition":
            update_entry_state(state, item, patch={
                "status": "UNSUPPORTED",
                "endpoint": "/theorems/:id",
                "reason": "No documented definition update endpoint accepted the definition id",
            })
            log_line(f"patch unsupported definition={item['name']}")
            continue
        returned = payload.get("natural_language_statement") if isinstance(payload, dict) else None
        update_entry_state(state, item, patch={
            "status": "PATCHED",
            "endpoint": "/theorems/:id",
            "responseHash": digest(returned) if isinstance(returned, str) else None,
        })
        log_line(f"patched {item['kind']}={item['name']}")


def readback_phase(client: Client, state: dict[str, Any], items: list[dict[str, Any]]) -> None:
    for item in items:
        current = state["entries"].get(key_for(item), {})
        if current.get("patch", {}).get("status") == "UNSUPPORTED":
            continue
        if current.get("readback", {}).get("status") == "MATCH":
            continue
        for attempt in range(3):
            _, payload = client.request("GET", endpoint(item))
            actual = payload.get("natural_language_statement") if isinstance(payload, dict) else None
            if actual == item["text"]:
                update_entry_state(state, item, readback={
                    "status": "MATCH",
                    "attempts": attempt + 1,
                    "actualHash": digest(actual),
                    "visibility": payload.get("visibility"),
                })
                log_line(f"readback match {item['kind']}={item['name']}")
                break
            update_entry_state(state, item, readback={
                "status": "MISMATCH",
                "attempts": attempt + 1,
                "actualHash": digest(actual or ""),
            })
            if item["kind"] == "definition":
                code, _ = client.request(
                    "PATCH", f"/theorems/{item['id']}",
                    body={"natural_language_statement": item["text"], "reason": REASON},
                    allow={400, 404, 405},
                )
                if code in {400, 404, 405}:
                    update_entry_state(state, item, patch={
                        "status": "UNSUPPORTED",
                        "endpoint": "/theorems/:id",
                        "reason": "No documented definition update endpoint accepted the definition id",
                    })
                    break
            else:
                client.request(
                    "PATCH", f"/theorems/{item['id']}",
                    body={"natural_language_statement": item["text"], "reason": REASON},
                )
        else:
            raise RuntimeError(f"readback mismatch after retries: {item['name']}")


def known_sets(items: list[dict[str, Any]]) -> tuple[set[str], set[str]]:
    ids = {item["id"] for item in items}
    names = {item["name"] for item in items}
    return ids, names


def validate_public_response(payload: Any, ids: set[str], names: set[str]) -> None:
    if not isinstance(payload, dict):
        return
    for key in ("made_public", "published", "public"):
        values = payload.get(key)
        if not isinstance(values, list):
            continue
        for value in values:
            if isinstance(value, str) and (value in ids or value in names):
                continue
            if isinstance(value, dict):
                value_id = value.get("theorem_id") or value.get("definition_id") or value.get("id")
                value_name = value.get("theorem_name") or value.get("definition_name") or value.get("name")
                if value_id in ids or value_name in names:
                    continue
            raise RuntimeError("make-public response named an entry outside the LIDT project")


def public_phase(client: Client, state: dict[str, Any], items: list[dict[str, Any]]) -> None:
    ids, names = known_sets(items)
    ordered = [item for item in items if item["kind"] == "theorem" and item["id"] == MAIN_ID]
    ordered += [item for item in items if item["kind"] == "theorem" and item["id"] != MAIN_ID]
    ordered += [item for item in items if item["kind"] == "definition"]
    for item in ordered:
        current = state["entries"].get(key_for(item), {})
        if current.get("patch", {}).get("status") == "UNSUPPORTED":
            update_entry_state(state, item, publication={
                "status": "SKIPPED",
                "reason": "Description update endpoint did not accept definition id",
            })
            continue
        if current.get("readback", {}).get("status") != "MATCH":
            raise RuntimeError(f"refusing to publish without matching readback: {item['name']}")
        if current.get("publication", {}).get("status") == "PUBLIC":
            continue
        code, payload = client.request("POST", f"/theorems/{item['id']}/make-public", allow={400, 404})
        if code in {400, 404}:
            if item["kind"] == "definition":
                update_entry_state(state, item, publication={
                    "status": "SKIPPED",
                    "reason": "Make-public endpoint did not accept definition id",
                })
                log_line(f"make-public unsupported definition={item['name']}")
                continue
            raise ApiError("POST", f"/theorems/{item['id']}/make-public", code, payload)
        validate_public_response(payload, ids, names)
        update_entry_state(state, item, publication={
            "status": "PUBLIC",
            "response": response_summary(payload),
        })
        log_line(f"make-public requested {item['kind']}={item['name']}")


def verify_phase(client: Client, state: dict[str, Any], items: list[dict[str, Any]]) -> None:
    for item in items:
        current = state["entries"].get(key_for(item), {})
        if current.get("publication", {}).get("status") == "SKIPPED":
            continue
        if current.get("signedOut", {}).get("status") == "VERIFIED":
            continue
        code, payload = client.request("GET", endpoint(item), auth=False, allow={401, 403, 404})
        if code != 200:
            update_entry_state(state, item, signedOut={"status": "FAILED", "httpStatus": code})
            raise RuntimeError(f"signed-out verification failed for {item['name']}: HTTP {code}")
        actual = payload.get("natural_language_statement") if isinstance(payload, dict) else None
        visibility = payload.get("visibility") if isinstance(payload, dict) else None
        if actual != item["text"] or visibility != "public":
            update_entry_state(state, item, signedOut={
                "status": "FAILED",
                "httpStatus": code,
                "actualHash": digest(actual or ""),
                "visibility": visibility,
            })
            raise RuntimeError(f"signed-out verification mismatch for {item['name']}")
        update_entry_state(state, item, signedOut={
            "status": "VERIFIED",
            "httpStatus": code,
            "actualHash": digest(actual),
            "visibility": visibility or "public",
        })
        log_line(f"signed-out verified {item['kind']}={item['name']}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("patch", "readback", "public", "verify", "all"), default="all")
    args = parser.parse_args()
    items = entries()
    state = initial_state(items)
    save_state(state)
    client = Client(state)
    phases = ("patch", "readback", "public", "verify") if args.phase == "all" else (args.phase,)
    for phase in phases:
        print(f"phase {phase}", flush=True)
        if phase == "patch":
            patch_phase(client, state, items)
        elif phase == "readback":
            readback_phase(client, state, items)
        elif phase == "public":
            public_phase(client, state, items)
        elif phase == "verify":
            verify_phase(client, state, items)
    counts: dict[str, int] = {}
    for item in items:
        entry = state["entries"].get(key_for(item), {})
        for label, nested in (("patched", "patch"), ("readback", "readback"),
                              ("public", "publication"), ("signedOut", "signedOut")):
            if entry.get(nested, {}).get("status") in {"PATCHED", "MATCH", "PUBLIC", "VERIFIED"}:
                counts[label] = counts.get(label, 0) + 1
    print(json.dumps({"entries": len(items), "counts": counts,
                      "termsOrLicensingErrors": len(state["termsOrLicensingErrors"])}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except TermsError as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(2)
    except Exception as error:
        print(f"publish failed: {type(error).__name__}: {error}", file=sys.stderr)
        raise SystemExit(1)
