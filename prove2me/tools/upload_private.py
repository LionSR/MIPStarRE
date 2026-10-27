#!/usr/bin/env python3
"""Idempotently upload the validated LIDT tree as private Prove2Me entries."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
PAYLOADS_PATH = ROOT / "prove2me" / "generated" / "payloads.json"
STATE_PATH = ROOT / "prove2me" / "records" / "upload_state.json"
VALIDATION_RECEIPT = ROOT / "prove2me" / "generated" / "validation_receipt.json"
PLATFORM = ROOT / "prove2me" / "platform"
API_KEY_PATH = Path("/home/drx/.config/prove2me/api_key")
QPBT_NAMES = Path("/home/drx/p2m/status/lidt-names.tsv")
BASE = "https://prove2.me/api/v1"
DOCUMENTED_VERSION = "0.13.2"
TERMINAL_JOB = {"PUBLISHED", "FAILED", "ERROR"}
ACCEPTED_SUBMISSION = {"ACCEPTED"}
TERMINAL_SUBMISSION = {
    "ACCEPTED", "SKETCH_ACCEPTED", "FAILED", "CE", "WA", "SORRY", "ERROR",
}
TRANSIENT_PUBLISH_FAILURE_MARKERS = (
    "DB error looking up import",
    "ConnectionTerminated",
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


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


def require_validation_receipt() -> None:
    if not VALIDATION_RECEIPT.is_file():
        raise RuntimeError("missing validation receipt; run validate_upload.py first")
    receipt = json.loads(VALIDATION_RECEIPT.read_text(encoding="utf-8"))
    expected = {
        "planSha256": sha256(PLAN_PATH),
        "payloadsSha256": sha256(PAYLOADS_PATH),
        "platformSha256": platform_digest(),
        "typeAuditFailures": 0,
    }
    mismatches = {key: (receipt.get(key), value) for key, value in expected.items()
                  if receipt.get(key) != value}
    if mismatches:
        raise RuntimeError(f"validation receipt does not match upload payloads: {mismatches}")


class State:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.lock = threading.Lock()
        if path.is_file():
            self.data = json.loads(path.read_text(encoding="utf-8"))
        else:
            self.data = {
                "schemaVersion": 1,
                "createdAt": now(),
                "documentedVersion": DOCUMENTED_VERSION,
                "platformVersions": [],
                "definitions": {},
                "theorems": {},
                "solutions": {},
                "preflight": None,
                "finalVerification": None,
            }
            self.save()
        migrated = False
        for entry in self.data["definitions"].values():
            if not entry.get("definition_id") and entry.get("theorem_id"):
                entry["definition_id"] = entry["theorem_id"]
                migrated = True
        if migrated:
            self.save()

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temp = self.path.with_suffix(".json.tmp")
        temp.write_text(json.dumps(self.data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        temp.replace(self.path)

    def update(self, section: str, key: str, **values: Any) -> dict[str, Any]:
        with self.lock:
            entry = self.data[section].setdefault(key, {})
            entry.update(values)
            entry["updatedAt"] = now()
            self.save()
            return dict(entry)

    def entry(self, section: str, key: str) -> dict[str, Any]:
        with self.lock:
            return dict(self.data[section].get(key, {}))

    def add_version(self, version: str | None) -> None:
        if not version:
            return
        with self.lock:
            if version not in self.data["platformVersions"]:
                self.data["platformVersions"].append(version)
                self.save()


class Api:
    def __init__(self, state: State) -> None:
        self.api_key = API_KEY_PATH.read_text(encoding="utf-8").strip()
        self.state = state

    def refresh(self, retries: int = 8) -> str:
        for attempt in range(retries):
            request = urllib.request.Request(
                BASE + "/agent/refresh",
                data=json.dumps({"api_key": self.api_key}).encode(),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
                    payload = json.load(response)
                self.state.add_version(payload.get("version"))
                return payload["access_token"]
            except urllib.error.HTTPError as error:
                content = error.read().decode("utf-8", errors="replace")
                if error.code != 429 and not 500 <= error.code < 600:
                    raise RuntimeError(
                        f"token refresh returned {error.code}: {content}") from error
            except (TimeoutError, urllib.error.URLError, ConnectionError):
                if attempt + 1 == retries:
                    raise
            time.sleep(min(60, 2 ** attempt))
        raise RuntimeError("token refresh exhausted retries")

    def request(
        self,
        method: str,
        path: str,
        *,
        body: dict[str, Any] | None = None,
        multipart: dict[str, str | bytes] | None = None,
        retries: int = 8,
    ) -> dict[str, Any]:
        for attempt in range(retries):
            token = self.refresh()
            headers = {"Authorization": f"Bearer {token}"}
            data: bytes | None = None
            if body is not None:
                data = json.dumps(body).encode()
                headers["Content-Type"] = "application/json"
            elif multipart is not None:
                boundary = f"----p2m-lidt-{random.getrandbits(64):016x}"
                chunks: list[bytes] = []
                for key, value in multipart.items():
                    chunks.append(f"--{boundary}\r\n".encode())
                    if key == "file":
                        chunks.append(
                            b'Content-Disposition: form-data; name="file"; filename="solution.lean"\r\n')
                        chunks.append(b"Content-Type: text/plain\r\n\r\n")
                        chunks.append(value if isinstance(value, bytes) else value.encode())
                    else:
                        chunks.append(
                            f'Content-Disposition: form-data; name="{key}"\r\n\r\n'.encode())
                        chunks.append(value if isinstance(value, bytes) else value.encode())
                    chunks.append(b"\r\n")
                chunks.append(f"--{boundary}--\r\n".encode())
                data = b"".join(chunks)
                headers["Content-Type"] = f"multipart/form-data; boundary={boundary}"
            request = urllib.request.Request(BASE + path, data=data, headers=headers, method=method)
            try:
                with urllib.request.urlopen(request, timeout=120) as response:
                    return json.load(response)
            except urllib.error.HTTPError as error:
                content = error.read().decode("utf-8", errors="replace")
                if error.code == 429 or 500 <= error.code < 600:
                    time.sleep(min(60, 2 ** attempt))
                    continue
                raise RuntimeError(f"API {method} {path} returned {error.code}: {content}") from error
            except (TimeoutError, urllib.error.URLError):
                if attempt + 1 == retries:
                    raise
                time.sleep(min(60, 2 ** attempt))
        raise RuntimeError(f"API request exhausted retries: {method} {path}")


def assert_safe_payloads(payloads: dict[str, Any]) -> None:
    if payloads.get("tag") != "LIDT" or payloads.get("private") is not True:
        raise RuntimeError("payload manifest is not globally private and tagged LIDT")
    for section in ("definitions", "theorems"):
        for item in payloads[section]:
            if item.get("private") is not True or item.get("tags") != ["LIDT"]:
                raise RuntimeError(f"unsafe {section} payload: {item}")


def preflight_collisions(
    api: Api,
    state: State,
    definition_names: list[str],
    theorem_names: list[str],
    concurrency: int,
) -> None:
    receipt_hash = sha256(PAYLOADS_PATH)
    prior = state.data.get("preflight")
    if prior and prior.get("payloadsSha256") == receipt_hash and prior.get("complete"):
        return
    requests = [("definition", name) for name in definition_names]
    requests.extend(("theorem", name) for name in theorem_names)
    collisions: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=concurrency) as executor:
        futures = {executor.submit(exact_search, api, kind, name): (kind, name)
                   for kind, name in requests}
        for future in as_completed(futures):
            kind, name = futures[future]
            matches = future.result()
            if not matches:
                continue
            section = "definitions" if kind == "definition" else "theorems"
            entry = state.entry(section, name)
            id_key = "definition_id" if kind == "definition" else "theorem_id"
            owned_id = entry.get(id_key)
            unmatched = [row for row in matches if not owned_id or row.get(id_key) != owned_id]
            if unmatched:
                collisions.append({
                    "kind": kind,
                    "name": name,
                    "visibility": unmatched[0].get("visibility"),
                })
    if collisions:
        raise RuntimeError(f"preflight found existing platform names: {collisions[:20]}")
    with state.lock:
        state.data["preflight"] = {
            "complete": True,
            "checkedAt": now(),
            "payloadsSha256": receipt_hash,
            "definitions": len(definition_names),
            "theorems": len(theorem_names),
        }
        state.save()


def exact_search(api: Api, kind: str, name: str) -> list[dict[str, Any]]:
    if kind == "definition":
        endpoint, key, rows = "/definitions", "definition_name", "definitions"
    else:
        endpoint, key, rows = "/theorems", "theorem_name", "theorems"
    query = urllib.parse.urlencode({key: name, "view": "full", "limit": 10})
    payload = api.request("GET", endpoint + "?" + query)
    return [row for row in payload.get(rows, []) if row.get(key) == name]


def normalize_cascaded_sketch(api: Api, state: State, name: str) -> bool:
    """Record an accepted sketch as complete once its theorem has cascaded to Proved."""
    entry = state.entry("solutions", name)
    if entry.get("status") != "SKETCH_ACCEPTED":
        return entry.get("status") == "ACCEPTED"
    matches = exact_search(api, "theorem", name)
    if len(matches) != 1 or matches[0].get("status") != "Proved":
        return False
    state.update(
        "solutions", name,
        status="ACCEPTED",
        platformSubmissionStatus="SKETCH_ACCEPTED",
        acceptedViaCascade=True,
    )
    state.update("theorems", name, theorem_status="Proved")
    return True


def is_transient_publish_failure(result: dict[str, Any]) -> bool:
    message = result.get("error_message") or ""
    return any(marker in message for marker in TRANSIENT_PUBLISH_FAILURE_MARKERS)


def record_transient_publish_failure(
    state: State, section: str, key: str, result: dict[str, Any],
) -> None:
    entry = state.entry(section, key)
    retries = entry.get("transientRetries", 0) + 1
    if retries > 8:
        raise RuntimeError(
            f"{section} job {key} exceeded transient retry limit: "
            f"{result.get('error_message')}")
    state.update(
        section, key,
        status="ERROR",
        transientRetries=retries,
        transientError=result.get("error_message"),
        transientFailedAt=now(),
    )


def poll_publish_job(api: Api, job_id: str) -> dict[str, Any]:
    return api.request("GET", f"/publish-jobs/{job_id}")


def reconcile_active_publish_jobs(api: Api, state: State, concurrency: int) -> None:
    active: list[tuple[str, str, str]] = []
    for section in ("definitions", "theorems"):
        for key, entry in state.data[section].items():
            if entry.get("status") in {"PENDING", "COMPILING"} and entry.get("job_id"):
                active.append((section, key, entry["job_id"]))
    with ThreadPoolExecutor(max_workers=concurrency) as executor:
        futures = {
            executor.submit(poll_publish_job, api, job_id): (section, key)
            for section, key, job_id in active
        }
        for future in as_completed(futures):
            section, key = futures[future]
            result = future.result()
            status = result.get("status")
            values: dict[str, Any] = {"status": status, "lastPollAt": now()}
            if section == "definitions":
                definition_id = result.get("definition_id") or result.get("theorem_id")
                if definition_id:
                    values["definition_id"] = definition_id
            elif result.get("theorem_id"):
                values["theorem_id"] = result["theorem_id"]
            if result.get("visibility"):
                values["visibility"] = result["visibility"]
            if result.get("error_message"):
                values["error_message"] = result["error_message"]
            state.update(section, key, **values)
            if status == "FAILED":
                if is_transient_publish_failure(result):
                    record_transient_publish_failure(state, section, key, result)
                    continue
                raise RuntimeError(
                    f"recorded {section} job {key} ended FAILED: "
                    f"{result.get('error_message')}")
            if status == "PUBLISHED" and result.get("visibility") != "private":
                raise RuntimeError(f"recorded {section} job {key} was not private")


def poll_submission(api: Api, submission_id: str) -> dict[str, Any]:
    query = urllib.parse.urlencode({"submission_id": submission_id})
    return api.request("GET", "/verify?" + query)


def recover_published(api: Api, state: State, section: str, key: str, kind: str) -> bool:
    matches = exact_search(api, kind, key)
    if len(matches) > 1:
        raise RuntimeError(f"multiple exact matches for {key}")
    if not matches:
        return False
    row = matches[0]
    visibility = row.get("visibility")
    if visibility != "private":
        raise RuntimeError(f"existing collision for {key} is not private")
    values: dict[str, Any] = {"status": "PUBLISHED", "recovered": True}
    if kind == "definition":
        values["definition_id"] = row.get("definition_id")
    else:
        values["theorem_id"] = row.get("theorem_id")
        values["theorem_status"] = row.get("status")
    state.update(section, key, **values)
    return True


def recover_publish_job(
    api: Api, state: State, section: str, key: str, kind: str,
) -> bool:
    entry = state.entry(section, key)
    intent_at = entry.get("intentAt", "")
    offset = 0
    matches: list[dict[str, Any]] = []
    while True:
        query = urllib.parse.urlencode({"limit": 200, "offset": offset})
        payload = api.request("GET", "/publish-jobs?" + query)
        batch = payload.get("publish_jobs", [])
        for job in batch:
            job_name = job.get("definition_name") if kind == "definition" else job.get(
                "theorem_name")
            if job_name == key and job.get("created_at", "") >= intent_at:
                matches.append(job)
        offset += len(batch)
        if offset >= payload.get("total", offset) or not batch:
            break
    if not matches:
        return False
    job = max(matches, key=lambda row: row.get("created_at", ""))
    job_id = job.get("job_id") or job.get("id")
    if not job_id:
        return False
    values: dict[str, Any] = {
        "job_id": job_id,
        "status": job.get("status", "PENDING"),
        "recovered": True,
    }
    if kind == "definition":
        definition_id = job.get("definition_id") or job.get("theorem_id")
        if definition_id:
            values["definition_id"] = definition_id
    elif job.get("theorem_id"):
        values["theorem_id"] = job["theorem_id"]
    state.update(section, key, **values)
    return True


def recover_submission(api: Api, state: State, name: str) -> bool:
    entry = state.entry("solutions", name)
    intent_at = entry.get("intentAt", "")
    page = 1
    matches: list[dict[str, Any]] = []
    while True:
        payload = api.request("GET", f"/submissions?page={page}")
        batch = payload.get("submissions", [])
        for submission in batch:
            theorem = submission.get("theorem") or {}
            theorem_name = submission.get("theorem_name") or theorem.get("theorem_name")
            if theorem_name == name and submission.get("created_at", "") >= intent_at:
                matches.append(submission)
        if page * 100 >= payload.get("total", page * 100) or not batch:
            break
        page += 1
    if not matches:
        return False
    submission = max(matches, key=lambda row: row.get("created_at", ""))
    submission_id = submission.get("submission_id") or submission.get("id")
    if not submission_id:
        return False
    state.update(
        "solutions", name,
        submission_id=submission_id,
        status=submission.get("status", "PENDING"),
        recovered=True,
    )
    return True


def submit_definition(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["definition_name"]
    entry = state.entry("definitions", name)
    if entry.get("status") == "PUBLISHED":
        return
    if entry.get("job_id") and entry.get("status") in {"PENDING", "COMPILING"}:
        return
    if entry.get("status") == "FAILED":
        raise RuntimeError(f"definition has a terminal failed job: {name}")
    if (not entry or entry.get("status") in {"INTENT", "ERROR"}) and recover_published(
            api, state, "definitions", name, "definition"):
        return
    if entry.get("status") == "INTENT" and recover_publish_job(
            api, state, "definitions", name, "definition"):
        return
    if entry.get("status") == "INTENT" and not entry.get("job_id"):
        raise RuntimeError(
            f"definition {name} has an unresolved pre-request intent; recover its publish job")
    state.update("definitions", name, status="INTENT", intentAt=now())
    body = {key: payload[key] for key in (
        "definition_name", "definition_title", "definition",
        "natural_language_statement", "source", "tags", "private")}
    response = api.request("POST", "/submit-definition", body=body)
    job_id = response.get("job_id")
    if not job_id:
        raise RuntimeError(f"definition submission returned no job_id: {name}")
    state.update("definitions", name, status="PENDING", job_id=job_id, submittedAt=now())


def submit_theorem(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["theorem_name"]
    entry = state.entry("theorems", name)
    if entry.get("status") == "PUBLISHED":
        return
    if entry.get("job_id") and entry.get("status") in {"PENDING", "COMPILING"}:
        return
    if entry.get("status") == "FAILED":
        raise RuntimeError(f"theorem has a terminal failed job: {name}")
    if (not entry or entry.get("status") in {"INTENT", "ERROR"}) and recover_published(
            api, state, "theorems", name, "theorem"):
        return
    if entry.get("status") == "INTENT" and recover_publish_job(
            api, state, "theorems", name, "theorem"):
        return
    if entry.get("status") == "INTENT" and not entry.get("job_id"):
        raise RuntimeError(
            f"theorem {name} has an unresolved pre-request intent; recover its publish job")
    state.update("theorems", name, status="INTENT", intentAt=now())
    body = {key: payload[key] for key in (
        "theorem_name", "theorem_title", "formal_statement", "natural_language_statement",
        "preamble", "source", "tags", "private")}
    response = api.request("POST", "/submit-problem", body=body)
    errors = response.get("errors", [])
    if errors:
        raise RuntimeError(f"theorem pre-queue rejection for {name}: {errors}")
    jobs = response.get("jobs", [])
    if len(jobs) != 1 or not jobs[0].get("job_id"):
        raise RuntimeError(f"theorem submission returned unexpected jobs for {name}: {jobs}")
    state.update("theorems", name, status="PENDING", job_id=jobs[0]["job_id"], submittedAt=now())


def submit_solution(api: Api, state: State, payload: dict[str, Any]) -> None:
    name = payload["theorem_name"]
    entry = state.entry("solutions", name)
    if entry.get("status") == "ACCEPTED":
        return
    if entry.get("status") == "SKETCH_ACCEPTED" and normalize_cascaded_sketch(
            api, state, name):
        return
    if entry.get("submission_id") and entry.get("status") == "PENDING":
        return
    if entry.get("status") in TERMINAL_SUBMISSION - {"ACCEPTED", "ERROR"}:
        raise RuntimeError(f"solution has a terminal non-accepted submission: {name}")
    if entry.get("status") == "INTENT" and recover_submission(api, state, name):
        return
    if entry.get("status") == "INTENT" and not entry.get("submission_id"):
        raise RuntimeError(
            f"solution {name} has an unresolved pre-request intent; recover its submission")
    theorem = state.entry("theorems", name)
    theorem_id = theorem.get("theorem_id")
    if not theorem_id:
        matches = exact_search(api, "theorem", name)
        if len(matches) != 1:
            raise RuntimeError(f"cannot resolve theorem id for solution {name}")
        theorem_id = matches[0]["theorem_id"]
        state.update("theorems", name, theorem_id=theorem_id,
                     theorem_status=matches[0].get("status"), status="PUBLISHED")
    state.update("solutions", name, status="INTENT", intentAt=now())
    solution = (ROOT / payload["solution_path"]).read_bytes()
    response = api.request("POST", "/verify", multipart={
        "theorem_id": theorem_id,
        "proof_type": "prove",
        "file": solution,
        "explanation": payload["explanation"],
    })
    submission_id = response.get("submission_id")
    if not submission_id:
        raise RuntimeError(f"solution submission returned no submission_id: {name}")
    state.update("solutions", name, status="PENDING", submission_id=submission_id,
                 submittedAt=now(), theorem_id=theorem_id)


def run_publish_phase(
    api: Api,
    state: State,
    *,
    section: str,
    ordered_keys: list[str],
    dependencies: dict[str, set[str]],
    payloads: dict[str, dict[str, Any]],
    submit: Callable[[Api, State, dict[str, Any]], None],
    concurrency: int,
) -> None:
    pending = set(ordered_keys)
    while pending:
        completed = {
            key for key in ordered_keys if state.entry(section, key).get("status") == "PUBLISHED"
        }
        pending -= completed
        if not pending:
            break
        ready = [key for key in ordered_keys if key in pending and dependencies[key] <= completed]
        if not ready:
            blocked = {key: sorted(dependencies[key] - completed) for key in sorted(pending)}
            raise RuntimeError(f"no ready {section}; blocked dependencies: {blocked}")
        wave = ready[:concurrency]
        with ThreadPoolExecutor(max_workers=concurrency) as executor:
            futures = {executor.submit(submit, api, state, payloads[key]): key for key in wave}
            for future in as_completed(futures):
                future.result()
        active = {
            key: state.entry(section, key).get("job_id") for key in wave
            if state.entry(section, key).get("status") != "PUBLISHED"
        }
        while active:
            time.sleep(3)
            with ThreadPoolExecutor(max_workers=concurrency) as executor:
                futures = {executor.submit(poll_publish_job, api, job_id): key
                           for key, job_id in active.items()}
                for future in as_completed(futures):
                    key = futures[future]
                    result = future.result()
                    status = result.get("status")
                    values: dict[str, Any] = {"status": status, "lastPollAt": now()}
                    if section == "definitions":
                        definition_id = result.get("definition_id") or result.get("theorem_id")
                        if definition_id:
                            values["definition_id"] = definition_id
                    elif result.get("theorem_id"):
                        values["theorem_id"] = result["theorem_id"]
                    if result.get("visibility"):
                        values["visibility"] = result["visibility"]
                    if result.get("error_message"):
                        values["error_message"] = result["error_message"]
                    state.update(section, key, **values)
                    if status in TERMINAL_JOB:
                        del active[key]
                        if status == "FAILED":
                            if is_transient_publish_failure(result):
                                record_transient_publish_failure(
                                    state, section, key, result)
                                continue
                            raise RuntimeError(
                                f"{section} job {key} ended {status}: {result.get('error_message')}")
                        if status == "PUBLISHED" and result.get("visibility") != "private":
                            raise RuntimeError(f"{section} job {key} was not private")


def run_solution_phase(
    api: Api,
    state: State,
    ordered_keys: list[str],
    dependencies: dict[str, set[str]],
    payloads: dict[str, dict[str, Any]],
    concurrency: int,
) -> None:
    pending = set(ordered_keys)
    while pending:
        completed = {
            key for key in ordered_keys if state.entry("solutions", key).get("status") == "ACCEPTED"
        }
        pending -= completed
        if not pending:
            break
        ready = [key for key in ordered_keys if key in pending and dependencies[key] <= completed]
        if not ready:
            blocked = {key: sorted(dependencies[key] - completed) for key in sorted(pending)}
            raise RuntimeError(f"no ready solutions; blocked dependencies: {blocked}")
        wave = ready[:concurrency]
        with ThreadPoolExecutor(max_workers=concurrency) as executor:
            futures = {executor.submit(submit_solution, api, state, payloads[key]): key for key in wave}
            for future in as_completed(futures):
                future.result()
        active = {
            key: state.entry("solutions", key).get("submission_id") for key in wave
            if state.entry("solutions", key).get("status") != "ACCEPTED"
        }
        while active:
            time.sleep(3)
            with ThreadPoolExecutor(max_workers=concurrency) as executor:
                futures = {executor.submit(poll_submission, api, submission_id): key
                           for key, submission_id in active.items()}
                for future in as_completed(futures):
                    key = futures[future]
                    result = future.result()
                    status = result.get("status")
                    state.update("solutions", key, status=status, lastPollAt=now())
                    if status in TERMINAL_SUBMISSION:
                        del active[key]
                        if status == "SKETCH_ACCEPTED" and normalize_cascaded_sketch(
                                api, state, key):
                            continue
                        if status not in ACCEPTED_SUBMISSION | {"ERROR"}:
                            raise RuntimeError(
                                f"solution {key} ended {status}: "
                                f"{result.get('error') or result.get('message')}")


def run_proved_node_phase(
    api: Api,
    state: State,
    ordered_keys: list[str],
    dependencies: dict[str, set[str]],
    theorem_payloads: dict[str, dict[str, Any]],
    solution_payloads: dict[str, dict[str, Any]],
    concurrency: int,
) -> None:
    pending = set(ordered_keys)
    while pending:
        completed = {
            key for key in ordered_keys
            if state.entry("solutions", key).get("status") == "ACCEPTED"
        }
        pending -= completed
        if not pending:
            break
        ready = [key for key in ordered_keys if key in pending and dependencies[key] <= completed]
        if not ready:
            blocked = {key: sorted(dependencies[key] - completed) for key in sorted(pending)}
            raise RuntimeError(f"no dependency-ready theorem nodes: {blocked}")
        wave = ready[:concurrency]
        for key in wave:
            entry = state.entry("theorems", key)
            if (entry.get("status") == "FAILED" and
                    "Imported platform theorems must be Proved" in
                    (entry.get("error_message") or "")):
                state.update(
                    "theorems", key,
                    status="ERROR",
                    scheduleRetry=True,
                    scheduleError=entry.get("error_message"),
                )
        run_publish_phase(
            api, state,
            section="theorems",
            ordered_keys=wave,
            dependencies={key: set() for key in wave},
            payloads=theorem_payloads,
            submit=submit_theorem,
            concurrency=concurrency,
        )
        run_solution_phase(
            api, state,
            ordered_keys=wave,
            dependencies={key: set() for key in wave},
            payloads=solution_payloads,
            concurrency=concurrency,
        )


def paged(
    api: Api,
    endpoint: str,
    row_key: str,
    filters: dict[str, Any],
    *,
    retries: int = 8,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    offset = 0
    while True:
        query = urllib.parse.urlencode({
            **filters,
            "view": "full",
            "limit": 200,
            "offset": offset,
        })
        payload = api.request("GET", endpoint + "?" + query, retries=retries)
        batch = payload.get(row_key, [])
        rows.extend(batch)
        total = payload.get("total", len(rows))
        if len(rows) >= total or not batch:
            return rows
        offset += len(batch)


def tagged_census(
    api: Api, endpoint: str, row_key: str,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    try:
        return paged(api, endpoint, row_key, {"tags": "LIDT"}, retries=1), {
            "mode": "tag-filter",
        }
    except RuntimeError as error:
        rows = paged(api, endpoint, row_key, {"q": "LIDT"})
        tagged = [
            row for row in rows
            if "lidt" in {str(tag).lower() for tag in row.get("tags", [])}
        ]
        return tagged, {
            "mode": "namespace-search-tag-filter",
            "tagQueryError": str(error),
            "searched": len(rows),
        }


def update_qpbt_ids(state: State) -> None:
    lines = QPBT_NAMES.read_text(encoding="utf-8").splitlines()
    header = lines[0].split("\t")
    theorem_name_index = header.index("platform_name")
    kind_index = header.index("entry_kind")
    theorem_id_index = header.index("theorem_id")
    output = [lines[0]]
    for line in lines[1:]:
        fields = line.split("\t")
        if fields[kind_index] == "theorem":
            fields[theorem_id_index] = state.entry("theorems", fields[theorem_name_index]).get(
                "theorem_id", "")
        output.append("\t".join(fields))
    QPBT_NAMES.write_text("\n".join(output) + "\n", encoding="utf-8")


def final_verify(
    api: Api,
    state: State,
    expected_definition_names: list[str],
    expected_theorem_names: list[str],
) -> None:
    definitions, definition_census = tagged_census(api, "/definitions", "definitions")
    theorems, theorem_census = tagged_census(api, "/theorems", "theorems")
    expected_defs = set(expected_definition_names)
    expected_theorems = set(expected_theorem_names)
    actual_defs = {row["definition_name"] for row in definitions}
    actual_theorems = {row["theorem_name"] for row in theorems}
    problems: list[str] = []
    if len(definitions) != len(actual_defs):
        problems.append("duplicate definition names in platform census")
    if len(theorems) != len(actual_theorems):
        problems.append("duplicate theorem names in platform census")
    missing_defs = sorted(expected_defs - actual_defs)
    unexpected_defs = sorted(actual_defs - expected_defs)
    missing_theorems = sorted(expected_theorems - actual_theorems)
    unexpected_theorems = sorted(actual_theorems - expected_theorems)
    if missing_defs:
        problems.append(f"missing definitions: {missing_defs[:10]}")
    if unexpected_defs:
        problems.append(f"unexpected definitions: {unexpected_defs[:10]}")
    if missing_theorems:
        problems.append(f"missing theorems: {missing_theorems[:10]}")
    if unexpected_theorems:
        problems.append(f"unexpected theorems: {unexpected_theorems[:10]}")
    nonprivate_defs = [row["definition_name"] for row in definitions
                       if row.get("visibility") != "private"]
    nonprivate_theorems = [row["theorem_name"] for row in theorems
                           if row.get("visibility") != "private"]
    nonproved = [row["theorem_name"] for row in theorems if row.get("status") != "Proved"]
    if nonprivate_defs:
        problems.append(f"nonprivate definitions: {nonprivate_defs[:10]}")
    if nonprivate_theorems:
        problems.append(f"nonprivate theorems: {nonprivate_theorems[:10]}")
    if nonproved:
        problems.append(f"non-Proved theorems: {nonproved[:10]}")
    definition_id_mismatches = [
        row["definition_name"] for row in definitions
        if state.entry("definitions", row["definition_name"]).get("definition_id") !=
        row.get("definition_id")
    ]
    theorem_id_mismatches = [
        row["theorem_name"] for row in theorems
        if state.entry("theorems", row["theorem_name"]).get("theorem_id") !=
        row.get("theorem_id")
    ]
    if definition_id_mismatches:
        problems.append(f"definition id mismatches: {definition_id_mismatches[:10]}")
    if theorem_id_mismatches:
        problems.append(f"theorem id mismatches: {theorem_id_mismatches[:10]}")
    main_name = "LIDT.MIPStarRE.LDT.Test.mainFormal"
    main_row = next((row for row in theorems if row["theorem_name"] == main_name), None)
    result = {
        "checkedAt": now(),
        "definitions": len(definitions),
        "theorems": len(theorems),
        "proved": sum(row.get("status") == "Proved" for row in theorems),
        "open": sum(row.get("status") == "Open" for row in theorems),
        "allPrivate": not nonprivate_defs and not nonprivate_theorems,
        "allTagged": all(
            "lidt" in {str(tag).lower() for tag in row.get("tags", [])}
            for row in definitions + theorems
        ),
        "definitionCensus": definition_census,
        "theoremCensus": theorem_census,
        "mainTheoremId": main_row.get("theorem_id") if main_row else None,
        "problems": problems,
    }
    with state.lock:
        state.data["finalVerification"] = result
        state.save()
    if problems:
        raise RuntimeError("final verification failed: " + "; ".join(problems))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("definitions", "theorems", "solutions", "verify", "all"),
                        default="all")
    parser.add_argument("--concurrency", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.concurrency <= 20:
        raise RuntimeError("concurrency must be between 1 and 20")

    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    payload_manifest = json.loads(PAYLOADS_PATH.read_text(encoding="utf-8"))
    require_validation_receipt()
    assert_safe_payloads(payload_manifest)
    state = State(STATE_PATH)
    api = Api(state)

    definition_payloads_by_module = {
        item["module"]: item for item in payload_manifest["definitions"]}
    definition_keys = [
        plan["definitions"][module]["definitionName"] for module in plan["definitionOrder"]]
    definition_payloads = {
        plan["definitions"][module]["definitionName"]: definition_payloads_by_module[module]
        for module in plan["definitionOrder"]
    }
    definition_deps = {
        plan["definitions"][module]["definitionName"]: {
            plan["definitions"][dependency]["definitionName"]
            for dependency in plan["definitions"][module]["definitionDependencies"]
        }
        for module in plan["definitionOrder"]
    }
    theorem_payloads_by_command = {item["command_id"]: item
                                   for item in payload_manifest["theorems"]}
    solution_payloads_by_command = {item["command_id"]: item
                                    for item in payload_manifest["solutions"]}
    theorem_keys = [plan["nodes"][command_id]["platformName"]
                    for command_id in plan["nodeOrder"]]
    theorem_payloads = {
        plan["nodes"][command_id]["platformName"]: theorem_payloads_by_command[command_id]
        for command_id in plan["nodeOrder"]
    }
    solution_payloads = {
        plan["nodes"][command_id]["platformName"]: solution_payloads_by_command[command_id]
        for command_id in plan["nodeOrder"]
    }
    theorem_deps = {
        plan["nodes"][command_id]["platformName"]: {
            plan["nodes"][dependency]["platformName"]
            for dependency in plan["nodes"][command_id]["theoremDependencies"]
        }
        for command_id in plan["nodeOrder"]
    }

    phases = ("definitions", "nodes", "verify") if args.phase == "all" else (args.phase,)
    if any(phase in {"definitions", "theorems", "solutions", "nodes"} for phase in phases):
        reconcile_active_publish_jobs(api, state, min(args.concurrency, 8))
        preflight_collisions(
            api, state, definition_keys, theorem_keys, min(args.concurrency, 8))
    for phase in phases:
        print(f"phase {phase}", flush=True)
        if phase == "definitions":
            run_publish_phase(
                api, state, section="definitions", ordered_keys=definition_keys,
                dependencies=definition_deps, payloads=definition_payloads,
                submit=submit_definition, concurrency=args.concurrency)
        elif phase == "theorems":
            if any(state.entry("definitions", key).get("status") != "PUBLISHED"
                   for key in definition_keys):
                raise RuntimeError("all definitions must be PUBLISHED before theorem upload")
            run_publish_phase(
                api, state, section="theorems", ordered_keys=theorem_keys,
                dependencies=theorem_deps, payloads=theorem_payloads,
                submit=submit_theorem, concurrency=args.concurrency)
            update_qpbt_ids(state)
        elif phase == "nodes":
            if any(state.entry("definitions", key).get("status") != "PUBLISHED"
                   for key in definition_keys):
                raise RuntimeError("all definitions must be PUBLISHED before theorem upload")
            run_proved_node_phase(
                api, state,
                ordered_keys=theorem_keys,
                dependencies=theorem_deps,
                theorem_payloads=theorem_payloads,
                solution_payloads=solution_payloads,
                concurrency=args.concurrency,
            )
            update_qpbt_ids(state)
        elif phase == "solutions":
            if any(state.entry("theorems", key).get("status") != "PUBLISHED"
                   for key in theorem_keys):
                raise RuntimeError("all theorem stubs must be PUBLISHED before solution upload")
            run_solution_phase(
                api, state, ordered_keys=theorem_keys, dependencies=theorem_deps,
                payloads=solution_payloads, concurrency=args.concurrency)
        elif phase == "verify":
            final_verify(api, state, definition_keys, theorem_keys)
            update_qpbt_ids(state)
    print(json.dumps(state.data["finalVerification"] or {
        "definitionsPublished": sum(
            item.get("status") == "PUBLISHED" for item in state.data["definitions"].values()),
        "theoremsPublished": sum(
            item.get("status") == "PUBLISHED" for item in state.data["theorems"].values()),
        "solutionsAccepted": sum(
            item.get("status") == "ACCEPTED" for item in state.data["solutions"].values()),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
