# Blueprint ↔ Lean sync check

The [`blueprint-sync.yml`](../.github/workflows/blueprint-sync.yml) workflow
defends against drift between the LaTeX blueprint and the Lean source tree at
the **axiom** level: a `\leanok` tag is only honest if the Lean proof it
points to is free of `sorryAx` in its transitive closure.

It runs on every pull request that touches `blueprint/**`, `MIPStarRE/**`,
or the toolchain files, and on manual dispatch.

## What it checks

For every `\begin{theorem|lemma|proposition|corollary|definition}` block in
`blueprint/src/chapter/*.tex` that contains `\lean{Name}`:

| Condition                                           | Severity |
|-----------------------------------------------------|----------|
| `Name` is not a known Lean declaration, and the block has `\leanok` | error |
| `Name` is not a known Lean declaration (no `\leanok`)               | warning |
| Block has `\leanok` **and** the axiom closure of `Name` contains `sorryAx` | error |
| Block has `\leanok` and `#print axioms Name` output could not be parsed (fail-safe) | error |
| `#print axioms Name` output could not be parsed, no `\leanok`       | warning |
| `Name` is sorry-free but the block has no `\leanok` anywhere        | warning |

Both statement-level `\leanok` (inside the environment body) and proof-level
`\leanok` (inside the matching `\begin{proof}…\end{proof}`) are accepted. No
distinction is drawn for this check — either form is considered a claim that
the theorem statement is formalized.

The axiom closure is obtained by `lake env lean`-ing a throwaway harness that
runs `#print axioms Name` for each unique declaration. Lean's `#print axioms`
output is accepted both with a `<file>:line:col:` location prefix and as
plain `'Name' depends on axioms: […]` / `'Name' does not depend on any
axioms` lines. ANSI colour escapes are stripped before parsing. Unknown
declarations are detected case-insensitively via `Unknown identifier` /
`Unknown constant` (either capitalisation, including Lean 4.28's
capital-U form).

**Two distinct global/local failure modes:**

1. **Global harness failure** — `lake env lean` exits non-zero **and** no
   recognised `#print axioms` output was attributed to any queried
   declaration (typical symptom of `import MIPStarRE` failing before the
   body runs). The script prints a warning with the tail of the raw lake
   output to stderr, skips per-declaration classification, and exits 0.
   That way a broken Lean build is not hidden behind cascading false
   blueprint errors.
2. **Per-declaration parse failure** — the harness output for a specific
   declaration is non-empty but matches none of the expected patterns
   (`does not depend on any axioms`, `depends on axioms: [...]`,
   `Unknown identifier/constant`). This is treated as **parse drift and
   fails safe**: for a `\leanok`-tagged entry it is an error, for an
   un-tagged entry it is a warning. The rationale is that a safety gate
   must not silently pass a `\leanok` declaration whose actual axiom
   dependence we cannot verify — if Lean's output format changes, we want
   CI to flag it rather than default to "looks fine".

## Running locally

Prerequisite: a working Lean toolchain (`elan`) and a prefetched Mathlib
cache.

```bash
lake exe cache get
lake build
python scripts/check_blueprint_sync.py
```

For a fast, parse-only smoke test that skips the Lean harness step:

```bash
python scripts/check_blueprint_sync.py --skip-axiom-check
```

To verify the check actually fails on drift, temporarily replace the proof of
a `\leanok`-tagged theorem with `sorry`, rerun, and confirm you see an
`ERROR` line and a GitHub Actions `::error::` annotation.

## Related tooling

* [`scripts/blueprint_lean_sync.py`](../scripts/blueprint_lean_sync.py) — the
  older name-level (grep-based) sync checker. It reports missing or stale
  entries in `blueprint/lean_decls` and decls referenced by name that don't
  appear in the Lean source tree. The two scripts are complementary:
  `blueprint_lean_sync.py` catches surface drift, `check_blueprint_sync.py`
  catches proof-level dishonesty.
* [`docs/PROOF_INTEGRITY.md`](PROOF_INTEGRITY.md) — full blocker list
  (`sorry`, `native_decide`, unexplained `axiom`, …) enforced elsewhere.
