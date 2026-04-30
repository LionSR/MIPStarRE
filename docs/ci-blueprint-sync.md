# Blueprint ↔ Lean sync check

The [`blueprint-sync.yml`](../.github/workflows/blueprint-sync.yml) workflow
defends against drift between the LaTeX blueprint and the Lean source tree at
the **axiom** level: a `\leanok` tag is only honest if the Lean proof it
points to is free of `sorryAx` in its transitive closure.

It runs on every pull request that touches `blueprint/**`, `MIPStarRE/**`,
or the toolchain files, and on manual dispatch.

> **Current mode: advisory.** The check runs with `continue-on-error: true`
> so it does not block merging. Once the codebase reaches zero sorry sites,
> flip the workflow to hard-fail by removing `continue-on-error`.

## What it checks

For every `\begin{theorem|lemma|proposition|corollary|definition}` block in
`blueprint/src/chapter/*.tex` that contains `\lean{Name}`, the parser
records two independent flags based on `\leanok` placement (see
[`docs/blueprint_style_guide.md`](blueprint_style_guide.md)):

- **statement-level** — `\leanok` inside the statement environment body,
  i.e. the Lean declaration exists and its statement matches the blueprint;
- **proof-level** — `\leanok` inside the matching
  `\begin{proof}…\end{proof}`, i.e. the Lean proof is claimed complete.

A declaration may have both, only one, or neither. The axiom-closure check
then classifies findings by the strongest placement observed:

| Condition                                                                                | Severity |
|------------------------------------------------------------------------------------------|----------|
| `Name` is not a known Lean declaration, and the block has **proof-level** `\leanok`       | error    |
| `Name` is not a known Lean declaration, and the block has only **statement-level** `\leanok` | warning  |
| `Name` is not a known Lean declaration (no `\leanok`)                                     | warning  |
| Block has **proof-level** `\leanok` **and** the axiom closure of `Name` contains `sorryAx` | error    |
| Block has only **statement-level** `\leanok` and the axiom closure of `Name` contains `sorryAx` | warning  |
| Block has **proof-level** `\leanok` and `#print axioms Name` output could not be parsed (fail-safe) | error    |
| Block has only **statement-level** `\leanok` and `#print axioms Name` output could not be parsed (fail-safe) | warning  |
| `#print axioms Name` output could not be parsed, no `\leanok`                             | warning  |
| `Name` is sorry-free but the block has no `\leanok` anywhere                              | warning  |

The rationale for the statement-level downgrade is that statement-level
`\leanok` only claims the Lean statement matches the blueprint; it is **not**
a claim that the proof is complete. Flagging a `sorryAx` under a
statement-level-only marker would be overclaiming a violation. Proof-level
`\leanok` is the only placement that promises proof completeness, so that
remains the hard-failure signal.

Each failure and warning in the console output is annotated with its
observed `\leanok` placement (`[\leanok: statement-level]` or
`[\leanok: proof-level]`) so reviewers can distinguish statement-sync work
from proof-completion work at a glance.

The axiom closure is obtained by `lake env lean`-ing a throwaway harness that
runs `#print axioms Name` for each unique declaration. Lines are attributed
to a declaration **by the quoted `'Name'` / `` `Name` `` subject first**
(this is what Lean 4.28 emits with its plain-line format: `'Name' depends
on axioms: […]` / `'Name' does not depend on any axioms`), and only fall
back to a strict `<harness-path>:line:col:` location prefix (historical
format). Arbitrary `file:line:col:` prefixes from imported modules are
deliberately **not** trusted — a stray warning such as
`./MIPStarRE/Foo.lean:4:0: warning: …` would otherwise misattribute lines
to whichever declaration happens to sit on line 4 of the harness. ANSI
colour escapes are stripped before parsing. Pattern matching
(`Unknown identifier` / `Unknown constant`, `does not depend on any
axioms`, `depends on axioms: […]`) is performed case-insensitively so
both Lean 4.28's capital-U form and older lowercase forms are accepted.

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

* [`docs/blueprint-script-coverage.md`](blueprint-script-coverage.md) — the
  documented support surface for blueprint Python helpers, including their
  unit-test coverage and workflow path-filter policy.
* [`scripts/blueprint_lean_sync.py`](../scripts/blueprint_lean_sync.py) — the
  older name-level (grep-based) sync checker. It reports missing or stale
  entries in `blueprint/lean_decls` and decls referenced by name that don't
  appear in the Lean source tree. The two scripts are complementary:
  `blueprint_lean_sync.py` catches surface drift, `check_blueprint_sync.py`
  catches proof-level dishonesty.

  Its per-chapter progress table and JSON report (`--report FILE`) expose
  statement-level and proof-level coverage separately:

  ```json
  {
    "leanok_totals": {
      "statement_level": 42,
      "proof_level": 17,
      "statement_level_with_matching_lean_decl": 41,
      "proof_level_with_matching_lean_decl": 17
    },
    "chapter_stats": {
      "src/chapter/ch08_commutativity.tex": {
        "total": 6,
        "formalized": 6,
        "statement_formalized": 6,
        "proof_formalized": 3,
        "missing_lean": 0
      }
    }
  }
  ```

  The legacy `formalized` field is kept as an alias of
  `statement_formalized` so existing consumers (badges, dashboards) keep
  working.
* [`docs/PROOF_INTEGRITY.md`](PROOF_INTEGRITY.md) — full blocker list
  (`sorry`, `native_decide`, unexplained `axiom`, …) enforced elsewhere.
