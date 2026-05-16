# Blueprint Style Guide & Lessons Learned

## Core Philosophy
The blueprint is a **bridge between the mathematics and the Lean formalization**. A reader should be able to read a blueprint entry and immediately understand the corresponding Lean declaration. Conversely, someone reading the Lean code should find the blueprint proof sketch faithful to what the code actually does.

## General Principles
1. **Blueprint ↔ Lean must match.** Every `\lean{X}` tag must correspond to an actual Lean declaration. Every proof sketch must match what the Lean proof actually does — not a hand-wavy version of it.
2. **Standalone.** `blueprint/` and any slides are independent — no cross-references, no shared files. Each has its own macros, its own `references.bib`.
3. **Mathematical language only — zero Lean jargon.** No Lean identifiers in prose (no `selfImprovement_step`, no `PastingLemma.aux`, no `rintro ⟨X, hX⟩`). The `\lean{...}` tag is the link; the body text is standard mathematics. If you can't say it in math, rewrite it.
4. **No filler prose.** Only precise definitions, theorem statements, and proof sketches. No "this is important because..." or "the self-improvement step governs the induction...".
5. **Cite non-trivial things.** Basic definitions don't need citations. Important results and non-obvious definitions should cite the source paper.
6. **Don't invent terminology or notation.** Don't create ad-hoc notation when standard notation exists. Don't name things that the literature doesn't name.
7. **Match Lean's theorem/lemma/def exactly.** If Lean says `theorem X`, use `\begin{theorem}`. If Lean says `lemma X`, use `\begin{lemma}`. `\begin{proposition}` is allowed in blueprint prose when it improves mathematical readability, but still map it to an actual Lean `theorem`/`lemma` declaration via `\lean{...}`. Label prefix: `thm:` for theorem, `lem:` for lemma, `def:` for definition, `prop:` for proposition.

### Remark On Mathematical Prose

Blueprint entries should read as mathematical exposition, not as progress
reports. The mathematical argument should determine the order of the prose:
introduce the notation, state the assertion, give the proof or calculation, and
then record Lean references through the usual blueprint tags. Lean declarations,
file paths, and proof-status information should not become the visible structure
of the paragraph. When referring to a source article, cite it bibliographically
rather than relying on an uncited reference to the article.

Use displayed formulae when the formula benefits from visual separation, and
keep short scalar definitions or elementary inequalities inline when the
sentence reads better that way. As in ordinary mathematical writing, displayed
formulae should be punctuated as part of the sentences in which they occur.

## Proof Sketches Must Match Lean
This is the most important rule. Every proof in the blueprint must faithfully describe what the Lean proof does:

- **Reference the actual lemmas used.** If the Lean proof calls `LDT.selfImprovement`, the blueprint proof should say "By Lemma X.Y (self-improvement)..." and list it in `\uses`.
- **Describe the actual proof structure.** If Lean does induction on a parameter, say so. If Lean uses a specific decomposition, name it.
- **Don't hand-wave where Lean is specific.** "Standard argument" is not acceptable if Lean uses three specific lemmas. Name them.
- **Don't be more specific than Lean.** If Lean uses `simp` to close a goal, a one-line sketch is fine.
- **`\uses` in proofs must be accurate.** Only list what the proof actually uses, not what the statement mentions.

## Source-Labelled Statements And Conditional Helpers

If a blueprint theorem, lemma, or proposition carries a source label from the
paper, the linked Lean declaration must state the same theorem, up to faithful
formal encoding of the paper's domain.  Do not use `\lean{...}` and `\leanok`
on the source-labelled statement to point to a conditional helper whose
additional assumptions supply an unproved part of the paper proof.
Changing the Lean statement away from `references/ldt-paper/` is strongly
discouraged unless faithful formal encoding or a documented mathematical
necessity requires it; the blueprint should make any such necessity explicit.

Boundary hypotheses such as nonemptiness, decidability, field-model instances,
positivity of parameters, and denominator nonvanishing may be faithful when
they express the mathematical domain that the paper leaves implicit.  By
contrast, bridge inputs, residual data, repair hypotheses, producer
assumptions, proof-obligation inputs, or package assumptions are proof debt.
They must not be added to a source-labelled theorem statement.  If such data is
still unproved, the source-labelled Lean theorem should keep the source-shaped
statement and carry a tracked `sorry`, or the missing assertion should appear
as the lowest named internal obligation with a tracked `sorry`.  A separately
named conditional helper should not be introduced as a repair pattern.  If one
already contains substantial proof content, it may remain temporarily only as
quarantine: it needs a paper source, a tracking issue, and a discharge or
deletion plan.  The blueprint should leave the paper theorem unmarked as
proof-complete until the source-faithful Lean statement has a source-faithful
proof.

If a Lean theorem proves only a restricted version of a source theorem, the
blueprint entry carrying `\leanok` must state that restriction in the theorem
statement itself.  It must not be cited as the unrestricted source theorem.
When the only Lean declaration available for a source label has extra
non-paper assumptions, remove the `\leanok` claim from the source-labelled
entry or move the restricted statement to a separate Lean-only entry.  The
unrestricted paper theorem remains unformalized until a Lean statement with
the source's hypothesis set exists.

## Notation Consistency
Notation must be **internally consistent** across the entire blueprint and **close to what the Lean code expresses**:

- **Indices**: 0-indexed where matching `Fin n` in Lean
- **Finite fields / alphabets**: use standard notation for the alphabet $\Sigma$ and finite fields $\mathbb{F}_q$
- **Measurements**: use standard quantum measurement notation (projective measurements, POVMs)
- **Strategies**: quantum strategies for nonlocal games should use standard notation from the literature
- **Expansion**: use standard notation for graph expansion parameters
- **Macros** (in `macros/common.tex`): define project-specific macros and use them consistently

The original reference controls notation whenever it gives a usable convention.
If the blueprint needs a different symbol, index convention, or name in order to
match Lean, introduce it explicitly and relate it to the paper notation in the
same paragraph.  Do not let a `\lean{...}` tag, a Lean namespace, or a file name
be the only explanation of a changed term.

When a public Lean declaration is a formalization-only auxiliary lemma, the
blueprint should say so before listing the declaration.  The surrounding prose
should identify the paper theorem, equation, or construction that the auxiliary
lemma supports, and should avoid making the auxiliary name look like a named
result from the source article.

## What NOT to Put in the Blueprint
- **Lean identifier names in math text.** Write "the self-improvement lemma", never "the `selfImprovement` step". The `\lean{LDT.selfImprovement}` tag handles the linking.
- **Implementation details.** Don't say "bundled as an element of the Euclidean space" or "using `EuclideanSpace.equiv`". Describe the mathematical object.
- **Ad-hoc notation.** Don't invent superscripts or subscripts to distinguish from existing notation. Use standard conventions.
- **Function-call syntax.** Use mathematical notation, not programming notation.
- **Redundant definitions.** If two blueprint definitions describe the same mathematical object, consolidate them. Each definition should introduce genuinely new mathematical content.
- **Lean namespace prefixes in prose.** Don't write "the `LDT.PastingLemma`" — write "the pasting lemma".

## Banned AI/Software Language (enforced in both blueprint AND Lean code)
The blueprint reads as a **mathematical document**, not software documentation. The following patterns are banned in ALL reader-facing text (section titles, theorem names, proof sketches, remarks, chapter preambles) and in ALL Lean docstrings, comments, and section names:

### Banned terms → replacements:
| Banned | Use instead |
|--------|------------|
| "Assembly" (as section/chapter title) | "Proof of [theorem]", "Construction", "Composition" |
| "Pipeline" | "reduction", "construction", "proof chain" |
| "Bridge" (as noun for a connection) | "connection", name by mathematical content |
| "Handoff" / "hand off" | "transition", "continuation", or drop entirely |
| "In this blueprint" / "Within this blueprint" | "here", "in what follows", or omit |
| "Honest" (as adjective for rigorous) | "exact", "faithful", "unconditional", "complete" |
| "Glue layer" | "intermediate construction", "connecting results" |
| "Re-export" / "reexport" | "provides", "re-states" |
| "Wiring" / "wire up" | "connecting", "composing", "combining" |
| "Package" (as noun for a data bundle) | "form", "data", "structure" |
| "Sorry-free" | acceptable only in Lean-specific technical context |

### Additional rules:
- **Section names in Lean**: use mathematical terms (`section QuantumSoundness`, `section SelfImprovement`, `section PastingLemma`), not organizational terms (`section Assembly`, `section Pipeline`).
- **Internal LaTeX labels** (e.g., `\label{ch:soundness}`) are not reader-facing and need not be renamed if doing so would break cross-references. But NEW labels should follow the standard.
- **Definitions that are actually theorems**: if a statement asserts a mathematical fact, it must be `\begin{theorem}`, not `\begin{definition}`. Definitions introduce new objects; theorems prove properties.

## `\uses` Dependency Guidelines
- **Statement `\uses`**: list only what's needed to *state* the result (typically definitions of the objects involved). Keep minimal — transitive deps are automatic.
- **Proof `\uses`**: list only what the proof *actually calls*. Don't list definitions unless the proof unfolds that definition.
- **Never self-reference**: a proof's `\uses` must NOT include the label of the theorem it proves.

## Recording Formalization-Only Lemmas
Some Lean lemmas are genuine proof infrastructure rather than named statements
from the original papers. These must be traceable without making the blueprint
look as if the paper stated them.

- If a declaration directly formalizes a paper or blueprint statement, record
  it as usual with `\lean{...}` on that statement and cite the relevant source.
- If a public declaration is an auxiliary lemma introduced only for the Lean
  proof, make that status explicit. Its Lean docstring should say that it is a
  formalization-only auxiliary lemma and should name the nearby paper equation,
  line range, or blueprint result it supports.
- If such an auxiliary declaration is important enough to be referenced from
  the blueprint, give it a clearly subordinate blueprint node, for example
  `[Formalization support for ...]`, and state in the first sentence that the
  lemma is not a named statement of the paper but isolates a step used in the
  Lean proof.
- Connect auxiliary nodes to the corresponding result from the paper with `\uses{...}` from
  the proof that actually calls them. Do not add them only to silence a sync
  warning; the dependency edge should explain where the auxiliary result is
  used.
- Do not mark an auxiliary node with proof-level `\leanok` unless its Lean proof
  is complete and `#print axioms` has no `sorryAx`. Statement-level `\leanok`
  is acceptable only when the Lean statement is intentionally recorded but the
  proof remains tracked as incomplete.

## Blueprint Structure
- `content.tex` is a router: `\input{chapter/ch01_intro}` etc.
- Each chapter is a separate file in `chapter/`
- Definitions/theorems numbered within chapters: `\newtheorem{theorem}{Theorem}[chapter]`

## Lean Blueprint Macros
- `\lean{Namespace.DeclName}` — links to Lean declaration
- `\leanok` — context-sensitive marker; see "Statement-level vs proof-level `\leanok`" below
- `\uses{label1, label2}` — declares dependency edges for the graph
- `\notready` — marks as not ready for formalization (orange in graph)
- `\mathlibok` — already in Mathlib (dark green in graph; see legend note below)

### Statement-level vs proof-level `\leanok`

`\leanok` is context-sensitive for human review and graph interpretation. The same macro is used for two different claims, so reviewers should read it by placement rather than by raw token count.

**Statement-level `\leanok`.** Place this inside a `theorem`, `lemma`, `proposition`, `corollary`, or `definition` environment, on its own line immediately after `\lean{...}`. It says that the corresponding Lean declaration exists and that its statement matches the blueprint or paper statement. It does **not** say that the Lean proof already exists or is complete. For definitions, this is the only `\leanok` marker.

**Proof-level `\leanok`.** Place this inside the matching `proof` environment, preferably as the first line after `\begin{proof}`. The canonical current placement is the theorem `thm:commutativity-points` in `blueprint/src/chapter/ch08_commutativity.tex:8-19`, where the statement block has `\leanok` immediately after `\lean{...}` and the proof block begins with another `\leanok`. This marker says that the Lean proof is complete and free of unresolved `sorry` or unjustified project-level `axiom` shortcuts. In particular, `#print axioms <decl>` must show no `sorryAx`, and the declaration must satisfy the broader blocker rules in [`docs/PROOF_INTEGRITY.md`](PROOF_INTEGRITY.md).

A theorem, lemma, proposition, or corollary node is **fully formalized in Lean if and only if it has both markers**: statement-level `\leanok` in the statement block and proof-level `\leanok` in the proof block. Statement-level without proof-level means “the statement has been transcribed and matched, but the proof is not yet certified complete.” Definitions have no proof block, so statement-level `\leanok` alone is enough there.

Excerpt from `blueprint/src/chapter/ch08_commutativity.tex:8-19`:

```latex
\begin{theorem}[Commutativity of the point measurements]\label{thm:commutativity-points}
  \lean{MIPStarRE.LDT.CommutativityPoints.commutativityPoints}
  \leanok
  \uses{def:good-strategy, def:approx_delta}
  Let $(\psi,A,B,L)$ be an $(\eps,\delta,\gamma)$-good symmetric strategy.
\end{theorem}
\begin{proof}
  \leanok
  The strategy passes the diagonal lines test with probability $1-\gamma$.
\end{proof}
```

**Current CI behavior.** The advisory Blueprint ↔ Lean sync check in [`docs/ci-blueprint-sync.md`](ci-blueprint-sync.md) distinguishes the two placements. Only proof-level `\leanok` whose axiom closure contains `sorryAx` (or whose harness output cannot be parsed) is reported as an **error**. Statement-level-only `\leanok` with the same finding is downgraded to a **warning**, because statement-level does not claim proof completeness. Each audit line is annotated with the observed placement so reviewers can tell statement-sync work apart from proof-completion work.

`leanblueprint` does not use distinct macro names for these two claims, so audits must distinguish them by environment context rather than by raw `\leanok` counts. A future split such as `\leanokstmt` / `\leanokproof` could make that distinction explicit, but that is only a possible later cleanup; the current convention is to keep `\leanok` and rely on placement.

A recurring example is the chapter 4 `Q/X/\widehat X/P` witness layer: `lem:X-squared`, `lem:X-hat-squared`, `lem:X-times-X-hat`, and `lem:P-Q-approx` intentionally stop at statement-level `\leanok`. Their current Lean declarations only unpack identities or bounds stored on the chosen witness data, so proof-level `\leanok` would overclaim until a theorem actually constructs that data from the upstream hypotheses.

## Dependency Graph Colors (web)
- **Light green box**: definition with `\lean` + `\leanok` (defined in Lean)
- **Green**: theorem/lemma/proposition/corollary with `\lean` + statement-level `\leanok` (statement matched in Lean)
- **Dark green**: either (i) theorem/lemma/proposition/corollary with both statement-level and proof-level `\leanok` (fully formalized in Lean), or (ii) a `\mathlibok` node
- **Blue**: ready to state/prove (all deps are done)
- **Orange**: `\notready` (needs more blueprint work)

## Bibliography Workflow
1. Edit `blueprint/src/references.bib` (standalone, AuthorYYYYKeyword keys)
2. Run `cd blueprint/src && latexmk -lualatex -interaction=nonstopmode print.tex` (generates `print.bbl`)
3. Copy `blueprint/src/print.bbl` → `blueprint/src/web.bbl`  ← **must do this every time bib changes**
4. Run `leanblueprint web` (plasTeX reads `web.bbl`)
5. Citation key format: e.g., `Ji2020MIPStar`, `Natarajan2020Quantum`

## Stale/Corrupt Aux File Recovery
If LaTeX reports `! File ended while scanning use of \@newl@bel` on startup:
- The `.aux` file was truncated by a previous killed/timed-out run
- Fix: `rm -f blueprint/src/print.aux blueprint/print/print.aux blueprint/print.aux`
- Then rerun latexmk — it rebuilds the aux from scratch cleanly
- After rebuild, copy fresh `print.bbl` → `web.bbl`

## Build Commands
```bash
leanblueprint pdf     # PDF → blueprint/print/print.pdf
leanblueprint web     # HTML → blueprint/web/
leanblueprint serve   # local server at http://0.0.0.0:8000/
leanblueprint all     # pdf + web + checkdecls
```
