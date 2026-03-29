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
7. **Match Lean's theorem/lemma/def exactly.** If Lean says `theorem X`, use `\begin{theorem}`. If Lean says `lemma X`, use `\begin{lemma}`. Never use `\begin{proposition}` (Lean has no `proposition` keyword). Label prefix: `thm:` for theorem, `lem:` for lemma, `def:` for definition.

## Proof Sketches Must Match Lean
This is the most important rule. Every proof in the blueprint must faithfully describe what the Lean proof does:

- **Reference the actual lemmas used.** If the Lean proof calls `LDT.selfImprovement`, the blueprint proof should say "By Lemma X.Y (self-improvement)..." and list it in `\uses`.
- **Describe the actual proof structure.** If Lean does induction on a parameter, say so. If Lean uses a specific decomposition, name it.
- **Don't hand-wave where Lean is specific.** "Standard argument" is not acceptable if Lean uses three specific lemmas. Name them.
- **Don't be more specific than Lean.** If Lean uses `simp` to close a goal, a one-line sketch is fine.
- **`\uses` in proofs must be accurate.** Only list what the proof actually uses, not what the statement mentions.

## Notation Consistency
Notation must be **internally consistent** across the entire blueprint and **close to what the Lean code expresses**:

- **Indices**: 0-indexed where matching `Fin n` in Lean
- **Finite fields / alphabets**: use standard notation for the alphabet $\Sigma$ and finite fields $\mathbb{F}_q$
- **Measurements**: use standard quantum measurement notation (projective measurements, POVMs)
- **Strategies**: quantum strategies for nonlocal games should use standard notation from the literature
- **Expansion**: use standard notation for graph expansion parameters
- **Macros** (in `macros/common.tex`): define project-specific macros and use them consistently

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

## Blueprint Structure
- `content.tex` is a router: `\input{chapter/ch01_intro}` etc.
- Each chapter is a separate file in `chapter/`
- Definitions/theorems numbered within chapters: `\newtheorem{theorem}{Theorem}[chapter]`

## Lean Blueprint Macros
- `\lean{Namespace.DeclName}` — links to Lean declaration
- `\leanok` — marks definition/theorem/proof as fully formalized
- `\uses{label1, label2}` — declares dependency edges for the graph
- `\notready` — marks as not ready for formalization (orange in graph)
- `\mathlibok` — already in Mathlib (dark green in graph)

## Dependency Graph Colors (web)
- **Light green box**: definition with `\lean` + `\leanok` (defined in Lean)
- **Green**: theorem stated + `\lean` + `\leanok` (stated in Lean)
- **Dark green**: theorem with proof also `\leanok` (fully proved)
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
