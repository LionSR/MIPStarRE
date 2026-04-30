---
title: Repository organization audit
date: 2026-03-21
purpose: >
  Reviews repository organization for the active LDT track and records where
  files, guides, or source maps should be moved or clarified.
status: snapshot
track: repo
kind: organization-audit
---

# What is organized well

_Dated audit snapshot: this note records a 2026-03-21 organization review. It is preserved as a point-in-time audit, so later fixes and renames may supersede some specific file-path observations._

- The top-level split is broadly good. `MIPStarRE/` holds Lean code, `blueprint/` holds the blueprint, `references/` holds paper sources, `docs/` holds notes, and `scripts/` holds tooling. A human can tell the purpose of each major directory without much guessing.

- The active Paper2009LDT track is visible right away in `README.md`. The README now does the most important job correctly: it says the active paper is arXiv:2009.12982, points to `references/ldt-paper/`, points to `blueprint/src/`, and points to `MIPStarRE/Paper2009LDT/`.

- The active LDT materials form a sensible chain:
  1. `references/ldt-paper/` for the mirrored TeX source,
  2. `blueprint/src/` for the dependency-ordered blueprint,
  3. `MIPStarRE/Paper2009LDT/` for the Lean scaffold.
  That is a good navigational story.

- `MIPStarRE/Paper2009LDT/` is easy to browse. The section-based file names are plain and predictable: `Section3Test.lean`, `Section4Preliminaries.lean`, ..., `Section12Pasting.lean`. For a paper-following project, that is a maintainable layout.

- `blueprint/src/chapter/` is also easy to browse. The chapter names are short, thematic, and consistent with the current LDT track.

- `scripts/Checkdecls.lean` and `lakefile.toml` are structurally clean. The checkdecls executable lives in the obvious place, and `lakefile.toml` wires it in with minimal fuss. This is good maintenance hygiene.

- The attempt to preserve old 2111 work without scattering it everywhere is good. Keeping legacy blueprint material under `blueprint/legacy/` and keeping Lean-side 2111 material under `MIPStarRE/Paper2111/` is the right basic idea.

- `MIPStarRE/Paper2111/` currently being just a small `Skeleton.lean` file is also good archival discipline. It does not sprawl through the active codebase.

- `references/ldt-paper/` looks like a real source mirror rather than an ad hoc dump. The section files, `multilinearity.tex`, bibliography, and style file are all together in one place. That is good separation between source material and formalization code.

- Some historical residue is perfectly acceptable here. The existence of old 2111 material is not the problem by itself. The repo is large enough that preserving earlier planning work makes sense, as long as it is clearly marked.

# Mild cleanup opportunities

- The current workspace has local clutter that is harmless but not pleasant to return to: `.DS_Store`, `.lake/`, `blueprint/print/`, `blueprint/web/`, and `blueprint/lean_decls` are present locally. Since these are generated or machine-local, cleaning them out before handing the repo to another human would make the tree calmer.

- `references/.gitkeep` looks obsolete now that `references/` is populated.

- `references/ldt-paper/README.md` is too thin to help a returning human. Right now it only says the folder was imported from another repo path. It does not say, in plain language, that this is the active TeX source mirror for the 2009 LDT paper or that `multilinearity.tex` is the root file.

- `blueprint/legacy/` is conceptually the right place for archived 2111 blueprint material, but internally it is a little messy. It currently contains:
  - `content_2111_strict_20260320.tex`
  - `paper2111_blueprint.tex`
  - `paper2111_strict_blueprint.tex`
  - `references_2111_strict_20260320.bib`
  The problem is not the files themselves; the problem is that there is no short index saying which one is the early pilot blueprint, which one is the later strict standalone blueprint, and which one is the modular archived content snapshot.

- The README is mostly good, but the section called "The repo now contains three distinct layers" undersells the reusable foundation layer in `Quantum/`, `Codes/`, and `Games/`. That is not a factual error, just a slight mismatch between the prose and the actual directory structure.

- The docs folder is starting to mix several document types: active guides, archived 2111 notes, and audits/reviews. That is manageable for now, but it will get messy quickly if more dated notes accumulate without subfolders or an index.

# Confusing or misleading structure

- The biggest problem is not the presence of legacy 2111 material. The biggest problem is that some legacy 2111 material still sits in generic locations and still points at active LDT paths.

- Before this cleanup, the generic `docs/roadmap.md` name was the single most misleading filename in the repo. Renaming it to `audits/2026-03-08_strict-2111-roadmap.md` makes the legacy scope clearer, but the underlying note is still legacy 2111 planning material rather than active Paper2009LDT guidance.

- The deeper problem was the stale source-of-truth pointer. The roadmap and several preserved 2111 notes pointed to `MIPStarRE/blueprint/src/content.tex` as if that were still the 2111 theorem DAG. That was no longer true once `blueprint/src/content.tex` became the active LDT blueprint.

- The same stale-pointer problem also showed up in:
  - `MIPStarRE/Paper2111/Skeleton.lean`
  - `audits/2026-03-08_strict-2111-effort-estimate.md`
  - `audits/2026-03-08_lean-quantuminfo-reuse-2111.md`
  Those files needed to be redirected toward archived 2111 blueprint material so that contributors would not follow the wrong artifact.

- `README.md` needed the docs-side active-vs-legacy split to be explicit, not just the code/blueprint split. Calling out the archived 2111 notes under `docs/` is an important part of that cleanup.

- `audits/2026-03-20_ldt-source-map.md` is no longer fully synchronized with the current active blueprint. The clearest example is the self-improvement split. The source-map note still says the blueprint keeps a single `thm:self-improvement` node carrying both Lean links, but the current blueprint now has separate nodes in:
  - `blueprint/src/chapter/ch07_self_improvement.tex`
  - `blueprint/src/chapter/ch10_induction.tex`
  That means an active-track documentation file is now describing an older state of the blueprint.

- `audits/2026-03-20_ldt-blueprint-dependency-review.md` also reads as a historical review rather than a current synced guide. That would be fine on its own. The problem is that the README currently lists it among the main files to use for the active track. Some of the issues it flags have already been fixed in the blueprint, including the source-order wording in `ch01_overview.tex`, the missing Schwartz–Zippel dependency in `ch10_induction.tex`, and the split between the two self-improvement theorems. As an audit snapshot, the file is useful. As a current navigation document, it is stale.

- `MIPStarRE.lean` imports both `MIPStarRE.Paper2111` and `MIPStarRE.Paper2009LDT`. That means the code-level entry point does not reflect the same active-vs-legacy boundary that the README is trying to communicate. A newcomer reading imports rather than prose will see both tracks presented as equally live.

- `blueprint/legacy/` is only half-separated. The directory itself is a good idea, but once you open it, there is no quick way to tell which 2111 file is the canonical archived strict blueprint and which files are earlier standalone documents.

- The `docs/` directory currently mixes:
  - active LDT docs,
  - legacy 2111 docs,
  - audit notes,
  - feasibility/investigation notes.
  That mix is survivable for the current repo size, but it is already at the point where a human has to inspect filenames closely to know whether a document is current, archival, or diagnostic.

# Recommended folder and doc cleanup

1. **Separate active and legacy docs explicitly.**
   The cleanest move would be to keep `docs/` for active-track material and move 2111 notes into something like `docs/legacy/2111/` or `archive/2111/`. Renaming `docs/roadmap.md` to `audits/2026-03-08_strict-2111-roadmap.md` is the first obvious step, but the larger active/legacy split would still improve navigation.

2. **Stop letting legacy 2111 files point at active LDT blueprint paths.**
   If those files are kept for historical reasons, they should either:
   - point to the archived 2111 blueprint material in `blueprint/legacy/`, or
   - say plainly at the top that they describe a pre-pivot state and are no longer the current source of truth.

3. **Add a short index for `docs/`.**
   A one-page `docs/README.md` would be enough. It should say which documents are current for Paper2009LDT, which are legacy 2111 archives, and which are audits or one-off investigation notes.

4. **Add a short index for `blueprint/legacy/`.**
   Right now the directory is understandable only if you already know the history. A two-minute index would fix that.

5. **Decide whether legacy 2111 should stay on the default Lean import path.**
   If the active track is really Paper2009LDT, then importing `Paper2111` from `MIPStarRE.lean` is structurally noisy. Either remove it from the default entry point or mark that import clearly as archival.

6. **Sync or retire the active LDT support docs that have drifted.**
   In particular:
   - `audits/2026-03-20_ldt-source-map.md` should match the current blueprint state,
   - `audits/2026-03-20_ldt-blueprint-dependency-review.md` should either be updated or clearly marked as a historical review with some findings already resolved.

7. **Keep the current high-level folder split, but make the history boundary sharper.**
   The overall architecture is already close to good. This does not need a major reorganization. The main need is to stop current and archival guidance from living under equally generic names.

8. **Do a light workspace cleanup before future handoff.**
   Remove local generated folders and OS cruft when convenient: `.DS_Store`, `.lake/`, `blueprint/print/`, `blueprint/web/`, `blueprint/lean_decls`, and the obsolete `references/.gitkeep`.

9. **Improve the small explanatory files in source-mirror areas.**
   `references/ldt-paper/README.md` should say what the folder is for in project language, not just where it came from.

Overall judgment: the repo has a good active-track spine now, and the folder split is mostly healthy. The main maintainability problem is documentation drift from the 2111 era, especially where legacy notes still sit under generic names or still point at the active LDT blueprint path.
