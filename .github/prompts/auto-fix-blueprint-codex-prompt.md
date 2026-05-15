The blueprint check failed. Your task is to fix the blueprint errors or
blueprint-to-Lean synchronization errors reported by CI.

Instructions:
1. Read the error logs carefully to identify the failing .tex files and error messages.
2. Common blueprint compilation failures and how to fix them:
   - Unresolved \ref or \label: Check for typos in label names. Search the .tex files for the correct label.
   - Duplicate labels: Two environments share the same \label{...}. Rename one to be unique.
   - Mismatched \begin/\end environments: Ensure every \begin{theorem} has a matching \end{theorem}, etc.
   - Invalid \lean{DeclName}: The declaration name in \lean{} must match a real Lean declaration. Check MIPStarRE/ source files.
   - Missing \lean{DeclName} for a changed Lean declaration: find the
     corresponding paper-facing blueprint statement in blueprint/src/chapter/
     and add the Lean declaration tag. If the declaration is genuinely only an
     internal helper, do not add a misleading tag; instead leave a clear PR
     comment explaining why the public helper should not be represented in the
     blueprint.
   - Source-labelled theorem alignment: do not fix blueprint sync by pointing a
     paper theorem, lemma, or proposition to a conditional helper with bridge,
     residual, repair, package, producer, witness, wrapper, proof-obligation input, hypotheses bundle,
     assumptions bundle, or arbitrary hypothesis inputs that are not in
     `references/ldt-paper/`. Such helpers may be mentioned only in separate
     non-`\leanok` notes, and only when they are already useful quarantined
     proof content with an explicit unresolved source obligation.
   - Do not add `\leanok` merely because a renamed Lean declaration exists. If
     the declaration is an open internal obligation, contains `sorry`, or is a
     conditional helper, mention it separately with `\lean{...}` and no
     `\leanok` rather than inserting it into a source-labelled completed block.
   - Malformed LaTeX: Missing closing braces, unescaped special characters, etc.
   - plasTeX parse errors: These often point to unsupported LaTeX commands. Simplify or wrap in \ifplastex guards.
3. GitHub annotations titled "Blueprint update suggested" are actionable
   failures only when the PR has the `enforce-blueprint-coverage` label. On
   unlabelled PRs, treat them as advisory reverse-coverage warnings unless the
   failing CI log explicitly shows that they caused the blueprint check to fail.
4. The blueprint .tex files are in blueprint/src/chapter/. The blueprint config is in blueprint/src/.
5. You can test your fix locally by running:
   pip install leanblueprint plastex
   cd blueprint && leanblueprint web
   python3 scripts/blueprint_lean_sync.py --root . --ci
   Check that no ERROR lines appear in the output and that the sync checker passes.
6. Make minimal, targeted fixes. Do not refactor unrelated LaTeX.
7. Commit and push your fix to the current branch. Prefix commit messages with `[codex-auto-fix]`.
8. After pushing, use the PR number from the runtime context to post a summary of what was fixed.
