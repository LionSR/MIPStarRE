# Proof Frontier Review

This document gives a checklist for reviewing Lean changes that introduce or
thread structure fields in the formalization. Its purpose is to prevent a
well-typed bookkeeping layer from being mistaken for a mathematical producer
theorem.

The central distinction is this:

- A **producer theorem** derives a mathematical object or relation from the
  hypotheses appearing in the paper or blueprint.
- An **external residual** records a missing producer explicitly, with a named
  issue and a statement of the mathematical obstruction.
- A **bookkeeping conversion** changes the form, namespace, or packaging of an
  already available object without deriving a new mathematical fact.

All three forms can be legitimate. The review problem is to identify which one
has been added, and to make sure the prose, blueprint tags, and issue status say
the same thing.

## Why Source-Level Holes Are Not Enough

The number of occurrences of `sorry` in the source is only a kernel-level
metric. It does not determine the mathematical frontier. A proof can be
`sorry`-free while still assuming the object that the paper asks one to
construct, for example by adding a field to a structure and proving the next
theorem by projecting that field.

For the LDT development this distinction matters most near the main theorem,
the main induction step, self-improvement, orthonormalization, and
projectivization. In these regions, a single displayed statement in the paper
usually depends on several producer theorems. Closing one local source hole may
only move the remaining obligation into an input structure.

## Reviewer Checklist

Before approving a PR that adds or modifies a structure field in a type named
with a suffix such as `Input`, `Residual`, `BridgeInputs`, `Witness`,
`Statement`, `Conclusion`, or `Package`, check the following points.

1. **Classify each new field.** State whether the field is produced in the PR,
   remains an external residual, or is only a bookkeeping conversion.
2. **Name the producer theorem.** If the field is produced, cite the exact Lean
   theorem that produces it from the paper hypotheses. If no such theorem
   exists, keep the parent mathematical issue open and link a native sub-issue
   for the missing producer.
3. **Check the blueprint frontier.** For work near `mainFormal`, Section 6,
   self-improvement, orthonormalization, or projectivization, inspect
   `blueprint/dep_graph_document.html` after building the blueprint. The
   remaining open vertices are part of the review context, even when the source
   diff contains no `sorry`.
4. **Reject hidden residual drift.** A theorem that merely moves an assumption
   into a structure field should be described as an input alignment or
   conditional bridge, not as proving the paper step.
5. **Review public prose.** Docstrings, module text, PR descriptions, and
   blueprint paragraphs should distinguish the words producer, input,
   residual, conditional theorem, and bookkeeping conversion.
6. **Size follow-up tasks by proof leaves.** Prefer issues such as "prove the
   raw Step 3 Cauchy--Schwarz estimate" to issues such as "close the
   self-improvement inputs" when the latter contains several independent
   proof obligations.
7. **Use native sub-issues.** Missing producers should be linked under the
   correct parent tracker instead of being left only in a PR comment.

## Diagonal and Completion Data

The recent Section 6 and self-improvement work produced several legitimate
bridge structures. It also exposed a recurring ambiguity: a theorem may mention
diagonal data, completion data, or restricted strategy data while only
repackaging such data as an explicit input.

For any theorem whose name or docstring mentions diagonal consistency,
line-130 data, completion, restricted strategies, or repaired strategy data,
reviewers should ask the following mathematical question:

Does the theorem derive the stated object from the paper hypotheses, or does it
assume that object as a field?

For line 130 of `references/ldt-paper/inductive_step.tex`, in particular,
the paper supplies a cross relation between `G^A` and `G^B`. A Lean theorem
that consumes diagonal strong self-consistency of `G^A` or `G^B` should not be
described as deriving that diagonal input unless it contains the missing
argument.

## Blueprint Tags

Use `\leanok` only when the Lean declaration proves the mathematical assertion
of the blueprint node under the stated hypotheses. If the Lean declaration is a
conditional wrapper or input splitter, then the blueprint should say so
explicitly. It may still cite the declaration with `\lean{...}`, but the prose
must identify the remaining producer.

When a PR introduces a public auxiliary lemma that is not a named paper
statement, the blueprint should either omit it or cite it as a subordinate
formalization-only support lemma. Do not allow a support lemma to inherit the
status of the paper theorem whose proof will eventually consume it.

## Examples From the Project

- Issue #1110 and the surrounding Section 6 work showed that diagonal and
  line-130 inputs can be made type-correct without proving the diagonal
  producer. Such declarations must be described as conditional inputs.
- Issue #1109 concerned final-field boundedness. The generalized theorem
  `final_fields_bounded` is a genuine producer once the SDP dual witness
  satisfies `I <= Z`; the blueprint prose was updated to state that hypothesis
  and the theorem's actual generality.
- Issues #1070 and #1072 are examples of proof-frontier work where individual
  structure fields had to be separated from the mathematical producer still
  tracked by the parent self-improvement issue.
- Issue #1081 and parent issue #931 illustrate why a parent tracker should stay
  open when a PR only supplies a bridge or residual package.

These examples are not special exceptions. They are the model for future review:
identify the mathematical producer, name the residual when it remains, and keep
the public prose faithful to that distinction.
