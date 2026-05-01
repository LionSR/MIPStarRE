import Lean.Elab.Tactic
import MIPStarRE.LDT.Basic.Distribution

/-!
# Local `avgOver` congruence tactic

This opt-in proof helper peels equality goals headed by the project-local
`MIPStarRE.LDT.avgOver` by first trying `avgOver_congr`, introducing the averaged
variable, and recursing through nested averages.  When a `using` tactic asks it
to close the leaf and the plain route cannot do so, it backtracks to the
support-restricted theorem `avgOver_congr_on_support`, introduces both the
averaged variable and its support membership hypothesis, and retries the same
leaf logic.  At non-average leaves it tries an optional user-supplied tactic
first, then `rfl` and `simp`, and finally leaves an unclosed leaf goal for the
following tactic only after at least one average has been peeled.

Usage patterns:

* `avg_congr` recursively descends through `avgOver` goals and closes definitional
  or simplifiable leaves.
* `avg_congr with x, u` names the introduced average variables before leaving the
  final leaf goal; the comma-separated `with` list is variadic.
* `avg_congr using tac` additionally tries `tac` at every leaf before the default
  closers; placeholders such as `_` are often enough when the introduced variables
  need not be named.  If the plain pointwise route does not close, the tactic
  retries with `avgOver_congr_on_support`, so `tac` may use the introduced support
  membership hypothesis; with `x` it is named `hx` when that name is available,
  and it can always be found by type with `by assumption` or `‹_›`.

The tactic is intentionally conservative: it registers no global simp rules and
first tries the existing `avgOver_congr` theorem.  With a `using` tactic, the
support-restricted theorem `avgOver_congr_on_support` is used only as a
backtracking fallback when the plain route cannot close the resulting leaf.
-/

open Lean Elab Tactic
open MIPStarRE.LDT

/-- Recursively peel `avgOver` equality goals with optional leaf tactics. -/
syntax (name := avgCongr) "avg_congr" (" with " ident,+)? (" using " tactic)? : tactic

private inductive AvgCongrPeelKind where
  | plain
  | onSupport

private def avgCongrPlainPeel (name? : Option (TSyntax `ident)) : TacticM Unit := do
  evalTactic (← `(tactic| refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_))
  match name? with
  | some name => evalTactic (← `(tactic| intro $name:ident))
  | none => evalTactic (← `(tactic| intro))

private def avgCongrSupportHypBaseName (name? : Option (TSyntax `ident)) : Name :=
  match name? with
  | some name =>
      match name.getId.eraseMacroScopes with
      | .str _ s => Name.mkSimple ("h" ++ s)
      | _ => `hmem
  | none => `hmem

private def avgCongrSupportHypName
    (name? : Option (TSyntax `ident)) : TacticM Name := do
  let base := avgCongrSupportHypBaseName name?
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && decl.userName == base then
      return ← mkFreshUserName base
  return base

private def avgCongrSupportPeel (name? : Option (TSyntax `ident)) : TacticM Unit := do
  evalTactic (← `(tactic| refine MIPStarRE.LDT.avgOver_congr_on_support _ _ _ ?_))
  let varName ← match name? with
    | some name => pure name.getId
    | none => mkFreshUserName `x
  let supportName ← avgCongrSupportHypName name?
  let goal ← getMainGoal
  let (_, goal) ← goal.introN 2 [varName, supportName]
  replaceMainGoal [goal]

private def avgCongrPeel
    (kind : AvgCongrPeelKind) (name? : Option (TSyntax `ident)) : TacticM Unit := do
  match kind with
  | .plain => avgCongrPlainPeel name?
  | .onSupport => avgCongrSupportPeel name?

private def avgCongrCloseLeaf (fallback? : Option (TSyntax `tactic)) : TacticM Unit := do
  match fallback? with
  | some tac =>
      evalTactic (← `(tactic| solve | $tac:tactic)) <|>
        evalTactic (← `(tactic| rfl)) <|>
        evalTactic (← `(tactic| solve | simp))
  | none =>
      evalTactic (← `(tactic| rfl)) <|>
        evalTactic (← `(tactic| solve | simp))

/-- Core recursion for `avg_congr` using a fixed peel theorem.

When `requireClosed` is true, an unclosed leaf is treated as failure so the caller
can retry the whole linear pass with the support-restricted theorem.  When it is
false, an unclosed leaf after at least one peel is left for the next tactic,
matching the original prototype behavior. -/
private partial def evalAvgCongrCore
    (kind : AvgCongrPeelKind) (names : List (TSyntax `ident))
    (fallback? : Option (TSyntax `tactic)) (mayStop requireClosed : Bool) :
    TacticM Unit := do
  let tryPeel (name? : Option (TSyntax `ident)) : TacticM Bool := do
    let saved ← saveState
    try
      avgCongrPeel kind name?
      return true
    catch _ =>
      saved.restore
      return false
  match names with
  | name :: rest =>
      if ← tryPeel (some name) then
        evalAvgCongrCore kind rest fallback? true requireClosed
      else if mayStop then
        throwError "avg_congr: no nested `avgOver` equality remains to introduce `{name.getId}`"
      else
        throwError "avg_congr failed: expected an equality headed by `avgOver`"
  | [] =>
      if ← tryPeel none then
        evalAvgCongrCore kind [] fallback? true requireClosed
      else
        let saved ← saveState
        try
          avgCongrCloseLeaf fallback?
        catch _ =>
          saved.restore
          if requireClosed || !mayStop then
            throwError
              "avg_congr failed: no `avgOver` head and leaf tactics did not close the goal"

/-- Elaborator for the `avg_congr` tactic syntax. -/
@[tactic avgCongr]
def evalAvgCongr : Tactic := fun stx => do
  match stx with
  | `(tactic| avg_congr $[with $names:ident,*]? $[using $fallback:tactic]?) =>
      let names := match names with
        | some names => names.getElems.toList
        | none => []
      match fallback with
      | some _ =>
          -- Only run the closed-leaf search when a `using` tactic was supplied;
          -- the no-`using` path keeps the original cheap "peel and leave the
          -- leaf" behavior.
          let saved ← saveState
          try
            evalAvgCongrCore .plain names fallback false true
          catch _ =>
            saved.restore
            let saved ← saveState
            try
              evalAvgCongrCore .onSupport names fallback false true
            catch _ =>
              saved.restore
              evalAvgCongrCore .plain names fallback false false
      | none =>
          evalAvgCongrCore .plain names fallback false false
  | _ => throwUnsupportedSyntax

section Examples

example {α : Type*} (𝒟 : Distribution α) (f : α → Error) :
    avgOver 𝒟 f = avgOver 𝒟 f := by
  avg_congr

example {α β : Type*} (𝒟 : Distribution α) (ℰ : Distribution β)
    (f g : α → β → Error) (h : ∀ x y, f x y = g x y) :
    avgOver 𝒟 (fun x => avgOver ℰ (f x)) =
      avgOver 𝒟 (fun x => avgOver ℰ (g x)) := by
  avg_congr with x, y
  exact h x y

example {α β γ δ ε : Type*} (𝒟 : Distribution α) (ℰ : Distribution β)
    (ℱ : Distribution γ) (𝒢 : Distribution δ) (ℋ : Distribution ε)
    (f g : α → β → γ → δ → ε → Error)
    (h : ∀ a b c d e, f a b c d e = g a b c d e) :
    avgOver 𝒟 (fun a => avgOver ℰ (fun b => avgOver ℱ (fun c =>
      avgOver 𝒢 (fun d => avgOver ℋ (f a b c d))))) =
    avgOver 𝒟 (fun a => avgOver ℰ (fun b => avgOver ℱ (fun c =>
      avgOver 𝒢 (fun d => avgOver ℋ (g a b c d))))) := by
  avg_congr with a, b, c, d, e
  exact h a b c d e

example {α β : Type*} (𝒟 : Distribution α) (ℰ : Distribution β)
    (f g : α → β → Error) (h : ∀ x y, f x y = g x y) :
    avgOver 𝒟 (fun x => avgOver ℰ (f x)) =
      avgOver 𝒟 (fun x => avgOver ℰ (g x)) := by
  avg_congr using exact h _ _

example {α : Type*} (𝒟 : Distribution α) (f g : α → Error)
    (h : ∀ x, x ∈ 𝒟.support → f x = g x) :
    avgOver 𝒟 f = avgOver 𝒟 g := by
  avg_congr with x using exact h x hx

example (h : (1 : Nat) = 2) : (1 : Nat) = 2 := by
  fail_if_success avg_congr
  exact h

end Examples
