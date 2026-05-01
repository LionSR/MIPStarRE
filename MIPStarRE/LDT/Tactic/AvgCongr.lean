import Lean.Elab.Tactic
import MIPStarRE.LDT.Basic.Distribution

/-!
# Local `avgOver` congruence tactic

This opt-in proof helper peels equality goals headed by the project-local
`MIPStarRE.LDT.avgOver` by applying `avgOver_congr`, introducing the averaged
variable, and recursing through nested averages.  At non-average leaves it tries
an optional user-supplied tactic first, then `rfl` and `simp`, and finally leaves
an unclosed leaf goal for the following tactic only after at least one average has
been peeled.

Usage patterns:

* `avg_congr` recursively descends through `avgOver` goals and closes definitional
  or simplifiable leaves.
* `avg_congr with x, u` names the introduced average variables before leaving the
  final leaf goal; the comma-separated `with` list is variadic.
* `avg_congr using tac` additionally tries `tac` at every leaf before the default
  closers; placeholders such as `_` are often enough when the introduced variables
  need not be named.

The tactic is intentionally conservative: it registers no global simp rules and
only rewrites by invoking the existing `avgOver_congr` theorem.  Goals requiring
`avgOver_congr_on_support` are not handled; use a manual `refine`/`apply` of the
support-restricted theorem for those cases.
-/

open Lean Elab Tactic
open MIPStarRE.LDT

syntax (name := avgCongr) "avg_congr" (" with " ident,+)? (" using " tactic)? : tactic

private def avgCongrPeel (name? : Option (TSyntax `ident)) : TacticM Unit := do
  evalTactic (← `(tactic| refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_))
  match name? with
  | some name => evalTactic (← `(tactic| intro $name:ident))
  | none => evalTactic (← `(tactic| intro))

private def avgCongrTryPeel (name? : Option (TSyntax `ident)) : TacticM Bool := do
  let saved ← saveState
  try
    avgCongrPeel name?
    return true
  catch _ =>
    saved.restore
    return false

private def avgCongrCloseLeaf (fallback? : Option (TSyntax `tactic)) : TacticM Unit := do
  match fallback? with
  | some tac =>
      evalTactic (← `(tactic| solve | $tac:tactic)) <|>
        evalTactic (← `(tactic| rfl)) <|>
        evalTactic (← `(tactic| solve | simp))
  | none =>
      evalTactic (← `(tactic| rfl)) <|>
        evalTactic (← `(tactic| solve | simp))

private partial def evalAvgCongrCore
    (names : List (TSyntax `ident)) (fallback? : Option (TSyntax `tactic))
    (mayStop : Bool) : TacticM Unit := do
  match names with
  | name :: rest =>
      if ← avgCongrTryPeel (some name) then
        evalAvgCongrCore rest fallback? true
      else if mayStop then
        throwError "avg_congr: no nested `avgOver` equality remains to introduce `{name.getId}`"
      else
        throwError "avg_congr failed: expected an equality headed by `avgOver`"
  | [] =>
      if ← avgCongrTryPeel none then
        evalAvgCongrCore [] fallback? true
      else
        try
          avgCongrCloseLeaf fallback?
        catch _ =>
          unless mayStop do
            throwError
              "avg_congr failed: no `avgOver` head and leaf tactics did not close the goal"

@[tactic avgCongr]
def evalAvgCongr : Tactic := fun stx => do
  match stx with
  | `(tactic| avg_congr $[with $names:ident,*]? $[using $fallback:tactic]?) =>
      let names := match names with
        | some names => names.getElems.toList
        | none => []
      evalAvgCongrCore names fallback false
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

example (h : (1 : Nat) = 2) : (1 : Nat) = 2 := by
  fail_if_success avg_congr
  exact h

end Examples
