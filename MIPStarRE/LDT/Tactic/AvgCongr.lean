import MIPStarRE.LDT.Basic.Distribution

/-!
# Local `avgOver` congruence tactic

This opt-in proof helper peels equality goals headed by the project-local
`MIPStarRE.LDT.avgOver` by applying `avgOver_congr`, introducing the averaged
variable, and recursing through nested averages.  At non-average leaves it tries
`rfl` and `simp`, then leaves the remaining goal for the following tactic.

Usage patterns:

* `avg_congr` recursively descends through `avgOver` goals and closes definitional
  or simplifiable leaves.
* `avg_congr with x, u` names the introduced average variables before leaving the
  final leaf goal.
* `avg_congr using tac` additionally tries `tac` at every leaf; placeholders such
  as `_` are often enough when the introduced variables need not be named.

The tactic is intentionally conservative: it registers no global simp rules and
only rewrites by invoking the existing `avgOver_congr` theorem.
-/

open MIPStarRE.LDT

syntax "avg_congr" : tactic
syntax "avg_congr" " using " tactic : tactic
syntax "avg_congr" " with " ident : tactic
syntax "avg_congr" " with " ident "," ident : tactic
syntax "avg_congr" " with " ident "," ident "," ident : tactic
syntax "avg_congr" " with " ident "," ident "," ident "," ident : tactic
syntax "avg_congr" " with " ident " using " tactic : tactic
syntax "avg_congr" " with " ident "," ident " using " tactic : tactic
syntax "avg_congr" " with " ident "," ident "," ident " using " tactic : tactic
syntax "avg_congr" " with " ident "," ident "," ident "," ident " using " tactic : tactic

macro_rules
  | `(tactic| avg_congr) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro;
           avg_congr)
        | rfl
        | (solve | simp)
        | skip)
  | `(tactic| avg_congr using $tac:tactic) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro;
           avg_congr using $tac:tactic)
        | rfl
        | (solve | simp)
        | (solve | $tac:tactic)
        | skip)
  | `(tactic| avg_congr with $x:ident) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr)
        | rfl
        | (solve | simp)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident)
        | rfl
        | (solve | simp)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident, $z:ident) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident, $z:ident)
        | rfl
        | (solve | simp)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident, $z:ident, $w:ident) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident, $z:ident, $w:ident)
        | rfl
        | (solve | simp)
        | skip)
  | `(tactic| avg_congr with $x:ident using $tac:tactic) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr using $tac:tactic)
        | rfl
        | (solve | simp)
        | (solve | $tac:tactic)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident using $tac:tactic) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident using $tac:tactic)
        | rfl
        | (solve | simp)
        | (solve | $tac:tactic)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident, $z:ident using $tac:tactic) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident, $z:ident using $tac:tactic)
        | rfl
        | (solve | simp)
        | (solve | $tac:tactic)
        | skip)
  | `(tactic| avg_congr with $x:ident, $y:ident, $z:ident, $w:ident using $tac:tactic) =>
      `(tactic|
        first
        | (refine MIPStarRE.LDT.avgOver_congr _ _ _ ?_;
           intro $x:ident;
           avg_congr with $y:ident, $z:ident, $w:ident using $tac:tactic)
        | rfl
        | (solve | simp)
        | (solve | $tac:tactic)
        | skip)

syntax "ldt_avg_congr" : tactic
syntax "ldt_avg_congr" " using " tactic : tactic
syntax "ldt_avg_congr" " with " ident : tactic
syntax "ldt_avg_congr" " with " ident "," ident : tactic
syntax "ldt_avg_congr" " with " ident "," ident "," ident : tactic
syntax "ldt_avg_congr" " with " ident "," ident "," ident "," ident : tactic
syntax "ldt_avg_congr" " with " ident " using " tactic : tactic
syntax "ldt_avg_congr" " with " ident "," ident " using " tactic : tactic
syntax "ldt_avg_congr" " with " ident "," ident "," ident " using " tactic : tactic
syntax "ldt_avg_congr" " with " ident "," ident "," ident "," ident " using " tactic : tactic

macro_rules
  | `(tactic| ldt_avg_congr) => `(tactic| avg_congr)
  | `(tactic| ldt_avg_congr using $tac:tactic) => `(tactic| avg_congr using $tac:tactic)
  | `(tactic| ldt_avg_congr with $x:ident) => `(tactic| avg_congr with $x:ident)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident) =>
      `(tactic| avg_congr with $x:ident, $y:ident)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident, $z:ident) =>
      `(tactic| avg_congr with $x:ident, $y:ident, $z:ident)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident, $z:ident, $w:ident) =>
      `(tactic| avg_congr with $x:ident, $y:ident, $z:ident, $w:ident)
  | `(tactic| ldt_avg_congr with $x:ident using $tac:tactic) =>
      `(tactic| avg_congr with $x:ident using $tac:tactic)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident using $tac:tactic) =>
      `(tactic| avg_congr with $x:ident, $y:ident using $tac:tactic)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident, $z:ident using $tac:tactic) =>
      `(tactic| avg_congr with $x:ident, $y:ident, $z:ident using $tac:tactic)
  | `(tactic| ldt_avg_congr with $x:ident, $y:ident, $z:ident, $w:ident using $tac:tactic) =>
      `(tactic| avg_congr with $x:ident, $y:ident, $z:ident, $w:ident using $tac:tactic)

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

example {α β : Type*} (𝒟 : Distribution α) (ℰ : Distribution β)
    (f g : α → β → Error) (h : ∀ x y, f x y = g x y) :
    avgOver 𝒟 (fun x => avgOver ℰ (f x)) =
      avgOver 𝒟 (fun x => avgOver ℰ (g x)) := by
  avg_congr using exact h _ _

end Examples
