import MIPStarRE.LDT.Pasting.Simplified.WordMarginal

/-!
# Uniform marginals of question tuples

A prefix of a uniformly sampled tuple is itself uniformly distributed.
The equivalence with a prefix and last coordinate provides the elementary
finite-product step used in the simplified pasting proof.

## References

- `blueprint/src/low_degree_simplified.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT

/-- A question tuple split into its initial segment and last coordinate. -/
def pointTuplePrefixLastEquiv
    (params : Parameters) (n : ℕ) :
    PointTuple params (n + 1) ≃ PointTuple params n × Fq params where
  toFun xs := (Fin.init xs, xs (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv xs := Fin.snoc_init_self xs
  right_inv p := by
    cases p with
    | mk xs x => simp

/-- The first `n` coordinates of a length-`k` question tuple. -/
def pointTuplePrefix
    (params : Parameters) {n k : ℕ} (h : n ≤ k)
    (xs : PointTuple params k) : PointTuple params n :=
  fun j => xs ⟨j.1, Nat.lt_of_lt_of_le j.2 h⟩

/-- Prefixes of uniformly sampled question tuples remain uniform. -/
theorem avgOver_uniform_pointTuple_prefix
    (params : Parameters) (n t : ℕ)
    (f : PointTuple params n → Error) :
    avgOver (uniformDistribution (PointTuple params (n + t)))
        (fun xs => f (pointTuplePrefix params (Nat.le_add_right n t) xs)) =
      avgOver (uniformDistribution (PointTuple params n)) f := by
  induction t with
  | zero =>
      have hprefix (xs : PointTuple params n) :
          pointTuplePrefix params (Nat.le_add_right n 0) xs = xs := by
        funext j
        rfl
      simp only [Nat.add_zero, hprefix]
  | succ t ih =>
      have hsplit := avgOver_uniform_equiv_fst
        (pointTuplePrefixLastEquiv params (n + t))
        (fun ys : PointTuple params (n + t) =>
          f (pointTuplePrefix params (Nat.le_add_right n t) ys))
      have hfun :
          (fun xs : PointTuple params (n + t + 1) =>
            f (pointTuplePrefix params (Nat.le_add_right n (t + 1)) xs)) =
          (fun xs => f (pointTuplePrefix params (Nat.le_add_right n t)
            ((pointTuplePrefixLastEquiv params (n + t)) xs).1)) := by
        funext xs
        congr 1
      simpa only [Nat.add_succ, hfun] using hsplit.trans ih

end MIPStarRE.LDT.Pasting
