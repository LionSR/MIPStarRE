import Mathlib

/-!
Coding-theoretic infrastructure for the MIP*=RE project.

This file gives a deliberately lightweight first abstraction of a linear code on
a finite coordinate type. We model a code as a submodule of the full function
space together with a chosen lower bound on the Hamming distance between distinct
codewords.

The paper's Proposition `prop:distance0` says that enough coordinate values
uniquely determine a codeword. We formalize the corresponding easy consequence
here as `LinearCode.eq_of_agree_on_large_set`.
-/

namespace MIPStarRE.Codes

open scoped BigOperators

section Hamming

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- Hamming distance is bounded by the blocklength. -/
theorem hammingDist_le_blockLength (x y : ι → α) : hammingDist x y ≤ Fintype.card ι := by
  simpa using hammingDist_le_card_fintype (x := x) (y := y)

section

variable [DecidableEq ι]

/-- If two words agree on a set `s`, then they can only differ on the complement of `s`. -/
theorem hammingDist_le_compl_card_of_agreeOn {x y : ι → α} (s : Finset ι)
    (hagree : ∀ i ∈ s, x i = y i) :
    hammingDist x y ≤ (Finset.univ \ s).card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  have hne : x i ≠ y i := by
    simpa using hi
  refine Finset.mem_sdiff.mpr ?_
  constructor
  · simp
  · intro his
    exact hne (hagree i his)

end

/--
If two words agree on at least `|ι| - d + 1` coordinates, then their Hamming
distance is strictly smaller than `d`.
-/
theorem hammingDist_lt_of_agree_on_large_set {x y : ι → α} {d : ℕ}
    (hd : 0 < d) {s : Finset ι}
    (hs : Fintype.card ι - d + 1 ≤ s.card)
    (hagree : ∀ i ∈ s, x i = y i) :
    hammingDist x y < d := by
  classical
  have hle₁ : hammingDist x y ≤ (Finset.univ \ s).card :=
    hammingDist_le_compl_card_of_agreeOn s hagree
  have hcompl : (Finset.univ \ s).card = Fintype.card ι - s.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ s)
  have hle₂ : hammingDist x y ≤ Fintype.card ι - s.card := by
    simpa [hcompl] using hle₁
  omega

end Hamming

/--
A lightweight linear code over a finite coordinate type.

We keep only the ambient linear space of codewords and a chosen minimum-distance
parameter. This is enough for basic uniqueness statements and for setting up the
interpolability/tensor-code interface used later in the project.
-/
structure LinearCode (R ι : Type*) [Semiring R] [Fintype ι] [DecidableEq ι] [DecidableEq R] where
  words : Submodule R (ι → R)
  distance : ℕ
  distance_pos : 0 < distance
  distance_le_blockLength : distance ≤ Fintype.card ι
  minimumDistance : ∀ ⦃x y : words⦄, x ≠ y → distance ≤ hammingDist (x : ι → R) (y : ι → R)

namespace LinearCode

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι] [DecidableEq R]

/-- The type of codewords of `C`. -/
abbrev Word (C : LinearCode R ι) := C.words

/-- The blocklength of a code is the size of its coordinate type. -/
def blockLength (_C : LinearCode R ι) : ℕ :=
  Fintype.card ι

/-- The threshold `n - d + 1` from Proposition `prop:distance0`. -/
def agreementThreshold (C : LinearCode R ι) : ℕ :=
  C.blockLength - C.distance + 1

section Field

variable [Field R]

/-- The dimension of a code is the finrank of its codeword subspace. -/
noncomputable def dimension (C : LinearCode R ι) : ℕ :=
  Module.finrank R C.words

end Field

/-- Distinct codewords cannot be closer than the chosen code distance. -/
theorem distance_le_hammingDist (C : LinearCode R ι) {x y : C.Word} (hxy : x ≠ y) :
    C.distance ≤ hammingDist (x : ι → R) (y : ι → R) :=
  C.minimumDistance hxy

/-- Codewords whose Hamming distance is too small must coincide. -/
theorem eq_of_hammingDist_lt_distance (C : LinearCode R ι) {x y : C.Word}
    (hxy : hammingDist (x : ι → R) (y : ι → R) < C.distance) :
    x = y := by
  by_contra hne
  exact Nat.not_lt_of_ge (C.distance_le_hammingDist hne) hxy

/--
Coordinate-free form of Proposition `prop:distance0`: if two codewords agree on
at least `n - d + 1` coordinates, then they are equal.
-/
theorem eq_of_agree_on_large_set (C : LinearCode R ι) {x y : C.Word} {s : Finset ι}
    (hs : C.agreementThreshold ≤ s.card)
    (hagree : ∀ i ∈ s, (x : ι → R) i = (y : ι → R) i) :
    x = y := by
  apply C.eq_of_hammingDist_lt_distance
  have hs' : Fintype.card ι - C.distance + 1 ≤ s.card := by
    simpa [agreementThreshold, blockLength] using hs
  exact hammingDist_lt_of_agree_on_large_set (d := C.distance) C.distance_pos hs' hagree

/-- The coordinates indexed by a finite set `s`. -/
abbrev Coordinates (s : Finset ι) := {i // i ∈ s}

/--
A code is interpolable if every large enough coordinate set comes with a chosen
linear interpolation map back into the code.

The uniqueness of the reconstructed codeword is not built into the structure: it
is supplied by `eq_of_agree_on_large_set`.
-/
structure Interpolable (C : LinearCode R ι) where
  interpolate :
    ∀ (s : Finset ι), C.agreementThreshold ≤ s.card →
      (Coordinates s → R) →ₗ[R] C.words
  agrees :
    ∀ (s : Finset ι) (hs : C.agreementThreshold ≤ s.card)
      (values : Coordinates s → R) (i : Coordinates s),
      (((interpolate s hs) values : C.words) : ι → R) i.1 = values i

namespace Interpolable

variable {C : LinearCode R ι}

/-- Any codeword matching the prescribed data must equal the chosen interpolation. -/
theorem interpolate_unique (hI : LinearCode.Interpolable C) {s : Finset ι}
    (hs : C.agreementThreshold ≤ s.card) (values : Coordinates s → R)
    {x : C.Word}
    (hagree : ∀ i : Coordinates s, (x : ι → R) i.1 = values i) :
    x = (hI.interpolate s hs) values := by
  apply C.eq_of_agree_on_large_set (s := s) hs
  intro i hi
  let ii : Coordinates s := ⟨i, hi⟩
  exact (hagree ii).trans ((hI.agrees s hs values ii).symm)

end Interpolable

end LinearCode

end MIPStarRE.Codes
