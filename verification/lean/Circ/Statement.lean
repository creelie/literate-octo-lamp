import Mathlib

/-!
# Definitions for Simpson's Conjecture 0.6

A binary circular word of length `n` is a list `w : List Bool` of length `n`, read cyclically,
with `a = true` and `b = false`. Its factors are the words `(w.rotate i).take L` with
`0 ≤ i < n` and `1 ≤ L ≤ n`; as in Simpson's paper, factors longer than `n` are not counted.
-/

namespace Simpson

/-- An abelian square: a word `uv` with `u` nonempty and `P(u) = P(v)`, where `P` is the
Parikh vector (the number of occurrences of each letter). -/
def IsAbelianSquare (s : List Bool) : Prop :=
  ∃ u v, s = u ++ v ∧ u ≠ [] ∧ ∀ c, u.count c = v.count c

/-- The factors of lengths `1, …, n` of the circular word `w` of length `n`. -/
def factors (w : List Bool) : Finset (List Bool) :=
  (Finset.range w.length ×ˢ Finset.Icc 1 w.length).image fun p => (w.rotate p.1).take p.2

open Classical in
/-- The number of distinct abelian squares in the circular word `w`. -/
noncomputable def numDistinctAbelianSquares (w : List Bool) : ℕ :=
  ((factors w).filter IsAbelianSquare).card

/-- `w` is a conjugate (cyclic rotation) of `u`. -/
def IsConj (w u : List Bool) : Prop := ∃ r, w = u.rotate r

/-- The complement, exchanging `a` and `b`. -/
def compl (w : List Bool) : List Bool := w.map (!·)

/-- The word `a^k b^(n-k)`. -/
def blk (k n : ℕ) : List Bool := List.replicate k true ++ List.replicate (n - k) false

/-- The word `abab⋯` of length `n`, that is `(ab)^(n/2)` for even `n`. -/
def alt (n : ℕ) : List Bool := (List.range n).map fun i => decide (i % 2 = 0)

end Simpson
