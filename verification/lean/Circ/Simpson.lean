import Circ.Bridge

/-!
# Simpson's Conjecture 0.6 on distinct abelian squares in binary circular words

`Simpson.min_distinct`: the minimum number of distinct abelian squares in a binary circular word
of length `n ≥ 1` is `⌊(n-1)/2⌋`.

`Simpson.extremal_odd`, `Simpson.extremal_even`: the circular words attaining it.

`Simpson.conjectureA`: part (a) of the conjecture holds.

`Simpson.not_conjectureB`, `Simpson.counterexample`: part (b) fails; `(ab)^3` is extremal and is
not a conjugate of `a^k b^(6-k)` or of its complement.
-/

open Classical

namespace Simpson

open Circ

lemma map_block (n α : ℕ) (hα : α ≤ n) (ℓ : Bool) :
    (List.range n).map (fun t => if t < α then ℓ else !ℓ) =
      List.replicate α ℓ ++ List.replicate (n - α) (!ℓ) := by
  apply List.ext_getElem
  · simp; omega
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    by_cases ht : t < α
    · rw [ite_eq_left ht, List.getElem_append_left (by simpa using ht)]
      simp
    · rw [ite_eq_right ht, List.getElem_append_right (by simp; omega)]
      simp

lemma compl_blk (k n : ℕ) :
    compl (blk k n) = List.replicate k false ++ List.replicate (n - k) true := by
  simp [compl, blk, List.map_replicate]

lemma map_alt_true (n : ℕ) :
    (List.range n).map (fun t => if t % 2 = 0 then true else !true) = alt n := by
  unfold alt
  apply List.map_congr_left
  intro t _
  by_cases h : t % 2 = 0 <;> simp [h]

lemma map_alt_false (n : ℕ) :
    (List.range n).map (fun t => if t % 2 = 0 then false else !false) = compl (alt n) := by
  unfold alt compl
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  by_cases h : t % 2 = 0 <;> simp [h]

section
variable {w : List Bool} (hn : 0 < w.length)
include hn

lemma block_true {α : ℕ} (hα : α ≤ w.length) :
    BlockShape (seq w) w.length true α ↔ IsConj w (blk α w.length) := by
  have := shape_iff_conj w hn (fun t => if t < α then true else !true)
  rw [map_block _ _ hα] at this
  exact this

lemma block_false {α : ℕ} (hα : α ≤ w.length) :
    BlockShape (seq w) w.length false α ↔ IsConj w (compl (blk α w.length)) := by
  have := shape_iff_conj w hn (fun t => if t < α then false else !false)
  rw [map_block _ _ hα, Bool.not_false, ← compl_blk] at this
  exact this

lemma alt_iff (he : w.length % 2 = 0) (ℓ : Bool) :
    AltShape (seq w) ℓ ↔
      IsConj w ((List.range w.length).map (fun t => if t % 2 = 0 then ℓ else !ℓ)) := by
  rw [← shape_iff_conj w hn]
  unfold AltShape
  simp only [Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero he)]

end

/-- The lower bound: every binary circular word of length `n ≥ 1` contains at least
`⌊(n-1)/2⌋` distinct abelian squares. -/
theorem lower_bound {w : List Bool} (hn : 0 < w.length) :
    (w.length - 1) / 2 ≤ numDistinctAbelianSquares w := by
  rw [num_eq_Dint w hn]
  exact Circ.lower_bound (seq_periodic w) hn

/-- Odd length: the words with `(n-1)/2` distinct abelian squares are the conjugates of
`a^n`, `a^(n-1) b` and of their complements. -/
theorem extremal_odd {w : List Bool} (ho : w.length % 2 = 1) :
    numDistinctAbelianSquares w = (w.length - 1) / 2 ↔
      IsConj w (blk w.length w.length) ∨ IsConj w (blk (w.length - 1) w.length) ∨
        IsConj w (compl (blk w.length w.length)) ∨
          IsConj w (compl (blk (w.length - 1) w.length)) := by
  have hn : 0 < w.length := by omega
  rw [num_eq_Dint w hn, (main_x (seq_periodic w) hn).2, ExtremalX, Bool.exists_bool,
    block_true hn le_rfl, block_true hn (Nat.sub_le _ _), block_false hn le_rfl,
    block_false hn (Nat.sub_le _ _)]
  constructor
  · rintro ((⟨-, h | h⟩ | ⟨he, -⟩) | (⟨-, h | h⟩ | ⟨he, -⟩))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · omega
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl ⟨ho, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨ho, Or.inr h⟩)
    · exact Or.inl (Or.inl ⟨ho, Or.inl h⟩)
    · exact Or.inl (Or.inl ⟨ho, Or.inr h⟩)

/-- Even length: the words with `(n-2)/2` distinct abelian squares are the conjugates of
`a^k b^(n-k)` with `k` odd and of their complements, and, when `n ≡ 2 (mod 4)`, the
conjugates of `(ab)^(n/2)`. -/
theorem extremal_even {w : List Bool} (he : w.length % 2 = 0) (hn : 0 < w.length) :
    numDistinctAbelianSquares w = (w.length - 2) / 2 ↔
      (∃ k, k % 2 = 1 ∧ k < w.length ∧
          (IsConj w (blk k w.length) ∨ IsConj w (compl (blk k w.length)))) ∨
        (w.length % 4 = 2 ∧ (IsConj w (alt w.length) ∨ IsConj w (compl (alt w.length)))) := by
  rw [show (w.length - 2) / 2 = (w.length - 1) / 2 by omega, num_eq_Dint w hn,
    (main_x (seq_periodic w) hn).2, ExtremalX, Bool.exists_bool, alt_iff hn he, alt_iff hn he,
    map_alt_true, map_alt_false]
  constructor
  · rintro ((⟨h, -⟩ | ⟨-, ⟨k, hk, hkn, h⟩ | ⟨h4, h⟩⟩) | (⟨h, -⟩ | ⟨-, ⟨k, hk, hkn, h⟩ | ⟨h4, h⟩⟩))
    · omega
    · exact Or.inl ⟨k, hk, hkn, Or.inr ((block_false hn hkn.le).mp h)⟩
    · exact Or.inr ⟨h4, Or.inr h⟩
    · omega
    · exact Or.inl ⟨k, hk, hkn, Or.inl ((block_true hn hkn.le).mp h)⟩
    · exact Or.inr ⟨h4, Or.inl h⟩
  · rintro (⟨k, hk, hkn, h | h⟩ | ⟨h4, h | h⟩)
    · exact Or.inr (Or.inr ⟨he, Or.inl ⟨k, hk, hkn, (block_true hn hkn.le).mpr h⟩⟩)
    · exact Or.inl (Or.inr ⟨he, Or.inl ⟨k, hk, hkn, (block_false hn hkn.le).mpr h⟩⟩)
    · exact Or.inr (Or.inr ⟨he, Or.inr ⟨h4, h⟩⟩)
    · exact Or.inl (Or.inr ⟨he, Or.inr ⟨h4, h⟩⟩)

lemma isConj_self (w : List Bool) : IsConj w w := ⟨0, (List.rotate_zero w).symm⟩

@[simp] lemma length_blk (k n : ℕ) (hk : k ≤ n) : (blk k n).length = n := by
  simp [blk]; omega

/-- The minimum number of distinct abelian squares in a binary circular word of length
`n ≥ 1` is `⌊(n-1)/2⌋`. -/
theorem min_distinct {n : ℕ} (hn : 0 < n) :
    IsLeast {d | ∃ w : List Bool, w.length = n ∧ numDistinctAbelianSquares w = d}
      ((n - 1) / 2) := by
  refine ⟨?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · refine ⟨blk 1 n, length_blk 1 n hn, ?_⟩
      have h := (extremal_even (w := blk 1 n) (by rw [length_blk 1 n hn]; exact he)
        (by rw [length_blk 1 n hn]; exact hn)).mpr
      rw [length_blk 1 n hn] at h
      rw [h (Or.inl ⟨1, rfl, by omega, Or.inl (isConj_self _)⟩)]
      omega
    · refine ⟨blk n n, length_blk n n le_rfl, ?_⟩
      have h := (extremal_odd (w := blk n n) (by rw [length_blk n n le_rfl]; exact ho)).mpr
      rw [length_blk n n le_rfl] at h
      exact h (Or.inl (isConj_self _))
  · rintro d ⟨w, rfl, rfl⟩
    exact lower_bound hn

/-- Simpson's Conjecture 0.6 (a). -/
def ConjectureA : Prop :=
  ∀ n : ℕ, n % 2 = 1 →
    IsLeast {d | ∃ w : List Bool, w.length = n ∧ numDistinctAbelianSquares w = d} ((n - 1) / 2) ∧
      ∀ w : List Bool, w.length = n →
        (numDistinctAbelianSquares w = (n - 1) / 2 ↔
          IsConj w (blk n n) ∨ IsConj w (blk (n - 1) n) ∨ IsConj w (compl (blk n n)) ∨
            IsConj w (compl (blk (n - 1) n)))

/-- Simpson's Conjecture 0.6 (b). -/
def ConjectureB : Prop :=
  ∀ n : ℕ, n % 2 = 0 → 0 < n →
    IsLeast {d | ∃ w : List Bool, w.length = n ∧ numDistinctAbelianSquares w = d} ((n - 2) / 2) ∧
      ∀ w : List Bool, w.length = n →
        (numDistinctAbelianSquares w = (n - 2) / 2 ↔
          ∃ k, k % 2 = 1 ∧ k < n ∧ (IsConj w (blk k n) ∨ IsConj w (compl (blk k n))))

theorem conjectureA : ConjectureA := by
  intro n ho
  refine ⟨min_distinct (by omega), ?_⟩
  rintro w rfl
  exact extremal_odd ho

@[simp] lemma length_alt (n : ℕ) : (alt n).length = n := by simp [alt]

/-- `(ab)^3` has two distinct abelian squares, the minimum for length `6`, and it is not a
conjugate of `a^k b^(6-k)` or of its complement. -/
theorem counterexample :
    numDistinctAbelianSquares (alt 6) = 2 ∧
      ∀ k, ¬ IsConj (alt 6) (blk k 6) ∧ ¬ IsConj (alt 6) (compl (blk k 6)) := by
  refine ⟨?_, fun k => ⟨?_, ?_⟩⟩
  · have h := (extremal_even (w := alt 6) (by simp) (by simp)).mpr
    simp only [length_alt] at h
    exact h (Or.inr ⟨by decide, Or.inl (isConj_self _)⟩)
  · rintro ⟨r, hr⟩
    have hk : k ≤ 6 := by
      have := congrArg List.length hr
      simp [blk] at this
      omega
    rw [← List.rotate_mod, length_blk k 6 hk] at hr
    have key : ∀ k ≤ 6, ∀ r < 6, alt 6 ≠ (blk k 6).rotate r := by decide
    exact key k hk (r % 6) (Nat.mod_lt _ (by norm_num)) hr
  · rintro ⟨r, hr⟩
    have hk : k ≤ 6 := by
      have := congrArg List.length hr
      simp [blk, compl] at this
      omega
    rw [← List.rotate_mod, show (compl (blk k 6)).length = 6 by simp [compl, blk]; omega] at hr
    have key : ∀ k ≤ 6, ∀ r < 6, alt 6 ≠ (compl (blk k 6)).rotate r := by decide
    exact key k hk (r % 6) (Nat.mod_lt _ (by norm_num)) hr

theorem not_conjectureB : ¬ ConjectureB := by
  intro h
  obtain ⟨k, -, -, hc⟩ := ((h 6 rfl (by norm_num)).2 (alt 6) (length_alt 6)).mp
    (by rw [counterexample.1])
  rcases hc with hc | hc
  · exact (counterexample.2 k).1 hc
  · exact (counterexample.2 k).2 hc

end Simpson
