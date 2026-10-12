import Circ.Patterns

/-!
# The minimum and the extremal words, for periodic bit sequences
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

/-- The extremal words: `ℓ^n`, `ℓ^(n-1) (!ℓ)` for odd `n`; `ℓ^k (!ℓ)^(n-k)` with `k` odd,
and `(ℓ (!ℓ))^(n/2)` when `n ≡ 2 (mod 4)`, for even `n`; up to rotation. -/
def ExtremalX (x : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ ℓ, (n % 2 = 1 ∧ (BlockShape x n ℓ n ∨ BlockShape x n ℓ (n - 1))) ∨
    (n % 2 = 0 ∧ ((∃ k, k % 2 = 1 ∧ k < n ∧ BlockShape x n ℓ k) ∨ (n % 4 = 2 ∧ AltShape x ℓ)))

theorem extremal_upper (hp : Periodic x n) (hn : 0 < n) (h : ExtremalX x n) :
    Dint x n ≤ (n - 1) / 2 := by
  obtain ⟨ℓ, ⟨ho, hB | hB⟩ | ⟨he, ⟨k, hk, hkn, hB⟩ | ⟨h4, s, hs⟩⟩⟩ := h
  · have := block_upper hp hn le_rfl hB (Or.inr (Or.inl ho)) (Or.inl rfl)
    omega
  · have := block_upper hp hn (Nat.sub_le n 1) hB (Or.inr (Or.inr (by omega)))
      (Or.inr (Or.inl (by omega)))
    omega
  · have := block_upper hp hn hkn.le hB (Or.inr (Or.inl hk)) (Or.inr (Or.inl (by omega)))
    omega
  · have := alt_upper hp hn hs
    omega

/-- A constant word. -/
lemma block_full (hp : Periodic x n) (hn : 0 < n) (h : total x n ℓ = n) :
    BlockShape x n ℓ n := by
  refine ⟨0, fun i => ?_⟩
  have hall := (cnt_eq_len_iff (x := x) (ℓ := ℓ) 0 n).mp h
  have hi := Nat.mod_lt i hn
  rw [ite_eq_left hi, Nat.zero_add, ← hp.mod i]
  simpa using hall _ hi

/-- `ℓ^α (!ℓ)^(n-α)` is a rotation of `(!ℓ)^(n-α) ℓ^α`. -/
lemma block_flip (hn : 0 < n) {α : ℕ} (hα : α ≤ n) (hB : BlockShape x n ℓ α) :
    BlockShape x n (!ℓ) (n - α) := by
  obtain ⟨s, hs⟩ := hB
  refine ⟨s + α, fun i => ?_⟩
  rw [Nat.add_assoc, hs, ← Nat.add_mod_mod]
  have hr := Nat.mod_lt i hn
  by_cases h : i % n < n - α
  · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega), ite_eq_left h]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega),
      ite_eq_right h, Bool.not_not]

/-- A column with `c` entries adds `c - 1` to the lower bound of `sum_col_ge`. -/
lemma sum_col_fat (hp : Periodic x n) (ℓ : Bool) {k₀ c : ℕ} (hk1 : 1 ≤ k₀)
    (hk2 : k₀ < total x n ℓ) (hc : c ≤ (col x n ℓ k₀).card) (hc1 : 1 ≤ c) :
    total x n ℓ - 1 + (c - 1) ≤ ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
  have htn : total x n ℓ ≤ n := by
    have := total_add_total_not x n ℓ; omega
  have hmem : k₀ ∈ Finset.Ico 1 (total x n ℓ) := Finset.mem_Ico.mpr ⟨hk1, hk2⟩
  calc total x n ℓ - 1 + (c - 1)
      = ∑ k ∈ Finset.Ico 1 (total x n ℓ), (1 + if k = k₀ then c - 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left hmem]
        simp
    _ ≤ ∑ k ∈ Finset.Ico 1 (total x n ℓ), (col x n ℓ k).card := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Ico] at hk
        have := Finset.card_pos.mpr (col_nonempty hp hk.1 hk.2)
        split_ifs with h
        · subst h; omega
        · omega
    _ ≤ ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        simp only [Finset.mem_Ico, Finset.mem_range] at *
        omega

/-- In `ℓ^α (!ℓ)^(2h)` with `α ≥ 3`, column `h` of `!ℓ` has at least three entries. -/
lemma fat_column (hp : Periodic x n) (hn : 0 < n) {s α h : ℕ} (hα3 : 3 ≤ α) (hh : 1 ≤ h)
    (hnα : n = α + 2 * h) (hs : ∀ i, x (s + i) = if i % n < α then ℓ else !ℓ) :
    3 ≤ (col x n (!ℓ) h).card := by
  have hα : α ≤ n := by omega
  have htot := block_total hp hn hα hs
  have hsum := total_add_total_not x n ℓ
  have hnl : x (s + (α + h - 1)) = !ℓ := by
    rw [hs, Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega)]
  -- `(!ℓ)^(2h)` itself
  have m1 : h ∈ col x n (!ℓ) h := by
    rw [mem_col]
    refine ⟨hh, by omega, s + α, ?_, ?_, ?_⟩
    · rw [Nat.add_assoc, show α + (h - 1) = α + h - 1 by omega, hnl]
    · rw [isSq_iff ℓ, Nat.add_assoc, block_cnt hn hα hs α h (by omega),
        block_cnt hn hα hs (α + h) h (by omega)]
      omega
    · have a := cnt_add_cnt_not (x := x) (ℓ := ℓ) (s + α) h
      rw [block_cnt hn hα hs α h (by omega)] at a
      omega
  -- `ℓ (!ℓ)^(2h) ℓ`
  have m2 : h + 1 ∈ col x n (!ℓ) h := by
    rw [mem_col]
    refine ⟨by omega, by omega, s + (α - 1), ?_, ?_, ?_⟩
    · rw [Nat.add_assoc, show α - 1 + (h + 1 - 1) = α + h - 1 by omega, hnl]
    · rw [isSq_iff ℓ, Nat.add_assoc, block_cnt hn hα hs (α - 1) (h + 1) (by omega),
        block_cnt hn hα hs (α - 1 + (h + 1)) (h + 1) (by omega)]
      omega
    · have a := cnt_add_cnt_not (x := x) (ℓ := ℓ) (s + (α - 1)) (h + 1)
      rw [block_cnt hn hα hs (α - 1) (h + 1) (by omega)] at a
      omega
  have m3 : n - h ∈ col x n (!ℓ) h := by
    have := col_mirror hp m1
    rwa [show total x n (!ℓ) - h = h by omega] at this
  have hsub : ({h, h + 1, n - h} : Finset ℕ) ⊆ col x n (!ℓ) h := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact m1
    · exact m2
    · exact m3
  have h3 : ({h, h + 1, n - h} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨h, h + 1, n - h, by omega, by omega, by omega, rfl⟩
  rw [← h3]
  exact Finset.card_le_card hsub

/-- Odd `n`, both letters present, `ℓ` tight and `!ℓ` with one spare entry. -/
lemma odd_case (hp : Periodic x n) (hn : 0 < n) (hR : Rigid x n) (hodd : n % 2 = 1)
    (ht : 0 < total x n ℓ) (ht' : 0 < total x n (!ℓ))
    (hS : ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card ≤ total x n ℓ - 1)
    (hS' : ∑ k ∈ Finset.range (n + 1), (col x n (!ℓ) k).card ≤ total x n (!ℓ)) :
    ExtremalX x n := by
  have hsum := total_add_total_not x n ℓ
  have hT := tight_of_sum hp ℓ hS
  rcases classify hp ht hT hR with ⟨⟨s, hs⟩, hodd' | hfull⟩ | ⟨h2, -⟩
  · by_cases h1 : total x n ℓ = 1
    · refine ⟨!ℓ, Or.inl ⟨hodd, Or.inr ?_⟩⟩
      have := block_flip hn (by omega) ⟨s, hs⟩
      rwa [h1] at this
    · exfalso
      have hfat := fat_column hp hn (h := total x n (!ℓ) / 2) (by omega) (by omega) (by omega) hs
      have hβ := block_total hp hn (by omega) hs
      have := sum_col_fat hp (!ℓ) (k₀ := total x n (!ℓ) / 2) (by omega) (by omega) hfat (by omega)
      omega
  · omega
  · omega

theorem extremal_of_eq (hp : Periodic x n) (hn : 0 < n) (hD : Dint x n = (n - 1) / 2) :
    ExtremalX x n := by
  obtain ⟨hR, hN⟩ := equality_facts hp hn hD
  unfold Nsum at hN
  rw [sum_Qset_eq, Fintype.sum_bool] at hN
  have gt := sum_col_ge hp (x := x) true
  have gf := sum_col_ge hp (x := x) false
  have hsum := total_add_total_not x n true
  simp only [Bool.not_true] at hsum
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [ite_eq_left he] at hN
    have ht : 0 < total x n true := by
      by_contra h0; omega
    have hf : 0 < total x n false := by
      by_contra h0; omega
    have hQ : (Qset x n (n / 2)).card = 0 := by omega
    have hT := tight_of_sum hp true (by omega)
    rcases classify hp ht hT hR with ⟨hB, hodd' | hfull⟩ | ⟨h2, s, hs⟩
    · exact ⟨true, Or.inr ⟨he, Or.inl ⟨total x n true, hodd', by omega, hB⟩⟩⟩
    · omega
    · refine ⟨true, Or.inr ⟨he, Or.inr ⟨?_, s, hs⟩⟩⟩
      by_contra h4
      have hsq : IsSq x s (n / 2) := by
        rw [isSq_iff true]
        have a := alt_cnt hs 0 (n / 2)
        have b := alt_cnt hs (n / 2) (n / 2)
        rw [Nat.add_zero] at a
        omega
      exact not_isSq_of_Qset_empty hp (by omega) (by omega) hQ s hsq
  · rw [ite_eq_right (by omega)] at hN
    by_cases ht : total x n true = 0
    · exact ⟨false, Or.inl ⟨ho, Or.inl (block_full hp hn (by omega))⟩⟩
    by_cases hf : total x n false = 0
    · exact ⟨true, Or.inl ⟨ho, Or.inl (block_full hp hn (by omega))⟩⟩
    by_cases hc : ∑ k ∈ Finset.range (n + 1), (col x n true k).card ≤ total x n true - 1
    · exact odd_case (ℓ := true) hp hn hR ho (by omega) (by simpa using Nat.pos_of_ne_zero hf) hc (by simp; omega)
    · exact odd_case (ℓ := false) hp hn hR ho (by omega) (by simpa using Nat.pos_of_ne_zero ht) (by omega)
        (by simp; omega)

/-- The minimum number of distinct abelian squares and the words attaining it. -/
theorem main_x (hp : Periodic x n) (hn : 0 < n) :
    (n - 1) / 2 ≤ Dint x n ∧ (Dint x n = (n - 1) / 2 ↔ ExtremalX x n) :=
  ⟨lower_bound hp hn, fun h => extremal_of_eq hp hn h,
    fun h => le_antisymm (extremal_upper hp hn h) (lower_bound hp hn)⟩

end Circ
