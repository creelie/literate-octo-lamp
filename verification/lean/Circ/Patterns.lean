import Circ.Classify

/-!
# Upper bounds for the extremal words
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

lemma cnt_congr_mod (hp : Periodic x n) {a b : ℕ} (h : a % n = b % n) (k : ℕ) :
    cnt x ℓ a k = cnt x ℓ b k := by
  rw [← cnt_mod hp a k, h, cnt_mod hp]

lemma window_congr {a b L : ℕ} (h : ∀ t < L, x (a + t) = x (b + t)) :
    window x a L = window x b L := by
  unfold window
  apply List.map_congr_left
  intro t ht
  exact h t (List.mem_range.mp ht)

lemma window_eq_replicate {i L : ℕ} {c : Bool} (h : ∀ t < L, x (i + t) = c) :
    window x i L = List.replicate L c := by
  rw [List.eq_replicate_iff]
  refine ⟨window_length i L, ?_⟩
  intro b hb
  simp only [window, List.mem_map, List.mem_range] at hb
  obtain ⟨t, ht, rfl⟩ := hb
  exact h t ht

/-- Every start is congruent to `s + o` with `o < n`. -/
lemma exists_offset (hn : 0 < n) (s i : ℕ) : ∃ o, o < n ∧ (s + o) % n = i % n := by
  have h1 : s % n < n := Nat.mod_lt _ hn
  have h2 := Nat.mod_add_div s n
  refine ⟨(i % n + n - s % n) % n, Nat.mod_lt _ hn, ?_⟩
  calc (s + (i % n + n - s % n) % n) % n = (s + (i % n + n - s % n)) % n := Nat.add_mod_mod _ _ _
    _ = (i % n + n + n * (s / n)) % n := by congr 1; omega
    _ = i % n := by rw [Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_mod]

lemma add_mod_congr {a b : ℕ} (h : a % n = b % n) (u : ℕ) : (a + u) % n = (b + u) % n := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

lemma shape_mod (hp : Periodic x n) {s : ℕ} {f : ℕ → Bool} (hs : ∀ i, x (s + i) = f i) :
    ∀ i, x (s % n + i) = f i := by
  intro i
  rw [← hs i, ← hp.add_mul (s % n + i) (s / n)]
  congr 1
  have := Nat.mod_add_div s n
  rw [Nat.mul_comm] at this
  omega

section block
variable (hp : Periodic x n) (hn : 0 < n) {s α : ℕ} (hα : α ≤ n)
  (hs : ∀ i, x (s + i) = if i % n < α then ℓ else !ℓ)
include hp hn hα hs

omit hp in
lemma block_cnt (u L : ℕ) (hL : u + L ≤ 2 * n) :
    cnt x ℓ (s + u) L = (min (u + L) α - u) + (min (u + L) (n + α) - max u n) := by
  induction L with
  | zero => simp only [Nat.add_zero, cnt_zero]; omega
  | succ L ih =>
    have hb : (!ℓ) ≠ ℓ := by cases ℓ <;> decide
    have hm : ((u + L) % n = u + L ∧ u + L < n) ∨ (n ≤ u + L ∧ (u + L) % n = u + L - n) := by
      by_cases h : u + L < n
      · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
      · right
        refine ⟨by omega, ?_⟩
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [cnt_succ, ih (by omega), Nat.add_assoc s u L, hs]
    by_cases hc : (u + L) % n < α
    · rw [ite_eq_left hc, ite_eq_left rfl]
      rcases hm with ⟨hm, hm1⟩ | ⟨hm1, hm⟩ <;> rw [hm] at hc <;> omega
    · rw [ite_eq_right hc, ite_eq_right hb]
      rcases hm with ⟨hm, hm1⟩ | ⟨hm1, hm⟩ <;> rw [hm] at hc <;> omega

lemma block_total : total x n ℓ = α := by
  unfold total
  rw [← cnt_period hp s]
  have := block_cnt hn hα hs 0 n (by omega)
  rw [Nat.add_zero] at this
  rw [this]; omega

/-- Under the parity conditions, every abelian square of a block word is constant. -/
lemma block_sq (H1 : α = 0 ∨ α % 2 = 1 ∨ n < α + 2)
    (H2 : α = n ∨ (n - α) % 2 = 1 ∨ n < n - α + 2)
    {i m : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ n) (hsq : IsSq x i m) :
    cnt x ℓ i (2 * m) = 0 ∨ cnt x ℓ i (2 * m) = 2 * m := by
  have hs' := shape_mod hp hs
  have hsn : s % n < n := Nat.mod_lt s hn
  obtain ⟨o, ho, hmod⟩ := exists_offset hn (s % n) i
  have c : ∀ u k, cnt x ℓ (i + u) k = cnt x ℓ (s % n + (o + u)) k := by
    intro u k
    rw [← Nat.add_assoc]
    exact cnt_congr_mod hp (add_mod_congr hmod.symm u) k
  rw [isSq_iff ℓ] at hsq
  have e1 := c 0 m
  have e2 := c m m
  have e3 := c 0 (2 * m)
  simp only [Nat.add_zero] at e1 e3
  have f1 := block_cnt hn hα hs' o m (by omega)
  have f2 := block_cnt hn hα hs' (o + m) m (by omega)
  have f3 := block_cnt hn hα hs' o (2 * m) (by omega)
  omega

lemma block_card_Sset (H1 : α = 0 ∨ α % 2 = 1 ∨ n < α + 2)
    (H2 : α = n ∨ (n - α) % 2 = 1 ∨ n < n - α + 2) {m : ℕ} (hm : 1 ≤ m) (h2m : 2 * m ≤ n) :
    (Sset x n m).card ≤ (if 2 * m ≤ α then 1 else 0) + (if 2 * m ≤ n - α then 1 else 0) := by
  have htot := block_total hp hn hα hs
  have hsum := total_add_total_not x n ℓ
  have hsub : Sset x n m ⊆
      (if 2 * m ≤ α then {List.replicate (2 * m) ℓ} else ∅) ∪
        (if 2 * m ≤ n - α then {List.replicate (2 * m) (!ℓ)} else ∅) := by
    intro w hw
    simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨i, ⟨-, hsq⟩, rfl⟩ := hw
    rcases block_sq hp hn hα hs H1 H2 hm h2m hsq with h0 | h0
    · have hall : ∀ t < 2 * m, x (i + t) = !ℓ :=
        fun t ht => bool_eq_not (((cnt_eq_zero_iff i (2 * m)).mp h0) t ht)
      have hc : cnt x (!ℓ) i (2 * m) = 2 * m := (cnt_eq_len_iff i (2 * m)).mpr hall
      have := cnt_le_total (ℓ := !ℓ) hp i (2 * m) h2m
      have h' : 2 * m ≤ n - α := by omega
      rw [window_eq_replicate hall, ite_eq_left h']
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · have hall : ∀ t < 2 * m, x (i + t) = ℓ := (cnt_eq_len_iff i (2 * m)).mp h0
      have := cnt_le_total (ℓ := ℓ) hp i (2 * m) h2m
      have h' : 2 * m ≤ α := by omega
      rw [window_eq_replicate hall, ite_eq_left h']
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  apply Nat.add_le_add <;> split_ifs <;> simp

end block

lemma sum_ind (a N : ℕ) :
    ∑ m ∈ Finset.Ico 1 (N + 1), (if 2 * m ≤ a then 1 else 0) = min (a / 2) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    split_ifs <;> omega

lemma sum_even (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 (N + 1), (if m % 2 = 0 then 2 else 0) = 2 * (N / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    split_ifs <;> omega

theorem block_upper (hp : Periodic x n) (hn : 0 < n) {α : ℕ} (hα : α ≤ n)
    (hB : BlockShape x n ℓ α) (H1 : α = 0 ∨ α % 2 = 1 ∨ n < α + 2)
    (H2 : α = n ∨ (n - α) % 2 = 1 ∨ n < n - α + 2) : Dint x n ≤ α / 2 + (n - α) / 2 := by
  obtain ⟨s, hs⟩ := hB
  unfold Dint
  calc ∑ m ∈ Finset.Ico 1 (n / 2 + 1), (Sset x n m).card
      ≤ ∑ m ∈ Finset.Ico 1 (n / 2 + 1),
          ((if 2 * m ≤ α then 1 else 0) + (if 2 * m ≤ n - α then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ico] at hm
        exact block_card_Sset hp hn hα hs H1 H2 hm.1 (by omega)
    _ = min (α / 2) (n / 2) + min ((n - α) / 2) (n / 2) := by
        rw [Finset.sum_add_distrib, sum_ind, sum_ind]
    _ ≤ α / 2 + (n - α) / 2 := by omega

section alt
variable (hp : Periodic x n) (hn : 0 < n) {s : ℕ}
  (hs : ∀ i, x (s + i) = if i % 2 = 0 then ℓ else !ℓ)
include hs

omit hp hn in
lemma alt_cnt (u L : ℕ) : cnt x ℓ (s + u) L = (u + L + 1) / 2 - (u + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hb : (!ℓ) ≠ ℓ := by cases ℓ <;> decide
    rw [cnt_succ, ih, Nat.add_assoc s u L, hs]
    by_cases hc : (u + L) % 2 = 0
    · rw [ite_eq_left hc, ite_eq_left rfl]; omega
    · rw [ite_eq_right hc, ite_eq_right hb]; omega

include hp hn

lemma alt_card_Sset {m : ℕ} (hm : 1 ≤ m) :
    (Sset x n m).card ≤ if m % 2 = 0 then 2 else 0 := by
  have hs' := shape_mod hp hs
  have hsn : s % n < n := Nat.mod_lt s hn
  have key : ∀ i, IsSq x i m → m % 2 = 0 ∧
      (window x i (2 * m) = window x (s % n) (2 * m) ∨
        window x i (2 * m) = window x (s % n + 1) (2 * m)) := by
    intro i hsq
    obtain ⟨o, ho, hmod⟩ := exists_offset hn (s % n) i
    have c : ∀ u k, cnt x ℓ (i + u) k = cnt x ℓ (s % n + (o + u)) k := by
      intro u k
      rw [← Nat.add_assoc]
      exact cnt_congr_mod hp (add_mod_congr hmod.symm u) k
    rw [isSq_iff ℓ] at hsq
    have e1 := c 0 m
    have e2 := c m m
    simp only [Nat.add_zero] at e1
    have f1 := alt_cnt hs' o m
    have f2 := alt_cnt hs' (o + m) m
    refine ⟨by omega, ?_⟩
    have hw : window x i (2 * m) = window x (s % n + o) (2 * m) := by
      rw [← window_mod hp i, ← hmod, window_mod hp]
    rw [hw]
    rcases Nat.mod_two_eq_zero_or_one o with h0 | h0
    · left
      apply window_congr
      intro t _
      rw [Nat.add_assoc, hs', hs', show (o + t) % 2 = t % 2 by omega]
    · right
      apply window_congr
      intro t _
      rw [Nat.add_assoc, Nat.add_assoc, hs', hs', show (o + t) % 2 = (1 + t) % 2 by omega]
  split_ifs with he
  · have hsub : Sset x n m ⊆ {window x (s % n) (2 * m), window x (s % n + 1) (2 * m)} := by
      intro w hw
      simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hw
      obtain ⟨i, ⟨-, hsq⟩, rfl⟩ := hw
      rcases (key i hsq).2 with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨i, ⟨-, hsq⟩, -⟩ := hw
    exact he (key i hsq).1

theorem alt_upper : Dint x n ≤ 2 * ((n / 2) / 2) := by
  unfold Dint
  calc ∑ m ∈ Finset.Ico 1 (n / 2 + 1), (Sset x n m).card
      ≤ ∑ m ∈ Finset.Ico 1 (n / 2 + 1), (if m % 2 = 0 then 2 else 0) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ico] at hm
        exact alt_card_Sset hp hn hs hm.1
    _ = 2 * ((n / 2) / 2) := sum_even _

end alt

end Circ
