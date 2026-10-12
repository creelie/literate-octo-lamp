import Circ.Squares

/-!
# Runs of a tight letter

`pos x ℓ` enumerates the occurrences of `ℓ`. Squares are produced from the positions of
occurrences, and the runs of `ℓ` are described through these positions.
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

/-- `x (s + i)` is `ℓ` exactly when `i mod n < α`: a rotation of `ℓ^α (!ℓ)^(n-α)`. -/
def BlockShape (x : ℕ → Bool) (n : ℕ) (ℓ : Bool) (α : ℕ) : Prop :=
  ∃ s, ∀ i, x (s + i) = if i % n < α then ℓ else !ℓ

/-- A rotation of `(ℓ (!ℓ))^∞`. -/
def AltShape (x : ℕ → Bool) (ℓ : Bool) : Prop :=
  ∃ s, ∀ i, x (s + i) = if i % 2 = 0 then ℓ else !ℓ

/-- The occurrences `J+1, …, J+L` of `ℓ` are adjacent, with a gap before and after. -/
def RunAt (x : ℕ → Bool) (ℓ : Bool) (J L : ℕ) : Prop :=
  1 ≤ L ∧ pos x ℓ J + 2 ≤ pos x ℓ (J + 1) ∧
    (∀ t, t < L → pos x ℓ (J + 1 + t) = pos x ℓ (J + 1) + t) ∧
    pos x ℓ (J + L) + 2 ≤ pos x ℓ (J + L + 1)

lemma consec {f : ℕ → ℕ} {a L : ℕ} (h : ∀ t, t + 1 < L → f (a + 1 + t) = f (a + t) + 1) :
    ∀ t, t < L → f (a + t) = f a + t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro htL
    rw [show a + (t + 1) = a + 1 + t by omega, h t htL, ih (by omega)]
    omega

lemma bool_eq_not {b ℓ : Bool} (h : b ≠ ℓ) : b = !ℓ := by
  cases b <;> cases ℓ <;> simp_all

section
variable (hp : Periodic x n) (ht : 0 < total x n ℓ)
include hp ht

/-- A square whose left half holds the occurrences `j+1, …, j+k` and ends at the last. -/
lemma sq_of_pos {j k m : ℕ} (hk : 1 ≤ k)
    (h1 : pos x ℓ j + m < pos x ℓ (j + k) + 1)
    (h2 : pos x ℓ (j + k) + 1 ≤ pos x ℓ (j + 1) + m)
    (h3 : pos x ℓ (j + 2 * k) < pos x ℓ (j + k) + 1 + m)
    (h4 : pos x ℓ (j + k) + 1 + m ≤ pos x ℓ (j + 2 * k + 1)) :
    1 ≤ m ∧ x (pos x ℓ (j + k) + 1 - m + (m - 1)) = ℓ ∧
      IsSq x (pos x ℓ (j + k) + 1 - m) m ∧ cnt x ℓ (pos x ℓ (j + k) + 1 - m) m = k := by
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have f1 := pos_add_le hp ht (j + k) k
  have f2 := pos_lt_succ hp ht (j + k)
  have i1 := P (j + k + k) (j + 2 * k) (by omega)
  have i2 := P (j + k + k + 1) (j + 2 * k + 1) (by omega)
  have hm : 1 ≤ m := by omega
  have hcL : cnt x ℓ (pos x ℓ (j + k) + 1 - m) m = k := by
    apply cnt_between hp ht (j := j) (t := k) <;> omega
  have hcR : cnt x ℓ (pos x ℓ (j + k) + 1 - m + m) m = k := by
    apply cnt_between hp ht (j := j + k) (t := k) <;> omega
  refine ⟨hm, ?_, ?_, hcL⟩
  · rw [show pos x ℓ (j + k) + 1 - m + (m - 1) = pos x ℓ (j + k) by omega]
    exact pos_spec hp ht _
  · rw [isSq_iff ℓ, hcL, hcR]

lemma col_of_pos {j k m : ℕ} (hk : 1 ≤ k) (hkt : k < total x n ℓ)
    (h1 : pos x ℓ j + m < pos x ℓ (j + k) + 1)
    (h2 : pos x ℓ (j + k) + 1 ≤ pos x ℓ (j + 1) + m)
    (h3 : pos x ℓ (j + 2 * k) < pos x ℓ (j + k) + 1 + m)
    (h4 : pos x ℓ (j + k) + 1 + m ≤ pos x ℓ (j + 2 * k + 1)) : m ∈ col x n ℓ k := by
  obtain ⟨hm, hx, hsq, hc⟩ := sq_of_pos hp ht hk h1 h2 h3 h4
  rw [mem_col]
  exact ⟨hm, lt_of_cnt_lt_total hp (by rw [hc]; exact hkt), _, hx, hsq, hc⟩

lemma total_le : total x n ℓ ≤ n := by
  have := total_add_total_not x n ℓ; omega

lemma RunAt.le_total {J L : ℕ} (h : RunAt x ℓ J L) : L ≤ total x n ℓ := by
  obtain ⟨hL, hg, hi, he⟩ := h
  by_contra hc
  push Not at hc
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have a1 := hi (total x n ℓ) hc
  have a2 := hi (total x n ℓ - 1) (by omega)
  have b1 := pos_add_total hp ht J
  have b2 := pos_add_total hp ht (J + 1)
  have e1 := P (J + 1 + (total x n ℓ - 1)) (J + total x n ℓ) (by omega)
  omega

lemma RunAt.shift {J L : ℕ} (h : RunAt x ℓ J L) : RunAt x ℓ (J + total x n ℓ) L := by
  obtain ⟨hL, hg, hi, he⟩ := h
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have per := pos_add_total hp ht
  have q1 := per J
  have q2 := per (J + 1)
  have q3 := P (J + total x n ℓ + 1) (J + 1 + total x n ℓ) (by omega)
  refine ⟨hL, by omega, ?_, ?_⟩
  · intro t htL
    have := hi t htL
    have := per (J + 1 + t)
    have := P (J + total x n ℓ + 1 + t) (J + 1 + t + total x n ℓ) (by omega)
    omega
  · have := per (J + L)
    have := per (J + L + 1)
    have := P (J + total x n ℓ + L) (J + L + total x n ℓ) (by omega)
    have := P (J + total x n ℓ + L + 1) (J + L + 1 + total x n ℓ) (by omega)
    omega

/-- After a gap, the occurrences form a run of some length. -/
lemma run_next {J : ℕ} (hg : pos x ℓ J + 2 ≤ pos x ℓ (J + 1)) : ∃ L, RunAt x ℓ J L := by
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have hex : ∃ t, pos x ℓ (J + 1 + t) + 2 ≤ pos x ℓ (J + 2 + t) := by
    refine ⟨total x n ℓ - 1, ?_⟩
    have := pos_add_total hp ht J
    have := pos_add_total hp ht (J + 1)
    have := P (J + 1 + (total x n ℓ - 1)) (J + total x n ℓ) (by omega)
    have := P (J + 2 + (total x n ℓ - 1)) (J + 1 + total x n ℓ) (by omega)
    omega
  refine ⟨Nat.find hex + 1, by omega, hg, ?_, ?_⟩
  · apply consec (f := pos x ℓ) (a := J + 1)
    intro t htL
    have hmin := Nat.find_min hex (show t < Nat.find hex by omega)
    have := pos_lt_succ hp ht (J + 1 + t)
    have := P (J + 1 + 1 + t) (J + 2 + t) (by omega)
    have := P (J + 1 + t + 1) (J + 2 + t) (by omega)
    omega
  · have := Nat.find_spec hex
    have := P (J + (Nat.find hex + 1)) (J + 1 + Nat.find hex) (by omega)
    have := P (J + (Nat.find hex + 1) + 1) (J + 2 + Nat.find hex) (by omega)
    omega

/-- Before a gap, the occurrences form a run of some length. -/
lemma run_prev {J : ℕ} (hg : pos x ℓ J + 2 ≤ pos x ℓ (J + 1)) :
    ∃ J' L, RunAt x ℓ J' L ∧ J' + L = J + total x n ℓ := by
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have hex : ∃ s, 1 ≤ s ∧ s ≤ J + total x n ℓ ∧
      pos x ℓ (J + total x n ℓ - s) + 2 ≤ pos x ℓ (J + total x n ℓ - s + 1) := by
    refine ⟨total x n ℓ, ht, by omega, ?_⟩
    rw [show J + total x n ℓ - total x n ℓ = J by omega]; exact hg
  obtain ⟨hs1, hsK, hsg⟩ := Nat.find_spec hex
  refine ⟨J + total x n ℓ - Nat.find hex, Nat.find hex, ⟨hs1, hsg, ?_, ?_⟩, by omega⟩
  · apply consec (f := pos x ℓ) (a := J + total x n ℓ - Nat.find hex + 1)
    intro t htL
    have hmin := Nat.find_min hex (show Nat.find hex - 1 - t < Nat.find hex by omega)
    push Not at hmin
    have h3 := hmin (by omega) (by omega)
    have := pos_lt_succ hp ht (J + total x n ℓ - Nat.find hex + 1 + t)
    have := P (J + total x n ℓ - (Nat.find hex - 1 - t))
      (J + total x n ℓ - Nat.find hex + 1 + t) (by omega)
    have := P (J + total x n ℓ - (Nat.find hex - 1 - t) + 1)
      (J + total x n ℓ - Nat.find hex + 1 + 1 + t) (by omega)
    have := P (J + total x n ℓ - Nat.find hex + 1 + t + 1)
      (J + total x n ℓ - Nat.find hex + 1 + 1 + t) (by omega)
    omega
  · have := pos_add_total hp ht J
    have := pos_add_total hp ht (J + 1)
    have := P (J + total x n ℓ - Nat.find hex + Nat.find hex) (J + total x n ℓ) (by omega)
    have := P (J + total x n ℓ - Nat.find hex + Nat.find hex + 1) (J + 1 + total x n ℓ)
      (by omega)
    omega

section tight
variable (hT : Tight x n ℓ)
include hT

/-- Every run of a tight letter has odd length. -/
lemma RunAt.odd {J L : ℕ} (h : RunAt x ℓ J L) : L % 2 = 1 := by
  have hLt := h.le_total hp ht
  obtain ⟨hL, hg, hi, he⟩ := h
  by_contra hodd
  obtain ⟨i, rfl⟩ : ∃ i, L = 2 * i := ⟨L / 2, by omega⟩
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have a1 := hi (i - 1) (by omega)
  have a2 := hi (2 * i - 1) (by omega)
  have e1 := P (J + 1 + (i - 1)) (J + i) (by omega)
  have e2 := P (J + 1 + (2 * i - 1)) (J + 2 * i) (by omega)
  have hm : ∀ m, i ≤ m → m ≤ i + 1 → m ∈ col x n ℓ i := by
    intro m hm1 hm2
    apply col_of_pos hp ht (j := J) (k := i) (by omega) (by omega) <;> omega
  exact absurd (hT i i (i + 1) (hm i le_rfl (by omega)) (hm (i + 1) (by omega) le_rfl))
    (by omega)

/-- The square around a run of length `2h+1` with left half `ℓ (!ℓ)^g ℓ^h`. -/
lemma run_sq_left {J h : ℕ} (hJ : 1 ≤ J) (hr : RunAt x ℓ J (2 * h + 1)) (hh : 1 ≤ h)
    (hk : h + 1 < total x n ℓ)
    (hg : pos x ℓ (J + 1) - pos x ℓ J ≤ pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1))) :
    pos x ℓ (J + 1) - pos x ℓ J + h ∈ col x n ℓ (h + 1) := by
  obtain ⟨-, hg1, hi, he⟩ := hr
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have b1 := hi (h - 1) (by omega)
  have b3 := hi (2 * h) (by omega)
  have e1 := P (J + 1 + (h - 1)) (J - 1 + (h + 1)) (by omega)
  have e2 := P (J - 1 + 1) J (by omega)
  have e3 := P (J + 1 + 2 * h) (J - 1 + 2 * (h + 1)) (by omega)
  have e4 := P (J + (2 * h + 1) + 1) (J - 1 + 2 * (h + 1) + 1) (by omega)
  have e5 := P (J + (2 * h + 1)) (J + 1 + 2 * h) (by omega)
  have f0 := pos_lt_succ hp ht (J - 1)
  apply col_of_pos hp ht (j := J - 1) (k := h + 1) (by omega) hk <;> omega

/-- The square around a run of length `2h+1` with left half `(!ℓ)^g ℓ^(h+1)`. -/
lemma run_sq_right {J h : ℕ} (hr : RunAt x ℓ J (2 * h + 1)) (hh : 1 ≤ h)
    (hk : h + 1 < total x n ℓ)
    (hg : pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) ≤ pos x ℓ (J + 1) - pos x ℓ J) :
    pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) + h ∈ col x n ℓ (h + 1) := by
  obtain ⟨-, hg1, hi, he⟩ := hr
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have b2 := hi h (by omega)
  have b3 := hi (2 * h) (by omega)
  have e1 := P (J + 1 + h) (J + (h + 1)) (by omega)
  have e3 := P (J + (2 * h + 1) + 1) (J + 2 * (h + 1)) (by omega)
  have e4 := P (J + (2 * h + 1) + 1 + 1) (J + 2 * (h + 1) + 1) (by omega)
  have e5 := P (J + (2 * h + 1)) (J + 1 + 2 * h) (by omega)
  have f0 := pos_lt_succ hp ht (J + (2 * h + 1) + 1)
  apply col_of_pos hp ht (j := J) (k := h + 1) (by omega) hk <;> omega

/-- All runs of length at least three have the same length. -/
lemma runs_same {J L J' L' : ℕ} (hr : RunAt x ℓ J L) (hr' : RunAt x ℓ J' L') (h3 : 3 ≤ L)
    (hlt : L < L') : False := by
  have hodd := hr.odd hp ht hT
  obtain ⟨h, rfl⟩ : ∃ h, L = 2 * h + 1 := ⟨L / 2, by omega⟩
  have hL' := hr'.le_total hp ht
  have hs := hr.shift hp ht
  set J₀ := J + total x n ℓ with hJ₀
  obtain ⟨-, hg', hi', he'⟩ := hr'
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have A : h + 1 ∈ col x n ℓ (h + 1) := by
    have a1 := hi' h (by omega)
    have a2 := hi' (2 * h + 1) (by omega)
    have e1 := P (J' + 1 + h) (J' + (h + 1)) (by omega)
    have e2 := P (J' + 1 + (2 * h + 1)) (J' + 2 * (h + 1)) (by omega)
    have f := pos_lt_succ hp ht (J' + 2 * (h + 1))
    have f0 := pos_lt_succ hp ht J'
    apply col_of_pos hp ht (j := J') (k := h + 1) (by omega) (by omega) <;> omega
  have g1 := hs.2.1
  have g2 := hs.2.2.2
  rcases le_total (pos x ℓ (J₀ + 1) - pos x ℓ J₀)
      (pos x ℓ (J₀ + (2 * h + 1) + 1) - pos x ℓ (J₀ + (2 * h + 1))) with hg | hg
  · have B := run_sq_left hp ht hT (by omega) hs (by omega) (by omega) hg
    have := hT _ _ _ A B
    omega
  · have B := run_sq_right hp ht hT hs (by omega) (by omega) hg
    have := hT _ _ _ A B
    omega

/-- A run of the common length `2h+1` is not followed by a shorter gap. -/
lemma gap_no_shrink {J h : ℕ} (hall : ∀ J' L', RunAt x ℓ J' L' → L' = 1 ∨ L' = 2 * h + 1)
    (hr : RunAt x ℓ J (2 * h + 1)) (hh : 1 ≤ h)
    (hgap : pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) <
      pos x ℓ (J + 1) - pos x ℓ J) : False := by
  have hLt := hr.le_total hp ht
  obtain ⟨-, hg1, hi, he⟩ := hr
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  obtain ⟨L'', hr''⟩ := run_next hp ht he
  have b2 := hi h (by omega)
  have b3 := hi (2 * h) (by omega)
  have e1 := P (J + 1 + h) (J + (h + 1)) (by omega)
  have e5 := P (J + (2 * h + 1)) (J + 1 + 2 * h) (by omega)
  rcases hall _ _ hr'' with h1 | h1
  · subst h1
    obtain ⟨-, -, -, he''⟩ := hr''
    have e3 := P (J + (2 * h + 1) + 1) (J + 2 * (h + 1)) (by omega)
    have e4 := P (J + (2 * h + 1) + 1 + 1) (J + 2 * (h + 1) + 1) (by omega)
    have hm : ∀ m, pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) + h ≤ m →
        m ≤ pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) + h + 1 →
        m ∈ col x n ℓ (h + 1) := by
      intro m hm1 hm2
      apply col_of_pos hp ht (j := J) (k := h + 1) (by omega) (by omega) <;> omega
    have := hT _ _ _ (hm _ le_rfl (by omega)) (hm _ (by omega) le_rfl)
    omega
  · subst h1
    obtain ⟨-, -, hi'', he''⟩ := hr''
    have c1 := hi'' (2 * h) (by omega)
    have e3 := P (J + (2 * h + 1) + 1 + 2 * h) (J + 2 * (2 * h + 1)) (by omega)
    have e4 := P (J + (2 * h + 1) + (2 * h + 1)) (J + 2 * (2 * h + 1)) (by omega)
    have e6 := P (J + (2 * h + 1) + (2 * h + 1) + 1) (J + 2 * (2 * h + 1) + 1) (by omega)
    have hne : total x n ℓ ≠ 2 * h + 1 := by
      intro hα
      have q1 := pos_add_total hp ht J
      have q2 := pos_add_total hp ht (J + 1)
      rw [hα] at q1 q2
      have := P (J + 1 + (2 * h + 1)) (J + (2 * h + 1) + 1) (by omega)
      omega
    have hm : ∀ m, pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) + 2 * h ≤ m →
        m ≤ pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) + 2 * h + 1 →
        m ∈ col x n ℓ (2 * h + 1) := by
      intro m hm1 hm2
      apply col_of_pos hp ht (j := J) (k := 2 * h + 1) (by omega) (by omega) <;> omega
    have := hT _ _ _ (hm _ le_rfl (by omega)) (hm _ (by omega) le_rfl)
    omega

/-- A run of length `2h+1` preceded by an isolated occurrence has its left gap at least its
right gap. -/
lemma gap_isolated_prev {J h : ℕ} (hJ : 1 ≤ J) (hr : RunAt x ℓ J (2 * h + 1)) (hh : 1 ≤ h)
    (hiso : pos x ℓ (J - 1) + 2 ≤ pos x ℓ J)
    (hgap : pos x ℓ (J + 1) - pos x ℓ J <
      pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1))) : False := by
  have hLt := hr.le_total hp ht
  obtain ⟨-, hg1, hi, he⟩ := hr
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have b1 := hi (h - 1) (by omega)
  have b3 := hi (2 * h) (by omega)
  have e1 := P (J + 1 + (h - 1)) (J - 1 + (h + 1)) (by omega)
  have e2 := P (J - 1 + 1) J (by omega)
  have e3 := P (J + 1 + 2 * h) (J - 1 + 2 * (h + 1)) (by omega)
  have e4 := P (J + (2 * h + 1) + 1) (J - 1 + 2 * (h + 1) + 1) (by omega)
  have e5 := P (J + (2 * h + 1)) (J + 1 + 2 * h) (by omega)
  have hm : ∀ m, pos x ℓ (J + 1) - pos x ℓ J + h ≤ m →
      m ≤ pos x ℓ (J + 1) - pos x ℓ J + h + 1 → m ∈ col x n ℓ (h + 1) := by
    intro m hm1 hm2
    apply col_of_pos hp ht (j := J - 1) (k := h + 1) (by omega) (by omega) <;> omega
  have := hT _ _ _ (hm _ le_rfl (by omega)) (hm _ (by omega) le_rfl)
  omega

end tight

/-- With equal gaps around a run, rigidity forces the word to be a single block. -/
lemma gap_equal (hT : Tight x n ℓ) (hR : Rigid x n) {J h : ℕ} (hJ : 1 ≤ J)
    (hr : RunAt x ℓ J (2 * h + 1)) (hh : 1 ≤ h)
    (heq : pos x ℓ (J + (2 * h + 1) + 1) - pos x ℓ (J + (2 * h + 1)) =
      pos x ℓ (J + 1) - pos x ℓ J) :
    BlockShape x n ℓ (2 * h + 1) ∧ total x n ℓ = 2 * h + 1 := by
  have hLt := hr.le_total hp ht
  obtain ⟨-, hg1, hi, he⟩ := hr
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have b1 := hi (h - 1) (by omega)
  have b2 := hi h (by omega)
  have b3 := hi (2 * h) (by omega)
  have e5 := P (J + (2 * h + 1)) (J + 1 + 2 * h) (by omega)
  by_cases h2m : 2 * (pos x ℓ (J + 1) - pos x ℓ J + h) ≤ n
  · exfalso
    have e1 := P (J + 1 + (h - 1)) (J - 1 + (h + 1)) (by omega)
    have e2 := P (J - 1 + 1) J (by omega)
    have e3 := P (J + 1 + 2 * h) (J - 1 + 2 * (h + 1)) (by omega)
    have e4 := P (J + (2 * h + 1) + 1) (J - 1 + 2 * (h + 1) + 1) (by omega)
    have f0 := pos_lt_succ hp ht (J - 1)
    obtain ⟨hm1, hx1, hsq1, hc1⟩ := sq_of_pos hp ht (j := J - 1) (k := h + 1)
      (m := pos x ℓ (J + 1) - pos x ℓ J + h) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have e1' := P (J + 1 + h) (J + (h + 1)) (by omega)
    have e3' := P (J + (2 * h + 1) + 1) (J + 2 * (h + 1)) (by omega)
    have e4' := P (J + (2 * h + 1) + 1 + 1) (J + 2 * (h + 1) + 1) (by omega)
    have f1 := pos_lt_succ hp ht (J + (2 * h + 1) + 1)
    obtain ⟨-, hx2, hsq2, hc2⟩ := sq_of_pos hp ht (j := J) (k := h + 1)
      (m := pos x ℓ (J + 1) - pos x ℓ J + h) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have := hR _ _ _ hm1 h2m hsq1 hsq2 (by rw [hx1, hx2]) (by rw [hx1, hc1, hc2]) 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero, show pos x ℓ (J - 1 + (h + 1)) + 1 -
      (pos x ℓ (J + 1) - pos x ℓ J + h) = pos x ℓ J by omega, pos_spec hp ht] at this
    exact not_of_between hp ht (j := J) (by omega) (by omega) this.symm
  · push Not at h2m
    have hα : total x n ℓ = 2 * h + 1 := by
      by_contra hne
      have q1 := pos_add_total hp ht J
      have q2 := pos_add_le hp ht (J + (2 * h + 1) + 1) (total x n ℓ - (2 * h + 2))
      have := P (J + (2 * h + 1) + 1 + (total x n ℓ - (2 * h + 2))) (J + total x n ℓ)
        (by omega)
      omega
    refine ⟨⟨pos x ℓ (J + 1), fun i => ?_⟩, hα⟩
    have q2 := pos_add_total hp ht (J + 1)
    rw [hα] at q2
    have e6 := P (J + 1 + (2 * h + 1)) (J + (2 * h + 1) + 1) (by omega)
    have hn : n = 2 * h + (pos x ℓ (J + 1) - pos x ℓ J) := by omega
    have hmod : x (pos x ℓ (J + 1) + i) = x (pos x ℓ (J + 1) + i % n) := by
      conv_lhs => rw [← Nat.mod_add_div i n]
      rw [← Nat.add_assoc, Nat.mul_comm, hp.add_mul]
    rw [hmod]
    have hr : i % n < n := Nat.mod_lt _ (by omega)
    split_ifs with hlt
    · rw [← hi (i % n) hlt]; exact pos_spec hp ht _
    · exact bool_eq_not (not_of_between hp ht (j := J + (2 * h + 1)) (by omega) (by omega))

end

end Circ
