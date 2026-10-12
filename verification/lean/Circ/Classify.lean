import Circ.Runs

/-!
# Classification of words with a tight letter and rigid squares
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

lemma x_add_mod (hp : Periodic x n) (s i : ℕ) : x (s + i) = x (s + i % n) := by
  conv_lhs => rw [← Nat.mod_add_div i n]
  rw [← Nat.add_assoc, Nat.mul_comm, hp.add_mul]

section
variable (hp : Periodic x n) (ht : 0 < total x n ℓ)
include hp ht

/-- No two occurrences of `ℓ` are adjacent. -/
lemma caseA (hT : Tight x n ℓ) (hR : Rigid x n)
    (hA : ∀ j, pos x ℓ j + 2 ≤ pos x ℓ (j + 1)) :
    (total x n ℓ = 1 ∧ BlockShape x n ℓ 1) ∨ (n = 2 * total x n ℓ ∧ AltShape x ℓ) := by
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have z1 := P (0 + 1) 1 rfl
  have z2 := P (1 + 1) 2 rfl
  have z3 := P (2 + 1) 3 rfl
  have z4 := P (1 + 1 + 1) 3 rfl
  have z5 := P (2 + 1 + 1) 4 rfl
  have z6 := P (0 + 1 + 1) 2 rfl
  have hn : 0 < n := by have := total_le hp ht; omega
  by_cases hα1 : total x n ℓ = 1
  · left
    refine ⟨hα1, pos x ℓ 0, fun i => ?_⟩
    have q := pos_add_total hp ht 0
    rw [hα1, Nat.zero_add] at q
    rw [x_add_mod hp]
    have := Nat.mod_lt i hn
    split_ifs with h0
    · rw [show i % n = 0 by omega, Nat.add_zero]; exact pos_spec hp ht 0
    · exact bool_eq_not (not_of_between hp ht (j := 0) (by omega) (by omega))
  have hα2 : 2 ≤ total x n ℓ := by omega
  have mono : ∀ j, pos x ℓ (j + 1) - pos x ℓ j ≤ pos x ℓ (j + 2) - pos x ℓ (j + 1) := by
    intro j
    by_contra hc
    push Not at hc
    have a1 := hA j
    have a2 := hA (j + 1)
    have a3 := hA (j + 2)
    have e0 := P (j + 1 + 1) (j + 2) (by omega)
    have e1 := P (j + 2 * 1) (j + 2) (by omega)
    have e2 := P (j + 2 * 1 + 1) (j + 2 + 1) (by omega)
    have hm : ∀ m, pos x ℓ (j + 2) - pos x ℓ (j + 1) ≤ m →
        m ≤ pos x ℓ (j + 2) - pos x ℓ (j + 1) + 1 → m ∈ col x n ℓ 1 := by
      intro m h1 h2
      apply col_of_pos hp ht (j := j) (k := 1) le_rfl (by omega) <;> omega
    have := hT _ _ _ (hm _ le_rfl (by omega)) (hm _ (by omega) le_rfl)
    omega
  have up : ∀ t j, pos x ℓ (j + 1) - pos x ℓ j ≤ pos x ℓ (j + t + 1) - pos x ℓ (j + t) := by
    intro t
    induction t with
    | zero => intro j; simp
    | succ t ih =>
      intro j
      have := ih j
      have := mono (j + t)
      have := P (j + (t + 1) + 1) (j + t + 2) (by omega)
      have := P (j + (t + 1)) (j + t + 1) (by omega)
      omega
  have step : ∀ j, pos x ℓ (j + 2) - pos x ℓ (j + 1) = pos x ℓ (j + 1) - pos x ℓ j := by
    intro j
    have h1 := up (total x n ℓ - 1) (j + 1)
    have h2 := mono j
    have q1 := pos_add_total hp ht j
    have q2 := pos_add_total hp ht (j + 1)
    have := P (j + 1 + 1) (j + 2) (by omega)
    have := P (j + 1 + (total x n ℓ - 1) + 1) (j + 1 + total x n ℓ) (by omega)
    have := P (j + 1 + (total x n ℓ - 1)) (j + total x n ℓ) (by omega)
    omega
  have dconst : ∀ j, pos x ℓ (j + 1) - pos x ℓ j = pos x ℓ 1 - pos x ℓ 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← ih, ← step j]
  have hpj : ∀ j, pos x ℓ j = pos x ℓ 0 + j * (pos x ℓ 1 - pos x ℓ 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := dconst j
      have := hA j
      rw [Nat.succ_mul]
      omega
  have hD2 : 2 ≤ pos x ℓ 1 - pos x ℓ 0 := by have := hA 0; omega
  have hnD : n = total x n ℓ * (pos x ℓ 1 - pos x ℓ 0) := by
    have q := pos_add_total hp ht 0
    rw [Nat.zero_add, hpj (total x n ℓ)] at q
    omega
  by_cases hD : pos x ℓ 1 - pos x ℓ 0 = 2
  · right
    refine ⟨by rw [hD] at hnD; omega, pos x ℓ 0, fun i => ?_⟩
    have a1 := hpj (i / 2)
    have a2 := hpj (i / 2 + 1)
    rw [hD] at a1 a2
    split_ifs with h0
    · rw [show pos x ℓ 0 + i = pos x ℓ (i / 2) by omega]; exact pos_spec hp ht _
    · exact bool_eq_not (not_of_between hp ht (j := i / 2) (by omega) (by omega))
  · exfalso
    set D := pos x ℓ 1 - pos x ℓ 0 with hDdef
    have p1 := hpj 1
    have p2 := hpj 2
    have p3 := hpj 3
    have p4 := hpj 4
    have c1 : cnt x ℓ (pos x ℓ 1) D = 1 := by
      apply cnt_between hp ht (j := 0) (t := 1) <;> omega
    have c2 : cnt x ℓ (pos x ℓ 1 + D) D = 1 := by
      apply cnt_between hp ht (j := 1) (t := 1) <;> omega
    have c3 : cnt x ℓ (pos x ℓ 1 + 2) D = 1 := by
      apply cnt_between hp ht (j := 1) (t := 1) <;> omega
    have c4 : cnt x ℓ (pos x ℓ 1 + 2 + D) D = 1 := by
      apply cnt_between hp ht (j := 2) (t := 1) <;> omega
    have x1 : x (pos x ℓ 1 + (D - 1)) = !ℓ :=
      bool_eq_not (not_of_between hp ht (j := 1) (by omega) (by omega))
    have x2 : x (pos x ℓ 1 + 2 + (D - 1)) = !ℓ :=
      bool_eq_not (not_of_between hp ht (j := 2) (by omega) (by omega))
    have n1 := cnt_add_cnt_not (x := x) (ℓ := ℓ) (pos x ℓ 1) D
    have n2 := cnt_add_cnt_not (x := x) (ℓ := ℓ) (pos x ℓ 1 + 2) D
    have h2D : 2 * D ≤ n := by rw [hnD]; exact Nat.mul_le_mul_right D hα2
    have := hR D (pos x ℓ 1) (pos x ℓ 1 + 2) (by omega) h2D
      (by rw [isSq_iff ℓ, c1, c2]) (by rw [isSq_iff ℓ, c3, c4]) (by rw [x1, x2])
      (by rw [x1]; omega) 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero, pos_spec hp ht] at this
    exact not_of_between hp ht (j := 1) (by omega) (by omega) this.symm

/-- The classification of a word with a tight letter and rigid squares. -/
theorem classify (hT : Tight x n ℓ) (hR : Rigid x n) :
    (BlockShape x n ℓ (total x n ℓ) ∧ (total x n ℓ % 2 = 1 ∨ total x n ℓ = n)) ∨
      (n = 2 * total x n ℓ ∧ AltShape x ℓ) := by
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  have hn : 0 < n := by have := total_le hp ht; omega
  have hlt := pos_lt_succ hp ht
  by_cases hfull : total x n ℓ = n
  · left
    refine ⟨⟨0, fun i => ?_⟩, Or.inr hfull⟩
    have hall := (cnt_eq_len_iff (x := x) (ℓ := ℓ) 0 n).mp hfull
    have := Nat.mod_lt i hn
    rw [x_add_mod hp, ite_eq_left (by omega)]
    exact hall _ this
  by_cases hA : ∀ j, pos x ℓ j + 2 ≤ pos x ℓ (j + 1)
  · rcases caseA hp ht hT hR hA with ⟨h1, h2⟩ | h
    · left; rw [h1]; exact ⟨h2, Or.inl rfl⟩
    · right; exact h
  left
  push Not at hA
  obtain ⟨j, hj⟩ := hA
  have hgap : ∃ J, pos x ℓ J + 2 ≤ pos x ℓ (J + 1) := by
    by_contra hc
    push Not at hc
    have all : ∀ i, pos x ℓ i = pos x ℓ 0 + i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => have := hc i; have := hlt i; omega
    have q := pos_add_total hp ht 0
    rw [Nat.zero_add, all] at q
    omega
  obtain ⟨J, hJ⟩ := hgap
  -- the first gap after `j`
  have hex : ∃ t, pos x ℓ (j + 1 + t) + 2 ≤ pos x ℓ (j + 1 + t + 1) := by
    refine ⟨J + (j + 1) * total x n ℓ - (j + 1), ?_⟩
    have hge : j + 1 ≤ (j + 1) * total x n ℓ := Nat.le_mul_of_pos_right _ ht
    have q1 := pos_add_mul_total hp ht J (j + 1)
    have q2 := pos_add_mul_total hp ht (J + 1) (j + 1)
    have := P (j + 1 + (J + (j + 1) * total x n ℓ - (j + 1))) (J + (j + 1) * total x n ℓ)
      (by omega)
    have := P (j + 1 + (J + (j + 1) * total x n ℓ - (j + 1)) + 1)
      (J + 1 + (j + 1) * total x n ℓ) (by omega)
    omega
  set J₁ := j + 1 + Nat.find hex with hJ₁
  have hg₁ : pos x ℓ J₁ + 2 ≤ pos x ℓ (J₁ + 1) := Nat.find_spec hex
  have hd₁ : pos x ℓ (J₁ - 1 + 1) = pos x ℓ (J₁ - 1) + 1 := by
    have := hlt (J₁ - 1)
    by_cases h0 : Nat.find hex = 0
    · have := P (J₁ - 1) j (by omega)
      have := P (J₁ - 1 + 1) (j + 1) (by omega)
      omega
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      have := P (j + 1 + (Nat.find hex - 1)) (J₁ - 1) (by omega)
      have := P (j + 1 + (Nat.find hex - 1) + 1) (J₁ - 1 + 1) (by omega)
      omega
  obtain ⟨J', L', hr', hJL'⟩ := run_prev hp ht hg₁
  have hL'2 : 2 ≤ L' := by
    by_contra hc
    have hL1 : L' = 1 := by have := hr'.1; omega
    subst hL1
    have g := hr'.2.1
    have q1 := pos_add_total hp ht (J₁ - 1)
    have q2 := pos_add_total hp ht (J₁ - 1 + 1)
    have := P (J₁ - 1 + total x n ℓ) J' (by omega)
    have := P (J₁ - 1 + 1 + total x n ℓ) (J' + 1) (by omega)
    omega
  have hodd := hr'.odd hp ht hT
  obtain ⟨h, rfl⟩ : ∃ h, L' = 2 * h + 1 := ⟨L' / 2, by omega⟩
  have hh : 1 ≤ h := by omega
  have hall : ∀ J₂ L₂, RunAt x ℓ J₂ L₂ → L₂ = 1 ∨ L₂ = 2 * h + 1 := by
    intro J₂ L₂ hr₂
    have := hr₂.odd hp ht hT
    have := hr₂.1
    rcases lt_trichotomy L₂ (2 * h + 1) with hc | hc | hc
    · by_cases h1 : L₂ = 1
      · exact Or.inl h1
      · exact (runs_same hp ht hT hr₂ hr' (by omega) hc).elim
    · exact Or.inr hc
    · exact (runs_same hp ht hT hr' hr₂ (by omega) hc).elim
  have claim : ∀ g J₂, 1 ≤ J₂ → RunAt x ℓ J₂ (2 * h + 1) →
      pos x ℓ (J₂ + 1) - pos x ℓ J₂ = g →
      BlockShape x n ℓ (2 * h + 1) ∧ total x n ℓ = 2 * h + 1 := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro J₂ hJ₂ hr hgJ
      rcases lt_trichotomy
          (pos x ℓ (J₂ + (2 * h + 1) + 1) - pos x ℓ (J₂ + (2 * h + 1)))
          (pos x ℓ (J₂ + 1) - pos x ℓ J₂) with hc | hc | hc
      · exact (gap_no_shrink hp ht hT hall hr hh hc).elim
      · exact gap_equal hp ht hT hR hJ₂ hr hh hc
      · obtain ⟨J₃, L₃, hr₃, hJ₃⟩ := run_prev hp ht hr.2.1
        have q1 := pos_add_total hp ht J₂
        have q2 := pos_add_total hp ht (J₂ + 1)
        have q3 := pos_add_total hp ht (J₂ + (2 * h + 1))
        have q4 := pos_add_total hp ht (J₂ + (2 * h + 1) + 1)
        rcases hall _ _ hr₃ with h1 | h1
        · subst h1
          have hs := hr.shift hp ht
          have g3 := hr₃.2.1
          exfalso
          apply gap_isolated_prev hp ht hT (J := J₂ + total x n ℓ) (h := h) (by omega) hs hh
          · have := P (J₂ + total x n ℓ - 1) J₃ (by omega)
            have := P J₃ J₃ rfl
            have := P (J₃ + 1) (J₂ + total x n ℓ) (by omega)
            omega
          · have := P (J₂ + total x n ℓ + 1) (J₂ + 1 + total x n ℓ) (by omega)
            have := P (J₂ + total x n ℓ + (2 * h + 1)) (J₂ + (2 * h + 1) + total x n ℓ)
              (by omega)
            have := P (J₂ + total x n ℓ + (2 * h + 1) + 1)
              (J₂ + (2 * h + 1) + 1 + total x n ℓ) (by omega)
            omega
        · subst h1
          have e1 := P (J₃ + (2 * h + 1)) (J₂ + total x n ℓ) (by omega)
          have e2 := P (J₃ + (2 * h + 1) + 1) (J₂ + 1 + total x n ℓ) (by omega)
          have hs₃ := hr₃.shift hp ht
          have r1 := pos_add_total hp ht J₃
          have r2 := pos_add_total hp ht (J₃ + 1)
          have r3 := P (J₃ + total x n ℓ + 1) (J₃ + 1 + total x n ℓ) (by omega)
          rcases lt_trichotomy (pos x ℓ (J₃ + 1) - pos x ℓ J₃) (pos x ℓ (J₂ + 1) - pos x ℓ J₂)
            with hd | hd | hd
          · exact ih (pos x ℓ (J₃ + 1) - pos x ℓ J₃) (by omega) (J₃ + total x n ℓ) (by omega) hs₃
              (by omega)
          · have r4 := pos_add_total hp ht (J₃ + (2 * h + 1))
            have r5 := pos_add_total hp ht (J₃ + (2 * h + 1) + 1)
            have := P (J₃ + total x n ℓ + (2 * h + 1)) (J₃ + (2 * h + 1) + total x n ℓ)
              (by omega)
            have := P (J₃ + total x n ℓ + (2 * h + 1) + 1)
              (J₃ + (2 * h + 1) + 1 + total x n ℓ) (by omega)
            exact gap_equal hp ht hT hR (by omega) hs₃ hh (by omega)
          · exact (gap_no_shrink hp ht hT hall hr₃ hh (by omega)).elim
  have hs := hr'.shift hp ht
  obtain ⟨hB, hα⟩ := claim _ (J' + total x n ℓ) (by omega) hs rfl
  rw [hα]
  exact ⟨hB, Or.inl (by omega)⟩

end

end Circ
