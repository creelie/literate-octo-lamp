import Mathlib

/-!
# Window counts on periodic binary words

A circular binary word of length `n` is encoded as a periodic map `x : ℕ → Bool`.
`cnt x ℓ u k` is the number of occurrences of the letter `ℓ` in the window
`x u, x (u+1), …, x (u+k-1)`.
-/

namespace Circ

/-- Number of occurrences of `ℓ` among `x u, …, x (u + k - 1)`. -/
def cnt (x : ℕ → Bool) (ℓ : Bool) (u : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cnt x ℓ u k + if x (u + k) = ℓ then 1 else 0

variable {x : ℕ → Bool} {ℓ : Bool}

@[simp] lemma cnt_zero (u : ℕ) : cnt x ℓ u 0 = 0 := rfl

lemma cnt_succ (u k : ℕ) :
    cnt x ℓ u (k + 1) = cnt x ℓ u k + if x (u + k) = ℓ then 1 else 0 := rfl

lemma cnt_add (u k₁ k₂ : ℕ) : cnt x ℓ u (k₁ + k₂) = cnt x ℓ u k₁ + cnt x ℓ (u + k₁) k₂ := by
  induction k₂ with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, cnt_succ, ih, cnt_succ, Nat.add_assoc u k₁ k]
    omega

lemma cnt_one (u : ℕ) : cnt x ℓ u 1 = if x u = ℓ then 1 else 0 := by
  simp [cnt_succ]

lemma cnt_le (u k : ℕ) : cnt x ℓ u k ≤ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [cnt_succ]; split <;> omega

lemma cnt_mono (u k₁ k₂ : ℕ) (h : k₁ ≤ k₂) : cnt x ℓ u k₁ ≤ cnt x ℓ u k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cnt_add]; omega

lemma cnt_add_cnt_not (u k : ℕ) : cnt x ℓ u k + cnt x (!ℓ) u k = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cnt_succ, cnt_succ]
    cases h : x (u + k) <;> cases ℓ <;> simp_all <;> omega

lemma cnt_const (u k : ℕ) (h : ∀ t < k, x (u + t) = ℓ) : cnt x ℓ u k = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cnt_succ, ih (fun t ht => h t (by omega)), ite_eq_left (h k (by omega))]

lemma cnt_const_not (u k : ℕ) (h : ∀ t < k, x (u + t) ≠ ℓ) : cnt x ℓ u k = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [cnt_succ, ih (fun t ht => h t (by omega)), ite_eq_right (h k (by omega))]

lemma cnt_eq_len_iff (u k : ℕ) : cnt x ℓ u k = k ↔ ∀ t < k, x (u + t) = ℓ := by
  refine ⟨fun h => ?_, cnt_const u k⟩
  induction k with
  | zero => intro t ht; omega
  | succ k ih =>
    rw [cnt_succ] at h
    have hle := cnt_le (x := x) (ℓ := ℓ) u k
    split at h
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
      · exact ih (by omega) t ht
      · subst ht; assumption
    · omega

lemma cnt_eq_zero_iff (u k : ℕ) : cnt x ℓ u k = 0 ↔ ∀ t < k, x (u + t) ≠ ℓ := by
  refine ⟨fun h => ?_, cnt_const_not u k⟩
  induction k with
  | zero => intro t ht; omega
  | succ k ih =>
    rw [cnt_succ] at h
    split at h
    · omega
    · intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
      · exact ih (by omega) t ht
      · subst ht; assumption

/-- Periodicity of the word. -/
def Periodic (x : ℕ → Bool) (n : ℕ) : Prop := ∀ i, x (i + n) = x i

lemma Periodic.add_mul {n : ℕ} (hp : Periodic x n) (i q : ℕ) : x (i + q * n) = x i := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, hp, ih]

lemma Periodic.mod {n : ℕ} (hp : Periodic x n) (i : ℕ) : x (i % n) = x i := by
  conv_rhs => rw [← Nat.mod_add_div i n, Nat.mul_comm, hp.add_mul]

lemma cnt_shift {n : ℕ} (hp : Periodic x n) (u k : ℕ) : cnt x ℓ (u + n) k = cnt x ℓ u k := by
  induction k with
  | zero => simp
  | succ k ih => rw [cnt_succ, cnt_succ, ih, Nat.add_right_comm, hp]

lemma cnt_shift_mul {n : ℕ} (hp : Periodic x n) (u q k : ℕ) :
    cnt x ℓ (u + q * n) k = cnt x ℓ u k := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, cnt_shift hp, ih]

/-- Every window of length `n` contains the same number of `ℓ`. -/
lemma cnt_period {n : ℕ} (hp : Periodic x n) (u : ℕ) : cnt x ℓ u n = cnt x ℓ 0 n := by
  induction u with
  | zero => rfl
  | succ u ih =>
    have h1 := cnt_add (x := x) (ℓ := ℓ) u 1 n
    have h2 := cnt_add (x := x) (ℓ := ℓ) u n 1
    rw [Nat.add_comm 1 n] at h1
    rw [h1, cnt_one, cnt_one, hp] at h2
    omega

/-- The number of `ℓ` in one period. -/
def total (x : ℕ → Bool) (n : ℕ) (ℓ : Bool) : ℕ := cnt x ℓ 0 n

lemma total_add_total_not (x : ℕ → Bool) (n : ℕ) (ℓ : Bool) :
    total x n ℓ + total x n (!ℓ) = n := cnt_add_cnt_not 0 n

/-- A window of length at least `n` contains every letter of a period. -/
lemma total_le_cnt {n : ℕ} (hp : Periodic x n) (u k : ℕ) (hk : n ≤ k) :
    total x n ℓ ≤ cnt x ℓ u k := by
  rw [total, ← cnt_period hp u]; exact cnt_mono u n k hk

/-- A window of length at most `n` contains at most `total` occurrences. -/
lemma cnt_le_total {n : ℕ} (hp : Periodic x n) (u k : ℕ) (hk : k ≤ n) :
    cnt x ℓ u k ≤ total x n ℓ := by
  rw [total, ← cnt_period hp u]; exact cnt_mono u k n hk

/-- If a window has fewer `ℓ` than a period, it is shorter than a period. -/
lemma lt_of_cnt_lt_total {n : ℕ} (hp : Periodic x n) {u k : ℕ}
    (h : cnt x ℓ u k < total x n ℓ) : k < n := by
  by_contra hk
  have := total_le_cnt (ℓ := ℓ) hp u k (by omega)
  omega

/-- The abelian-square predicate: the windows `[i, i+m)` and `[i+m, i+2m)` contain
the same number of `true`. -/
def IsSq (x : ℕ → Bool) (i m : ℕ) : Prop := cnt x true i m = cnt x true (i + m) m

lemma isSq_iff (ℓ : Bool) (i m : ℕ) : IsSq x i m ↔ cnt x ℓ i m = cnt x ℓ (i + m) m := by
  have h1 := cnt_add_cnt_not (x := x) (ℓ := true) i m
  have h2 := cnt_add_cnt_not (x := x) (ℓ := true) (i + m) m
  cases ℓ <;> simp [IsSq] at * <;> omega

lemma IsSq.shift {n : ℕ} (hp : Periodic x n) {i m : ℕ} :
    IsSq x (i + n) m ↔ IsSq x i m := by
  simp only [IsSq, Nat.add_right_comm i n m, cnt_shift hp]

lemma IsSq.mod {n : ℕ} (hp : Periodic x n) {i m : ℕ} :
    IsSq x (i % n) m ↔ IsSq x i m := by
  have : IsSq x (i % n + (i / n) * n) m ↔ IsSq x (i % n) m := by
    simp only [IsSq, Nat.add_right_comm (i % n) ((i / n) * n) m, cnt_shift_mul hp]
  rw [← this, Nat.mod_add_div' i n]

end Circ
