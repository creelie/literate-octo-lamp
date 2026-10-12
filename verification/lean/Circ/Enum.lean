import Circ.Basic

/-!
# Enumerating the occurrences of a letter

For a periodic word containing the letter `ℓ`, `pos x ℓ j` is the position of the
`j`-th occurrence of `ℓ` (counting from `0`).
-/

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

lemma count_eq_cnt (x : ℕ → Bool) (ℓ : Bool) (k : ℕ) :
    Nat.count (fun i => x i = ℓ) k = cnt x ℓ 0 k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.count_succ, ih, cnt_succ, Nat.zero_add]

lemma cnt_eq_count (x : ℕ → Bool) (ℓ : Bool) (u k : ℕ) :
    cnt x ℓ u k = Nat.count (fun i => x i = ℓ) (u + k) - Nat.count (fun i => x i = ℓ) u := by
  rw [count_eq_cnt, count_eq_cnt, cnt_add 0 u k, Nat.zero_add]; omega

lemma infinite_of_total_pos (hp : Periodic x n) (ht : 0 < total x n ℓ) :
    (Set.ofPred (fun i => x i = ℓ)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  have h : 0 < cnt x ℓ (a + 1) n := by rw [cnt_period hp]; exact ht
  by_contra hne
  push Not at hne
  have : cnt x ℓ (a + 1) n = 0 := by
    rw [cnt_eq_zero_iff]
    intro t _ hxt
    exact absurd (hne (a + 1 + t) hxt) (by omega)
  omega

/-- Position of the `j`-th occurrence of `ℓ`. -/
noncomputable def pos (x : ℕ → Bool) (ℓ : Bool) (j : ℕ) : ℕ := Nat.nth (fun i => x i = ℓ) j

section
variable (hp : Periodic x n) (ht : 0 < total x n ℓ)
include hp ht

lemma pos_spec (j : ℕ) : x (pos x ℓ j) = ℓ :=
  Nat.nth_mem_of_infinite (infinite_of_total_pos hp ht) j

lemma pos_strictMono : StrictMono (pos x ℓ) :=
  Nat.nth_strictMono (infinite_of_total_pos hp ht)

lemma pos_lt_succ (j : ℕ) : pos x ℓ j < pos x ℓ (j + 1) :=
  pos_strictMono hp ht (Nat.lt_succ_self j)

lemma pos_add_le (j t : ℕ) : pos x ℓ j + t ≤ pos x ℓ (j + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have := pos_lt_succ hp ht (j + t)
    show _ ≤ pos x ℓ (j + t + 1)
    omega

lemma count_pos (j : ℕ) : Nat.count (fun i => x i = ℓ) (pos x ℓ j) = j :=
  Nat.count_nth_of_infinite (infinite_of_total_pos hp ht) j

lemma count_pos_succ (j : ℕ) : Nat.count (fun i => x i = ℓ) (pos x ℓ j + 1) = j + 1 := by
  rw [Nat.count_succ, count_pos hp ht, ite_eq_left (pos_spec hp ht j)]

/-- Between two consecutive occurrences the count is constant. -/
lemma count_eq_of_between {j u : ℕ} (h1 : pos x ℓ j < u) (h2 : u ≤ pos x ℓ (j + 1)) :
    Nat.count (fun i => x i = ℓ) u = j + 1 := by
  have m := Nat.count_monotone (fun i => x i = ℓ)
  have a := m (show pos x ℓ j + 1 ≤ u by omega)
  have b := m h2
  rw [count_pos_succ hp ht] at a
  rw [count_pos hp ht] at b
  omega

lemma count_eq_zero_of_le {u : ℕ} (h : u ≤ pos x ℓ 0) :
    Nat.count (fun i => x i = ℓ) u = 0 := by
  have := Nat.count_monotone (fun i => x i = ℓ) h
  rw [count_pos hp ht] at this
  omega

lemma not_of_between {j u : ℕ} (h1 : pos x ℓ j < u) (h2 : u < pos x ℓ (j + 1)) : x u ≠ ℓ := by
  intro hu
  have a := count_eq_of_between hp ht h1 h2.le
  have b := count_eq_of_between hp ht (show pos x ℓ j < u + 1 by omega) h2
  rw [Nat.count_succ, ite_eq_left hu] at b
  omega

/-- Every occurrence of `ℓ` is enumerated. -/
lemma eq_pos_of {u : ℕ} (hu : x u = ℓ) : pos x ℓ (Nat.count (fun i => x i = ℓ) u) = u :=
  Nat.nth_count hu

lemma pos_add_total (j : ℕ) : pos x ℓ (j + total x n ℓ) = pos x ℓ j + n := by
  have hc : Nat.count (fun i => x i = ℓ) (pos x ℓ j + n) = j + total x n ℓ := by
    have := cnt_eq_count x ℓ (pos x ℓ j) n
    rw [cnt_period hp, count_pos hp ht] at this
    have hle : j ≤ Nat.count (fun i => x i = ℓ) (pos x ℓ j + n) := by
      have h := Nat.count_monotone (fun i => x i = ℓ) (show pos x ℓ j ≤ pos x ℓ j + n by omega)
      rwa [count_pos hp ht] at h
    unfold total; omega
  have hx : x (pos x ℓ j + n) = ℓ := by rw [hp]; exact pos_spec hp ht j
  rw [← hc]; exact eq_pos_of hp ht hx

lemma pos_add_mul_total (j q : ℕ) : pos x ℓ (j + q * total x n ℓ) = pos x ℓ j + q * n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul, ← Nat.add_assoc, pos_add_total hp ht, ih, Nat.add_assoc]

/-- The window `[u, v)` with `pos j < u ≤ pos (j+1)` and `pos (j+t) < v ≤ pos (j+t+1)`
contains exactly `t` occurrences. -/
lemma cnt_between {j t u k : ℕ} (h1 : pos x ℓ j < u) (h2 : u ≤ pos x ℓ (j + 1))
    (h3 : pos x ℓ (j + t) < u + k) (h4 : u + k ≤ pos x ℓ (j + t + 1)) : cnt x ℓ u k = t := by
  rw [cnt_eq_count, count_eq_of_between hp ht h1 h2, count_eq_of_between hp ht h3 h4]
  omega

end

end Circ
