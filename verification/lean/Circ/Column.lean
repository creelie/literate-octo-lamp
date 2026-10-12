import Circ.Enum

/-!
# The column lemma

For `1 ≤ k < total x n ℓ` there is an abelian square whose left half ends with `ℓ`
and contains exactly `k` occurrences of `ℓ`.
-/

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

/-- `d j` is the distance from the `j`-th to the `(j+k)`-th occurrence. -/
private lemma exists_turn (d : ℕ → ℕ) (k α : ℕ) (hα : 0 < α)
    (hper : ∀ j, d (j + α) = d j) :
    ∃ j, d (j + k) ≤ d j ∧ d (j + 1) ≤ d (j + 1 + k) := by
  have hperm : ∀ j q, d (j + q * α) = d j := by
    intro j q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]
  by_contra H
  push Not at H
  by_cases h0 : ∃ j0, d (j0 + k) ≤ d j0
  · obtain ⟨j0, hj0⟩ := h0
    have step : ∀ t, d (j0 + 1 + t + k) < d (j0 + 1 + t) := by
      intro t
      induction t with
      | zero => simpa using H j0 hj0
      | succ t ih =>
        have := H (j0 + 1 + t) ih.le
        simpa [Nat.add_assoc] using this
    have chain : ∀ s, d (j0 + 1 + s * k) + s ≤ d (j0 + 1) := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        have := step (s * k)
        have e : j0 + 1 + (s + 1) * k = j0 + 1 + s * k + k := by ring
        rw [e]
        omega
    have := chain α
    rw [Nat.mul_comm, hperm] at this
    omega
  · push Not at h0
    have chain : ∀ s, d 0 + s ≤ d (s * k) := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        have := h0 (s * k)
        have e : (s + 1) * k = s * k + k := by ring
        rw [e]
        omega
    have := chain α
    rw [Nat.mul_comm, ← Nat.zero_add (k * α), hperm] at this
    omega

theorem column (hp : Periodic x n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < total x n ℓ) :
    ∃ i m, 1 ≤ m ∧ m < n ∧ x (i + (m - 1)) = ℓ ∧ IsSq x i m ∧ cnt x ℓ i m = k := by
  have ht : 0 < total x n ℓ := by omega
  have hlt : ∀ j, pos x ℓ j < pos x ℓ (j + 1) := pos_lt_succ hp ht
  have hle : ∀ j t, pos x ℓ j + t ≤ pos x ℓ (j + t) := pos_add_le hp ht
  have P : ∀ a b, a = b → pos x ℓ a = pos x ℓ b := fun a b h => by rw [h]
  obtain ⟨j, he, hf⟩ := exists_turn (fun j => pos x ℓ (j + k) - pos x ℓ j) k (total x n ℓ) ht (by
    intro j
    have := pos_add_total hp ht (j + k)
    have := pos_add_total hp ht j
    have := P (j + total x n ℓ + k) (j + k + total x n ℓ) (by omega)

    omega)

  have i1 := P (j + 1 + (k - 1)) (j + k) (by omega)
  have i2 := P (j + k + k) (j + 2 * k) (by omega)
  have i3 := P (j + 1 + k) (j + k + 1) (by omega)
  have i4 := P (j + 1 + k + k) (j + 2 * k + 1) (by omega)
  have i5 := P (j + k + 1 + k) (j + 2 * k + 1) (by omega)
  have i6 := P (j + k + k + 1) (j + 2 * k + 1) (by omega)
  have f1 := hlt j
  have f2 := hle (j + 1) (k - 1)
  have f3 := hlt (j + k)
  have f4 := hle (j + k) k
  have f5 := hlt (j + 2 * k)
  have f6 := hle (j + k + 1) k
  set q := pos x ℓ (j + k)
  set m := max (q - pos x ℓ (j + 1) + 1) (pos x ℓ (j + 2 * k) - q) with hm
  have hm1 : q - pos x ℓ (j + 1) + 1 ≤ m := le_max_left _ _
  have hm2 : pos x ℓ (j + 2 * k) - q ≤ m := le_max_right _ _
  have hmL : m ≤ q - pos x ℓ j := by
    rw [hm]; apply max_le <;> omega
  have hmR : m ≤ pos x ℓ (j + 2 * k + 1) - q - 1 := by
    rw [hm]; apply max_le <;> omega
  have hcL : cnt x ℓ (q + 1 - m) m = k := by
    apply cnt_between hp ht (j := j) (t := k) <;> omega
  have hcR : cnt x ℓ (q + 1 - m + m) m = k := by
    apply cnt_between hp ht (j := j + k) (t := k) <;> omega
  refine ⟨q + 1 - m, m, by omega, ?_, ?_, ?_, hcL⟩
  · exact lt_of_cnt_lt_total hp (by rw [hcL]; exact hk2)
  · rw [show q + 1 - m + (m - 1) = q by omega]; exact pos_spec hp ht (j + k)
  · rw [isSq_iff ℓ, hcL, hcR]

end Circ
