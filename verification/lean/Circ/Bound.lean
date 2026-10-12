import Circ.Column

/-!
# Square sets, the mirror involution and the lower bound
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

/-- `Realized x m ℓ k`: some abelian square of half-length `m` has left half ending
with `ℓ` and containing `k` occurrences of `ℓ`. -/
def Realized (x : ℕ → Bool) (m : ℕ) (ℓ : Bool) (k : ℕ) : Prop :=
  ∃ i, x (i + (m - 1)) = ℓ ∧ IsSq x i m ∧ cnt x ℓ i m = k

/-- The pairs `(ℓ, k)` realized at half-length `m`. -/
noncomputable def Qset (x : ℕ → Bool) (n m : ℕ) : Finset (Bool × ℕ) :=
  (Finset.univ ×ˢ Finset.range (n + 1)).filter (fun p => Realized x m p.1 p.2)

/-- Column `k` of letter `ℓ`: the half-lengths `m ∈ [1, n)` realizing `(ℓ, k)`. -/
noncomputable def col (x : ℕ → Bool) (n : ℕ) (ℓ : Bool) (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun m => Realized x m ℓ k)

lemma mem_col {m k : ℕ} : m ∈ col x n ℓ k ↔ 1 ≤ m ∧ m < n ∧ Realized x m ℓ k := by
  simp [col, and_assoc]

lemma mem_Qset {m k : ℕ} : (ℓ, k) ∈ Qset x n m ↔ k ≤ n ∧ Realized x m ℓ k := by
  simp [Qset, Nat.lt_succ_iff]

lemma Realized.pos {m k : ℕ} (hm : 1 ≤ m) (h : Realized x m ℓ k) : 1 ≤ k := by
  obtain ⟨i, hx, -, hc⟩ := h
  have := cnt_succ (x := x) (ℓ := ℓ) i (m - 1)
  rw [Nat.sub_add_cancel hm, ite_eq_left hx] at this
  omega

lemma Realized.le (hp : Periodic x n) {m k : ℕ} (hm : m ≤ n) (h : Realized x m ℓ k) :
    k ≤ total x n ℓ := by
  obtain ⟨i, -, -, hc⟩ := h
  rw [← hc]; exact cnt_le_total hp i m hm

/-- The mirror involution `(m, k) ↦ (n - m, total - k)`. -/
lemma Realized.mirror (hp : Periodic x n) {m k : ℕ} (hm1 : 1 ≤ m) (hm2 : m < n)
    (h : Realized x m ℓ k) : Realized x (n - m) ℓ (total x n ℓ - k) := by
  obtain ⟨i, hx, hsq, hc⟩ := h
  have hsq' := (isSq_iff ℓ i m).mp hsq
  have a1 := cnt_add (x := x) (ℓ := ℓ) (i + m) m (n - m)
  have a2 := cnt_add (x := x) (ℓ := ℓ) i m (n - m)
  rw [Nat.add_sub_cancel' hm2.le, cnt_period hp] at a1 a2
  have s1 : cnt x ℓ (i + 2 * m + (n - m)) (n - m) = cnt x ℓ (i + m) (n - m) := by
    rw [show i + 2 * m + (n - m) = i + m + n by omega, cnt_shift hp]
  refine ⟨i + 2 * m, ?_, ?_, ?_⟩
  · rw [show i + 2 * m + (n - m - 1) = i + (m - 1) + n by omega, hp, hx]
  · rw [isSq_iff ℓ, s1, show i + 2 * m = i + m + m by omega]
    unfold total at *; omega
  · rw [show i + 2 * m = i + m + m by omega]; unfold total at *; omega

lemma col_bounds (hp : Periodic x n) {m k : ℕ} (h : m ∈ col x n ℓ k) :
    1 ≤ k ∧ k + 1 ≤ total x n ℓ := by
  rw [mem_col] at h
  obtain ⟨h1, h2, h3⟩ := h
  have a := h3.pos h1
  have b := h3.le hp h2.le
  have c := (h3.mirror hp h1 h2).pos (by omega)
  omega

lemma col_nonempty (hp : Periodic x n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < total x n ℓ) :
    (col x n ℓ k).Nonempty := by
  obtain ⟨i, m, h1, h2, h3, h4, h5⟩ := column hp hk1 hk2
  exact ⟨m, mem_col.mpr ⟨h1, h2, i, h3, h4, h5⟩⟩

lemma col_mirror (hp : Periodic x n) {m k : ℕ} (h : m ∈ col x n ℓ k) :
    n - m ∈ col x n ℓ (total x n ℓ - k) := by
  rw [mem_col] at *
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, h3.mirror hp h1 h2⟩

/-- `|Q_m| = |Q_{n-m}|`. -/
lemma card_Qset_mirror (hp : Periodic x n) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m < n) :
    (Qset x n m).card ≤ (Qset x n (n - m)).card := by
  apply Finset.card_le_card_of_injOn (fun p => (p.1, total x n p.1 - p.2))
  · rintro ⟨ℓ', k⟩ hp'
    simp only [Finset.mem_coe, mem_Qset] at hp' ⊢
    have := total_add_total_not x n ℓ'
    exact ⟨by omega, hp'.2.mirror hp hm1 hm2⟩
  · intro p hp' q hq hpq
    simp only [Finset.mem_coe] at *
    obtain ⟨ℓ', k⟩ := p
    obtain ⟨ℓ'', k'⟩ := q
    rw [mem_Qset] at hp' hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, h⟩ := hpq
    have := hp'.2.le hp hm2.le
    have := hq.2.le hp hm2.le
    simp only [Prod.mk.injEq, true_and]
    omega

lemma card_Qset_symm (hp : Periodic x n) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m < n) :
    (Qset x n m).card = (Qset x n (n - m)).card := by
  apply le_antisymm (card_Qset_mirror hp hm1 hm2)
  have := card_Qset_mirror hp (m := n - m) (by omega) (by omega)
  rwa [Nat.sub_sub_self hm2.le] at this

/-- Double counting: `∑_m |Q_m| = ∑_{ℓ, k} |col ℓ k|`. -/
lemma sum_Qset_eq (x : ℕ → Bool) (n : ℕ) :
    ∑ m ∈ Finset.Ico 1 n, (Qset x n m).card =
      ∑ ℓ : Bool, ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
  simp only [Qset, col, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_product]

lemma sum_col_ge (hp : Periodic x n) (ℓ : Bool) :
    total x n ℓ - 1 ≤ ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
  have htn : total x n ℓ ≤ n := by
    have := total_add_total_not x n ℓ; omega
  calc total x n ℓ - 1 = ∑ k ∈ Finset.Ico 1 (total x n ℓ), 1 := by simp
    _ ≤ ∑ k ∈ Finset.Ico 1 (total x n ℓ), (col x n ℓ k).card := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Ico] at hk
        exact Finset.card_pos.mpr (col_nonempty hp hk.1 hk.2)
    _ ≤ ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        simp only [Finset.mem_Ico, Finset.mem_range] at *
        omega

/-- Tightness: every column contains at most one half-length. -/
def Tight (x : ℕ → Bool) (n : ℕ) (ℓ : Bool) : Prop :=
  ∀ k m m', m ∈ col x n ℓ k → m' ∈ col x n ℓ k → m = m'

lemma tight_of_sum (hp : Periodic x n) (ℓ : Bool)
    (h : ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card ≤ total x n ℓ - 1) : Tight x n ℓ := by
  intro k m m' hm hm'
  by_contra hne
  have hb := col_bounds hp hm
  have htn : total x n ℓ ≤ n := by
    have := total_add_total_not x n ℓ; omega
  have two : 2 ≤ (col x n ℓ k).card := by
    have : ({m, m'} : Finset ℕ) ⊆ col x n ℓ k := by
      intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_pair hne] at this
    exact this
  have : total x n ℓ - 1 < ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
    calc total x n ℓ - 1 = ∑ k ∈ Finset.Ico 1 (total x n ℓ), 1 := by simp
      _ < ∑ k ∈ Finset.Ico 1 (total x n ℓ), (col x n ℓ k).card := by
          apply Finset.sum_lt_sum
          · intro k hk
            rw [Finset.mem_Ico] at hk
            exact Finset.card_pos.mpr (col_nonempty hp hk.1 hk.2)
          · exact ⟨k, by rw [Finset.mem_Ico]; omega, by omega⟩
      _ ≤ ∑ k ∈ Finset.range (n + 1), (col x n ℓ k).card := by
          apply Finset.sum_le_sum_of_subset
          intro k hk
          simp only [Finset.mem_Ico, Finset.mem_range] at *
          omega
  omega

end Circ
