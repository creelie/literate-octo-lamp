import Circ.Bound

/-!
# Distinct abelian squares and the lower bound
-/

open Classical

namespace Circ

variable {x : ℕ → Bool} {ℓ : Bool} {n : ℕ}

/-- The factor of length `L` starting at position `i`. -/
def window (x : ℕ → Bool) (i L : ℕ) : List Bool := (List.range L).map (fun t => x (i + t))

@[simp] lemma window_length (i L : ℕ) : (window x i L).length = L := by simp [window]

lemma window_getD (i L t : ℕ) (ht : t < L) : (window x i L).getD t false = x (i + t) := by
  simp [window, ht]

lemma window_add (i L₁ L₂ : ℕ) : window x i (L₁ + L₂) = window x i L₁ ++ window x (i + L₁) L₂ := by
  simp only [window, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [Nat.add_assoc]

lemma window_count (i L : ℕ) : (window x i L).count ℓ = cnt x ℓ i L := by
  induction L with
  | zero => simp [window]
  | succ L ih =>
    rw [window_add, List.count_append, ih, cnt_succ]
    simp only [window, List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
    rw [List.count_singleton]
    congr 1
    by_cases h : x (i + L) = ℓ <;> simp [h]

lemma window_take (i m : ℕ) : (window x i (2 * m)).take m = window x i m := by
  rw [two_mul, window_add, List.take_append_of_le_length (by simp)]
  simp

lemma window_shift (hp : Periodic x n) (i L : ℕ) : window x (i + n) L = window x i L := by
  simp only [window]
  apply List.map_congr_left
  intro t _
  rw [Nat.add_right_comm, hp]

lemma window_mod (hp : Periodic x n) (i L : ℕ) : window x (i % n) L = window x i L := by
  simp only [window]
  apply List.map_congr_left
  intro t _
  conv_rhs => rw [← Nat.mod_add_div i n]
  rw [Nat.add_right_comm, Nat.mul_comm, hp.add_mul]

lemma cnt_mod (hp : Periodic x n) (i k : ℕ) : cnt x ℓ (i % n) k = cnt x ℓ i k := by
  rw [← window_count, ← window_count, window_mod hp]

lemma x_mod_add (hp : Periodic x n) (i t : ℕ) : x (i % n + t) = x (i + t) := by
  conv_rhs => rw [← Nat.mod_add_div i n]
  rw [Nat.add_right_comm, Nat.mul_comm, hp.add_mul]

/-- The distinct abelian squares of half-length `m`. -/
noncomputable def Sset (x : ℕ → Bool) (n m : ℕ) : Finset (List Bool) :=
  ((Finset.range n).filter (fun i => IsSq x i m)).image (fun i => window x i (2 * m))

/-- Last letter of the left half, and its number of occurrences in the left half. -/
def phi (m : ℕ) (w : List Bool) : Bool × ℕ :=
  (w.getD (m - 1) false, (w.take m).count (w.getD (m - 1) false))

lemma phi_window {m : ℕ} (hm : 1 ≤ m) (i : ℕ) :
    phi m (window x i (2 * m)) = (x (i + (m - 1)), cnt x (x (i + (m - 1))) i m) := by
  simp only [phi]
  rw [window_getD _ _ _ (by omega), window_take, window_count]

lemma Qset_eq_image (hp : Periodic x n) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Qset x n m = (Sset x n m).image (phi m) := by
  have hn : 0 < n := by omega
  ext ⟨ℓ', k⟩
  rw [mem_Qset, Finset.mem_image]
  constructor
  · rintro ⟨-, i, hx, hsq, hc⟩
    refine ⟨window x (i % n) (2 * m), ?_, ?_⟩
    · simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      exact ⟨i % n, ⟨Nat.mod_lt _ hn, IsSq.mod hp |>.mpr hsq⟩, rfl⟩
    · rw [phi_window hm1, x_mod_add hp, hx, cnt_mod hp, hc]
  · rintro ⟨w, hw, hphi⟩
    simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨i, ⟨-, hsq⟩, rfl⟩ := hw
    rw [phi_window hm1, Prod.mk.injEq] at hphi
    obtain ⟨h1, h2⟩ := hphi
    refine ⟨?_, i, h1, hsq, ?_⟩
    · rw [← h2, h1]; exact (cnt_le i m).trans hmn
    · rw [← h1]; exact h2

lemma card_Qset_le (hp : Periodic x n) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (Qset x n m).card ≤ (Sset x n m).card := by
  rw [Qset_eq_image hp hm1 hmn]; exact Finset.card_image_le

/-- Number of distinct abelian squares, as a sum over half-lengths. -/
noncomputable def Dint (x : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Ico 1 (n / 2 + 1), (Sset x n m).card

/-- `F = ∑_{m ≤ n/2} |Q_m|`. -/
noncomputable def Fsum (x : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Ico 1 (n / 2 + 1), (Qset x n m).card

/-- `N = ∑_{1 ≤ m < n} |Q_m|`. -/
noncomputable def Nsum (x : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Ico 1 n, (Qset x n m).card

lemma Fsum_le_Dint (hp : Periodic x n) : Fsum x n ≤ Dint x n := by
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_Ico] at hm
  exact card_Qset_le hp hm.1 (by omega)

lemma Nsum_eq (hp : Periodic x n) (hn : 0 < n) :
    Nsum x n + (if n % 2 = 0 then (Qset x n (n / 2)).card else 0) = 2 * Fsum x n := by
  unfold Nsum Fsum
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ n / 2 + 1 by omega) (show n / 2 + 1 ≤ n by omega)]
  have hrefl : ∑ m ∈ Finset.Ico (n / 2 + 1) n, (Qset x n m).card =
      ∑ m ∈ Finset.Ico (n / 2 + 1) n, (Qset x n (n - m)).card := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact card_Qset_symm hp (by omega) (by omega)
  rw [hrefl, Finset.sum_Ico_reflect (fun m => (Qset x n m).card) (n / 2 + 1) (Nat.le_succ n)]
  rw [show n + 1 - n = 1 by omega]
  split
  · rename_i he
    rw [show n + 1 - (n / 2 + 1) = n / 2 by omega]
    rw [Finset.sum_Ico_succ_top (show 1 ≤ n / 2 by omega)]
    ring
  · rename_i ho
    rw [show n + 1 - (n / 2 + 1) = n / 2 + 1 by omega]
    ring

lemma Nsum_ge (hp : Periodic x n) : n - 2 ≤ Nsum x n := by
  unfold Nsum
  rw [sum_Qset_eq, Fintype.sum_bool]
  have h1 := sum_col_ge hp (x := x) true
  have h2 := sum_col_ge hp (x := x) false
  have h3 := total_add_total_not x n true
  simp only [Bool.not_true] at h3
  omega

theorem lower_bound (hp : Periodic x n) (hn : 0 < n) : (n - 1) / 2 ≤ Dint x n := by
  have a := Nsum_eq hp hn
  have b := Nsum_ge hp (x := x)
  have c := Fsum_le_Dint hp (x := x)
  split at a <;> omega

/-- Rigidity: abelian squares of the same half-length `m ≤ n/2` that agree in the last
letter of the left half and in its count are equal. -/
def Rigid (x : ℕ → Bool) (n : ℕ) : Prop :=
  ∀ m i i', 1 ≤ m → 2 * m ≤ n → IsSq x i m → IsSq x i' m →
    x (i + (m - 1)) = x (i' + (m - 1)) →
    cnt x (x (i + (m - 1))) i m = cnt x (x (i + (m - 1))) i' m →
    ∀ t < 2 * m, x (i + t) = x (i' + t)

lemma rigid_of_card (hp : Periodic x n) (hn : 0 < n)
    (h : ∀ m, 1 ≤ m → 2 * m ≤ n → (Sset x n m).card = (Qset x n m).card) : Rigid x n := by
  intro m i i' hm1 hm2 hsq hsq' hx hc t ht
  have hinj : Set.InjOn (phi m) (Sset x n m) := by
    rw [← Finset.card_image_iff, ← Qset_eq_image hp hm1 (by omega), h m hm1 hm2]
  have mem : ∀ j, IsSq x j m → window x j (2 * m) ∈ Sset x n m := by
    intro j hj
    simp only [Sset, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    exact ⟨j % n, ⟨Nat.mod_lt _ hn, IsSq.mod hp |>.mpr hj⟩, window_mod hp _ _⟩
  have heq := hinj (mem i hsq) (mem i' hsq') (by rw [phi_window hm1, phi_window hm1, hc, hx])
  have := congrArg (fun w => w.getD t false) heq
  rwa [window_getD _ _ _ ht, window_getD _ _ _ ht] at this

/-- Consequences of equality in the lower bound. -/
theorem equality_facts (hp : Periodic x n) (hn : 0 < n) (hD : Dint x n = (n - 1) / 2) :
    Rigid x n ∧ Nsum x n + (if n % 2 = 0 then (Qset x n (n / 2)).card else 0) = 2 * ((n - 1) / 2) := by
  have a := Nsum_eq hp hn
  have b := Nsum_ge hp (x := x)
  have c := Fsum_le_Dint hp (x := x)
  have hF : Fsum x n = Dint x n := by split at a <;> omega
  refine ⟨rigid_of_card hp hn ?_, by rw [a, hF, hD]⟩
  intro m hm1 hm2
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.Ico 1 (n / 2 + 1))
    (f := fun m => (Qset x n m).card) (g := fun m => (Sset x n m).card) ?_).mp hF
  · exact (this m (by rw [Finset.mem_Ico]; omega)).symm
  · intro m hm
    rw [Finset.mem_Ico] at hm
    exact card_Qset_le hp hm.1 (by omega)

lemma not_isSq_of_Qset_empty (hp : Periodic x n) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (h : (Qset x n m).card = 0) (i : ℕ) : ¬ IsSq x i m := by
  intro hsq
  rw [Finset.card_eq_zero] at h
  have : (x (i + (m - 1)), cnt x (x (i + (m - 1))) i m) ∈ Qset x n m := by
    rw [mem_Qset]
    exact ⟨(cnt_le i m).trans hmn, i, rfl, hsq, rfl⟩
  rw [h] at this
  simp at this

end Circ
