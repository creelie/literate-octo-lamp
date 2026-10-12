import Circ.MainX
import Circ.Statement

/-!
# From circular words to periodic sequences
-/

open Classical

namespace Circ

open Simpson

/-- The periodic sequence of a circular word. -/
def seq (w : List Bool) : ℕ → Bool := fun j => w.getD (j % w.length) false

lemma seq_periodic (w : List Bool) : Periodic (seq w) w.length := by
  intro i
  simp [seq]

lemma seq_eq {w : List Bool} {j : ℕ} (hj : j < w.length) : seq w j = w[j] := by
  simp [seq, Nat.mod_eq_of_lt hj, hj]

lemma seq_congr {w : List Bool} {a b : ℕ} (h : a % w.length = b % w.length) :
    seq w a = seq w b := by
  simp only [seq, h]

lemma take_rotate (w : List Bool) (hn : 0 < w.length) (i L : ℕ) (hL : L ≤ w.length) :
    (w.rotate i).take L = window (seq w) i L := by
  apply List.ext_getElem
  · simp [hL]
  · intro t h1 h2
    have ht : t < L := by simpa using h2
    rw [List.getElem_take, List.getElem_rotate]
    simp only [window, List.getElem_map, List.getElem_range]
    rw [← seq_eq (Nat.mod_lt _ hn)]
    apply seq_congr
    rw [Nat.mod_mod, Nat.add_comm]

lemma length_eq_count (u : List Bool) : u.length = u.count true + u.count false := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [List.length_cons, List.count_cons, List.count_cons, ih]
    cases b <;> simp <;> omega

lemma abSq_window {x : ℕ → Bool} {i L : ℕ} :
    IsAbelianSquare (window x i L) ↔ ∃ m, 1 ≤ m ∧ L = 2 * m ∧ IsSq x i m := by
  constructor
  · rintro ⟨u, v, hs, hu, hc⟩
    have hlen : u.length = v.length := by
      rw [length_eq_count u, length_eq_count v, hc true, hc false]
    have hL : L = 2 * u.length := by
      have := congrArg List.length hs
      rw [window_length, List.length_append] at this
      omega
    refine ⟨u.length, List.length_pos_iff.mpr hu, hL, ?_⟩
    rw [hL, two_mul, window_add] at hs
    obtain ⟨h1, h2⟩ := List.append_inj hs.symm (by simp)
    have := hc true
    rw [h1, h2, window_count, window_count] at this
    exact (isSq_iff true i u.length).mpr this
  · rintro ⟨m, hm, rfl, hsq⟩
    refine ⟨window x i m, window x (i + m) m, by rw [two_mul, window_add], ?_, fun c => ?_⟩
    · exact List.ne_nil_of_length_pos (by simp; omega)
    · rw [window_count, window_count]
      exact (isSq_iff c i m).mp hsq

lemma length_of_mem_Sset {x : ℕ → Bool} {n m : ℕ} {s : List Bool} (h : s ∈ Sset x n m) :
    s.length = 2 * m := by
  simp only [Sset, Finset.mem_image] at h
  obtain ⟨i, -, rfl⟩ := h
  simp

lemma filter_eq_biUnion (w : List Bool) (hn : 0 < w.length) :
    (factors w).filter IsAbelianSquare =
      (Finset.Ico 1 (w.length / 2 + 1)).biUnion (Sset (seq w) w.length) := by
  ext s
  simp only [Finset.mem_filter, factors, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_Ico, Sset, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨⟨i, L, ⟨hi, hL1, hL2⟩, rfl⟩, hab⟩
    rw [take_rotate w hn i L hL2] at hab ⊢
    obtain ⟨m, hm, rfl, hsq⟩ := abSq_window.mp hab
    exact ⟨m, ⟨hm, by omega⟩, i, ⟨hi, hsq⟩, rfl⟩
  · rintro ⟨m, ⟨hm1, hm2⟩, i, ⟨hi, hsq⟩, rfl⟩
    have h2 : 2 * m ≤ w.length := by omega
    refine ⟨⟨i, 2 * m, ⟨hi, by omega, h2⟩, take_rotate w hn i _ h2⟩, ?_⟩
    exact abSq_window.mpr ⟨m, hm1, rfl, hsq⟩

theorem num_eq_Dint (w : List Bool) (hn : 0 < w.length) :
    numDistinctAbelianSquares w = Dint (seq w) w.length := by
  unfold numDistinctAbelianSquares Dint
  rw [filter_eq_biUnion w hn, Finset.card_biUnion]
  intro m _ m' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro s h1 h2
  have := length_of_mem_Sset h1
  have := length_of_mem_Sset h2
  omega

/-- Rotations of the sequence are conjugates of the word. -/
lemma shape_iff_conj (w : List Bool) (hn : 0 < w.length) (f : ℕ → Bool) :
    (∃ s, ∀ i, seq w (s + i) = f (i % w.length)) ↔
      IsConj w ((List.range w.length).map f) := by
  set n := w.length with hnd
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨n - s % n, ?_⟩
    apply List.ext_getElem
    · simp [n]
    · intro j h1 h2
      rw [List.getElem_rotate]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [← seq_eq h1, ← hs]
      apply seq_congr
      have e1 := Nat.mod_add_div s n
      have e2 := Nat.mod_lt s hn
      rw [show s + (j + (n - s % n)) = j + n * (s / n + 1) by
        rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left]
  · rintro ⟨r, hr⟩
    refine ⟨n - r % n, fun i => ?_⟩
    have hk : (n - r % n + i) % n < n := Nat.mod_lt _ hn
    rw [seq_congr (b := (n - r % n + i) % n) (by rw [← hnd, Nat.mod_mod]), seq_eq hk]
    simp only [hr]
    rw [List.getElem_rotate]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1
    have e1 := Nat.mod_add_div r n
    have e2 := Nat.mod_lt r hn
    rw [Nat.mod_add_mod, show n - r % n + i + r = i + n * (r / n + 1) by
      rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left]

end Circ
