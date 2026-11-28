import OMAStatements.S_oeis_a203230

-- Problem: A203230 (statement of PR #22208). With S(n) = x_0..x_(n-1), e_n(x_n :: S(n)) = e_n(S(n)) + x_n e_(n-1)(S(n))
-- and e_n(S(n)) = prod S(n), so a(n+1) = prod S(n) + x_n a(n). By induction prod S(2m) = 3^m,
-- 3 a(2m+1) = (4m+3) 3^m, a(2m+2) = 4(m+1) 3^m; the recurrence follows, and with the first values
-- 1, 4, 7, 24 it gives the generating function.

namespace OMA.A203230

open OMA.S_oeis_a203230

def S (n : ℕ) : Multiset ℤ := (Multiset.range n).map x

lemma esymm_cons (c : ℤ) (s : Multiset ℤ) (k : ℕ) :
    (c ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + c * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

lemma S_succ (n : ℕ) : S (n + 1) = x n ::ₘ S n := by
  simp [S, Multiset.range_succ]

lemma card_S (n : ℕ) : Multiset.card (S n) = n := by simp [S]

lemma esymm_S_top (n : ℕ) : (S n).esymm n = (S n).prod := by
  induction n with
  | zero => simp [S, Multiset.esymm]
  | succ n ih =>
    rw [S_succ, esymm_cons, ih, Multiset.prod_cons]
    have : (S n).esymm (n + 1) = 0 := by
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty (n + 1) (s := S n) (by rw [card_S]; omega)]
      simp
    rw [this, zero_add]

lemma a_succ (m : ℕ) : a (m + 2) = (S (m + 1)).prod + x (m + 1) * a (m + 1) := by
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
    show Multiset.map x (Multiset.range (m + 2)) = S (m + 2) from rfl,
    show Multiset.map x (Multiset.range (m + 1)) = S (m + 1) from rfl,
    S_succ (m + 1), esymm_cons, esymm_S_top]

lemma a_one : a 1 = 1 := by simp [a, Multiset.esymm]

lemma x_even (m : ℕ) : x (2 * m) = 1 := by simp [x]
lemma x_odd (m : ℕ) : x (2 * m + 1) = 3 := by simp [x, Nat.add_mod]

lemma closed (m : ℕ) : (S (2 * m)).prod = 3 ^ m ∧ 3 * a (2 * m + 1) = (4 * m + 3) * 3 ^ m ∧
    a (2 * m + 2) = 4 * (m + 1) * 3 ^ m := by
  induction m with
  | zero =>
    refine ⟨by simp [S], by rw [a_one]; norm_num, ?_⟩
    rw [a_succ, a_one, S_succ]; simp [S, x]
  | succ m ih =>
    obtain ⟨hP, h1, h2⟩ := ih
    have hP' : (S (2 * (m + 1))).prod = 3 ^ (m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, S_succ, S_succ, Multiset.prod_cons,
        Multiset.prod_cons, hP, x_odd, x_even]; ring
    have h1' : 3 * a (2 * (m + 1) + 1) = (4 * ((m + 1 : ℕ) : ℤ) + 3) * 3 ^ (m + 1) := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, a_succ,
        show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hP',
        show 2 * (m + 1) = 2 * m + 2 by ring, h2,
        show 2 * m + 2 = 2 * (m + 1) by ring, x_even]
      push_cast; ring
    have h2' : a (2 * (m + 1) + 2) = 4 * (((m + 1 : ℕ) : ℤ) + 1) * 3 ^ (m + 1) := by
      rw [show 2 * (m + 1) + 2 = (2 * (m + 1)) + 2 by ring, a_succ,
        show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl, S_succ, Multiset.prod_cons, hP',
        x_even, x_odd]
      push_cast at h1' ⊢
      linarith
    exact ⟨hP', h1', h2'⟩

lemma odd_val (m : ℕ) : 3 * a (2 * m + 1) = (4 * m + 3) * 3 ^ m := (closed m).2.1
lemma even_val (m : ℕ) : a (2 * m + 2) = 4 * (m + 1) * 3 ^ m := (closed m).2.2

lemma recur (n : ℕ) (hn : 5 ≤ n) : a n = 6 * a (n - 2) - 9 * a (n - 4) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * (m + 2) + 1 ∨ n = 2 * (m + 2) + 2 := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact ⟨k - 3, Or.inr (by omega)⟩
    · exact ⟨k - 2, Or.inl (by omega)⟩
  · rw [show 2 * (m + 2) + 1 - 2 = 2 * (m + 1) + 1 by omega,
      show 2 * (m + 2) + 1 - 4 = 2 * m + 1 by omega]
    have h0 := odd_val (m + 2); have h1 := odd_val (m + 1); have h2 := odd_val m
    push_cast at h0 h1 h2
    have e : (3 : ℤ) ^ (m + 2) = 9 * 3 ^ m := by ring
    have e' : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
    rw [e] at h0; rw [e'] at h1
    nlinarith
  · rw [show 2 * (m + 2) + 2 - 2 = 2 * (m + 1) + 2 by omega,
      show 2 * (m + 2) + 2 - 4 = 2 * m + 2 by omega, even_val, even_val, even_val]
    push_cast; ring

end OMA.A203230

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203230.main := by
  refine ⟨OMA.A203230.recur, ?_⟩
  have hco : ∀ (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ),
      coeff n (f * (C c * X ^ k)) = if k ≤ n then c * coeff (n - k) f else 0 := by
    intro f c k n
    rw [show f * (C c * X ^ k) = f * X ^ k * C c by ring, coeff_mul_C, coeff_mul_X_pow']
    split_ifs <;> simp [mul_comm]
  have hpoly : ((-1 : PowerSeries ℤ) + 3 * X ^ 2) ^ 2 = 1 - C 6 * X ^ 2 + C 9 * X ^ 4 := by
    simp only [map_ofNat]; ring
  have hrhs : (X : PowerSeries ℤ) + 4 * X ^ 2 + X ^ 3 = C 1 * X ^ 1 + C 4 * X ^ 2 + C 1 * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  have v1 : OMA.S_oeis_a203230.a 1 = 1 := OMA.A203230.a_one
  have v2 : OMA.S_oeis_a203230.a 2 = 4 := by simpa using OMA.A203230.even_val 0
  have v3 : OMA.S_oeis_a203230.a 3 = 7 := by have := OMA.A203230.odd_val 1; norm_num at this; linarith
  have v4 : OMA.S_oeis_a203230.a 4 = 24 := by simpa using OMA.A203230.even_val 1
  rw [hpoly, hrhs]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk, coeff_C_mul_X_pow, hco]
  rcases n with _ | _ | _ | _ | _ | m
  · simp
  · simp [v1]
  · simp [v2]
  · simp [v1, v3]
  · simp [v2, v4]
  · have h := OMA.A203230.recur (m + 5) (by omega)
    simp only [show 2 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, if_true,
      show m + 5 ≠ 0 by omega, show m + 5 - 2 ≠ 0 by omega, show m + 5 - 4 ≠ 0 by omega, if_false,
      show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega]
    rw [h]; ring
