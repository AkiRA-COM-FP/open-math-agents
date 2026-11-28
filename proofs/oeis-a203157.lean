import OMAStatements.S_oeis_a203157

-- Problem: OEIS A203157, the (n-1)-st elementary symmetric function of the first n triangular
-- numbers x_i = (i+1)(i+2)/2. With S(n) = x_0..x_(n-1), e_n(x_n :: S(n)) = e_n(S(n)) + x_n e_(n-1)(S(n))
-- and e_n(S(n)) = prod S(n), so a(n+1) = prod S(n) + x_n a(n). By induction
-- 2^n prod S(n) = n! (n+1)! and 2^(n-1) a(n) = n (n!)^2, from which the recurrence follows.

namespace OMA.A203157

open OMA.S_oeis_a203157

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

lemma two_x (i : ℕ) : 2 * x i = ((i : ℤ) + 1) * ((i : ℤ) + 2) := by
  have h : 2 ∣ (i + 1) * (i + 2) := (Nat.even_mul_succ_self (i + 1)).two_dvd
  have : 2 * ((i + 1) * (i + 2) / 2) = (i + 1) * (i + 2) := Nat.mul_div_cancel' h
  simp only [x]
  exact_mod_cast this

lemma prod_S (n : ℕ) : 2 ^ n * (S n).prod = (n.factorial : ℤ) * ((n + 1).factorial : ℤ) := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S_succ, Multiset.prod_cons, pow_succ,
      show 2 ^ n * 2 * (x n * (S n).prod) = (2 * x n) * (2 ^ n * (S n).prod) by ring, ih, two_x,
      Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast; ring

lemma closed (n : ℕ) : 2 ^ n * a (n + 1) = ((n : ℤ) + 1) * ((n + 1).factorial : ℤ) ^ 2 := by
  induction n with
  | zero => simp [a_one]
  | succ m ih =>
    rw [a_succ, pow_succ,
      show 2 ^ m * 2 * ((S (m + 1)).prod + x (m + 1) * a (m + 1)) =
        2 ^ (m + 1) * (S (m + 1)).prod + (2 * x (m + 1)) * (2 ^ m * a (m + 1)) by ring,
      prod_S, ih, two_x, Nat.factorial_succ (m + 1)]
    push_cast; ring

end OMA.A203157

theorem OMA.solution : type_of% @OMA.S_oeis_a203157.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  have h1 := OMA.A203157.closed (m + 1)
  have h0 := OMA.A203157.closed m
  have hp : (2 : ℤ) ^ (m + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hp
  rw [Nat.factorial_succ (m + 1)] at h1
  push_cast at h0 h1 ⊢
  linear_combination (-2 * ((m : ℤ) + 1)) * h1 + 2 * ((m : ℤ) + 2) ^ 3 * h0
