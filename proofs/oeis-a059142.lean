import OMAStatements.S_oeis_a059142
import Mathlib

namespace OMA.S_oeis_a059142

theorem psum (k : ℕ) : (phrase k).sum = 7 * padicValNat 2 k + 11 := by
  simp [phrase, ruler]
  ring

theorem sumv (N : ℕ) : ∑ k ∈ Finset.range N, padicValNat 2 (k + 1) = padicValNat 2 N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero N)]
    ring

theorem dsum (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 0 < 2 ^ (m + 1) - 1 := by
      have : 2 ≤ 2 ^ (m + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.digits_def' (by norm_num) h1]
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hpos : 0 < 2 ^ m := by positivity
    have e1 : (2 ^ (m + 1) - 1) % 2 = 1 := by omega
    have e2 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by omega
    rw [e1, e2, List.sum_cons, ih]
    omega

theorem a_closed (n : ℕ) : (a n : ℤ) = -25 + 9 * 2 ^ (2 + n) - 7 * n := by
  have hN : ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), padicValNat 2 (k + 1) = 2 ^ (n + 1) - 1 - (n + 1) := by
    rw [sumv]
    have := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ (n + 1) - 1)
    rw [dsum] at this
    simpa using this
  have h2 : a n = 7 * ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), padicValNat 2 (k + 1) + 11 * (2 ^ (n + 1) - 1) := by
    simp only [a, psum, Finset.sum_add_distrib, Finset.mul_sum]
    simp
    ring
  rw [h2, hN]
  have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hp : (2 : ℤ) ^ (2 + n) = 2 * 2 * 2 ^ n := by ring
  have hp2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hq : ((2 ^ (n + 1) : ℕ) : ℤ) = 2 * 2 ^ n := by push_cast; ring
  zify [show 1 ≤ 2 ^ (n + 1) by omega, show n + 1 ≤ 2 ^ (n + 1) - 1 by omega]
  rw [hp, hp2]
  ring

theorem gf_gen (f : ℕ → ℚ) (q0 : f 0 = 11) (q1 : f 1 = 40) (q2 : f 2 = 105)
    (hrec : ∀ n, 3 ≤ n → f n = 4 * f (n - 1) - 5 * f (n - 2) + 2 * f (n - 3)) :
    PowerSeries.mk f * ((PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1)) = 4 * PowerSeries.X - 11 := by
  open PowerSeries in
  have hP : ((X - 1) ^ 2 * (2 * X - 1) : PowerSeries ℚ) = 2 • X ^ 3 - 5 • X ^ 2 + 4 • X - 1 := by ring
  have e : PowerSeries.mk f * (2 • X ^ 3 - 5 • X ^ 2 + 4 • X - 1) =
      2 • (X ^ 3 * PowerSeries.mk f) - 5 • (X ^ 2 * PowerSeries.mk f) + 4 • (X ^ 1 * PowerSeries.mk f)
        - PowerSeries.mk f := by ring
  have hQ : (4 * X - 11 : PowerSeries ℚ) = 4 • X - 11 • 1 := by simp [nsmul_eq_mul]
  rw [hP, e, hQ]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X]
  rcases (by omega : n < 3 ∨ 3 ≤ n) with h | h
  · interval_cases n
    · simp [q0, q1, q2]
    · simp [q0, q1, q2]; norm_num
    · simp [q0, q1, q2]; norm_num
  · have hq := hrec n h
    have n1 : n ≠ 1 := by omega
    have n0 : n ≠ 0 := by omega
    simp [n1, n0, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, hq]
    ring

theorem solution_aux : type_of% @OMA.S_oeis_a059142.main := by
  refine ⟨?_, fun n => a_closed n, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
      show k + 3 - 3 = k by omega, a_closed]
    push_cast
    ring
  · have := gf_gen (fun n => (a n : ℚ)) (by
        have := a_closed 0; simp at this; exact_mod_cast (by simpa using this : (a 0 : ℤ) = 11))
      (by have := a_closed 1; norm_num at this; exact_mod_cast this)
      (by have := a_closed 2; norm_num at this; exact_mod_cast this)
      (by
        intro n hn
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
        simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
          show k + 3 - 3 = k by omega]
        have h1 := a_closed (k + 3)
        have h2 := a_closed (k + 2)
        have h3 := a_closed (k + 1)
        have h4 := a_closed k
        have : ((a (k + 3) : ℤ) : ℚ) = 4 * (a (k + 2) : ℤ) - 5 * (a (k + 1) : ℤ) + 2 * (a k : ℤ) := by
          rw [h1, h2, h3, h4]; push_cast; ring
        exact_mod_cast this)
    exact this

end OMA.S_oeis_a059142

theorem OMA.solution : type_of% @OMA.S_oeis_a059142.main := OMA.S_oeis_a059142.solution_aux
