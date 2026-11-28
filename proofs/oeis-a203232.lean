import OMAStatements.S_oeis_a203232
import Mathlib

-- Proof: two steps of the recursion always multiply by the digits 2 and 3 (in some order), so
-- P(n+2) = 6 P(n) and a(n+2) = 6 a(n) + 5 P(n); eliminating P gives the recurrence for all n,
-- and the generating function follows coefficient by coefficient.

namespace OMA.P_oeis_a203232
open OMA.S_oeis_a203232 PowerSeries

lemma two_step (n : ℕ) :
    products (n + 2) = (6 * (products n).1, 6 * (products n).2 + 5 * (products n).1) := by
  rw [products, products]
  simp only [digit]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h1 : (n + 1) % 2 = 1 := by omega
    rw [h, h1]
    ext <;> simp <;> ring
  · have h1 : (n + 1) % 2 = 0 := by omega
    rw [h, h1]
    ext <;> simp <;> ring

lemma rec4 (n : ℕ) : a (n + 4) = 12 * a (n + 2) - 36 * a n := by
  unfold a
  rw [two_step (n + 2), two_step n]
  simp only
  ring

lemma a0 : a 0 = 0 := by decide
lemma a1 : a 1 = 1 := by decide
lemma a2 : a 2 = 5 := by decide
lemma a3 : a 3 = 16 := by decide

end OMA.P_oeis_a203232

open OMA.P_oeis_a203232 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203232.main := by
  open OMA.S_oeis_a203232 PowerSeries in
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [rec4]
    congr 2
  · ext n
    have hexp : (1 - C 6 * X ^ 2 : ℤ⟦X⟧) ^ 2 = 1 - C 12 * X ^ 2 + C 36 * X ^ 4 := by
      simp only [map_ofNat]
      ring
    rw [hexp, add_mul, sub_mul, one_mul, mul_assoc, mul_assoc]
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    by_cases h : n < 4
    · interval_cases n <;> simp [a0, a1, a2, a3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have e1 : m + 4 - 2 = m + 2 := by omega
      have e2 : m + 4 - 4 = m := by omega
      simp only [e1, e2, rec4, if_pos (show 2 ≤ m + 4 by omega), if_pos (show 4 ≤ m + 4 by omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
