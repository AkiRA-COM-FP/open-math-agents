import OMAStatements.S_oeis_a329227
import Mathlib

-- Proof: the denominator expands to 1 - X - X^2 - X^3 + X^4 - X^5 + X^6. Writing every Padovan
-- term P(m+k) through P(m), P(m+1), P(m+2) shows the products a(n) = P(n) P(n+1) satisfy the
-- matching order-6 recurrence; the first six coefficients are checked directly.

namespace OMA.P_oeis_a329227
open OMA.S_oeis_a329227 PowerSeries

lemma rec6 (m : ℕ) :
    a (m + 6) = a (m + 5) + a (m + 4) + a (m + 3) - a (m + 2) + a (m + 1) - a m := by
  unfold a
  have h3 : P (m + 3) = P (m + 1) + P m := by rw [P]
  have h4 : P (m + 4) = P (m + 2) + P (m + 1) := by rw [P]
  have h5 : P (m + 5) = P (m + 3) + P (m + 2) := by rw [P]
  have h6 : P (m + 6) = P (m + 4) + P (m + 3) := by rw [P]
  have h7 : P (m + 7) = P (m + 5) + P (m + 4) := by rw [P]
  simp only [show m + 6 + 1 = m + 7 from rfl, show m + 5 + 1 = m + 6 from rfl,
    show m + 4 + 1 = m + 5 from rfl, show m + 3 + 1 = m + 4 from rfl,
    show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl]
  rw [h7, h6, h5, h4, h3]
  ring

end OMA.P_oeis_a329227

open OMA.P_oeis_a329227 in
theorem OMA.solution : type_of% @OMA.S_oeis_a329227.main := by
  open OMA.S_oeis_a329227 PowerSeries in
  ext n
  have hD : ((1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3) : ℤ⟦X⟧) =
      1 - X ^ 1 - X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 + X ^ 6 := by ring
  rw [hD, mul_comm]
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases h : n < 6
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [if_pos (show 1 ≤ m + 6 by omega), if_pos (show 2 ≤ m + 6 by omega),
      if_pos (show 3 ≤ m + 6 by omega), if_pos (show 4 ≤ m + 6 by omega),
      if_pos (show 5 ≤ m + 6 by omega), if_pos (show 6 ≤ m + 6 by omega),
      if_neg (show m + 6 ≠ 5 by omega),
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega, rec6]
    ring
