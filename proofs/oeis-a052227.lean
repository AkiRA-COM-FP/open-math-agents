import OMAStatements.S_oeis_a052227
import Mathlib

open OMA.S_oeis_a052227 in
theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  have cc (m : ℕ) : ((3 * m).choose m : ℚ) = (3 * m).factorial / (m.factorial * (2 * m).factorial) := by
    rw [Nat.cast_choose ℚ (by omega : m ≤ 3 * m), show 3 * m - m = 2 * m by omega]
  simp only [a, cc]
  simp [Nat.factorial_succ, mul_add]
  field_simp
  ring
