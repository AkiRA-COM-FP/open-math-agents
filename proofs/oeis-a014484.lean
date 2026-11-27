import OMAStatements.S_oeis_a014484
import Mathlib

/-! Clear the exact division by six and expand the factorials at the shifted indices. -/

open OMA.S_oeis_a014484

lemma OMA.scaled (k : ℕ) : (a k : ℤ) * 6 = ((k + 2).factorial * (2 * k + 3) * 2 ^ k : ℕ) := by
  have h : 6 ∣ (k + 2).factorial * (2 * k + 3) * 2 ^ k := by
    cases k with
    | zero => decide
    | succ k => exact ((Nat.factorial_dvd_factorial (by omega : 3 ≤ k + 1 + 2)).mul_right _).mul_right _
  exact_mod_cast Nat.div_mul_cancel h

theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 2 m, show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
  have h0 := OMA.scaled m
  have h1 := OMA.scaled (m + 1)
  have h2 := OMA.scaled (m + 2)
  simp only [Nat.factorial_succ, pow_succ] at h0 h1 h2
  push_cast at h0 h1 h2 ⊢
  apply mul_right_cancel₀ (by decide : (6 : ℤ) ≠ 0)
  linear_combination h2 - (2 * ((m : ℤ) + 2) + 9) * h1 + 6 * ((m : ℤ) + 3) * h0
