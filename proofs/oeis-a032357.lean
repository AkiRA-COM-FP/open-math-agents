import OMAStatements.S_oeis_a032357

open OMA.S_oeis_a032357 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032357.main := by
  have st (n : ℕ) : a (n + 1) = catalan (n + 1) - a n := by
    rw [a, a, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, eq_sub_iff_add_eq, add_right_comm,
      ← Finset.sum_add_distrib, Finset.sum_eq_zero fun k hk => ?_, zero_add]
    rw [show n + 1 - k = n - k + 1 by simp at hk; omega, pow_succ]
    ring
  rintro (_ | _ | m) hn
  iterate 2 omega
  have := Nat.succ_mul_centralBinom_succ (m + 1)
  rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
  have r : ((m + 3) * catalan (m + 1 + 1) : ℤ) = 2 * (2 * (m + 1) + 1) * catalan (m + 1) := by
    exact_mod_cast Nat.eq_of_mul_eq_mul_left (m + 1).succ_pos (by linarith)
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  push_cast
  linear_combination ((m : ℤ) + 3) * st (m + 1) - 2 * (2 * ((m : ℤ) + 2) - 1) * st m + r
