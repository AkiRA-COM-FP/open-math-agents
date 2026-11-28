import OMAStatements.S_oeis_a266073

-- Credit: @oh-meh
-- Rule 3 moves the unique black cell one step right every two generations.
open OMA.S_oeis_a266073

private theorem rule_three (l c r : Bool) : update l c r = !(l || c) := by
  cases l <;> cases c <;> cases r <;> rfl

private theorem rows (k : ℕ) :
    (∀ i : ℤ, cell (2*k) i = decide (i = k)) ∧
    (∀ i : ℤ, cell (2*k+1) i = decide (i ≠ k ∧ i ≠ k+1)) := by
  induction k with
  | zero =>
    constructor
    · intro i
      rfl
    · intro i
      apply Bool.eq_iff_iff.mpr
      simp [cell, rule_three]
      omega
  | succ k ih =>
    have he (i : ℤ) : cell (2*(k+1)) i = decide (i = (k+1 : ℕ)) := by
      rw [show 2*(k+1) = (2*k+1)+1 by omega, cell, rule_three, ih.2, ih.2]
      apply Bool.eq_iff_iff.mpr
      simp
      omega
    refine ⟨he, ?_⟩
    intro i
    rw [cell, rule_three, he, he]
    apply Bool.eq_iff_iff.mpr
    simp
    omega

private theorem counts (k : ℕ) :
    a (2*k) = 4*(k : ℤ) ∧ a (2*k+1) = 2 := by
  constructor
  · unfold a
    simp_rw [(rows k).1]
    have h (j : ℕ) :
        (if decide ((j : ℤ) - (2*k : ℕ) = k) then (0 : ℤ) else 1) =
        1 - (if 3*k = j then 1 else 0) := by
      split_ifs <;> simp_all <;> omega
    simp_rw [h]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq, show 3*k < 2*(2*k)+1 by omega]
    omega
  · unfold a
    simp_rw [(rows k).2]
    have h (j : ℕ) :
        (if decide ((j : ℤ) - (2*k+1 : ℕ) ≠ k ∧ (j : ℤ) - (2*k+1 : ℕ) ≠ k+1)
         then (0 : ℤ) else 1) =
        (if 3*k+1 = j then 1 else 0) + (if 3*k+2 = j then 1 else 0) := by
      split_ifs <;> simp_all <;> omega
    simp_rw [h]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq, show 3*k+1 < 2*(2*k+1)+1 by omega,
      show 3*k+2 < 2*(2*k+1)+1 by omega]

private theorem formula (n : ℕ) :
    a n = (-1 : ℤ)^n * n + n - (-1 : ℤ)^n + 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n = 2*k by omega, (counts k).1, pow_mul]
    push_cast
    norm_num
    ring
  · rw [show n = 2*k+1 by omega, (counts k).2, pow_succ, pow_mul]
    push_cast
    norm_num

private theorem recurrence (n : ℕ) (hn : 3 < n) :
    a n = 2 * a (n-2) - a (n-4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
  simp only [formula]
  rw [show 4+k-2 = 2+k by omega, show 4+k-4 = k by omega, pow_add, pow_add]
  push_cast
  ring

open PowerSeries in
private theorem generating :
    mk (fun n => (a n : ℚ)) * (-1 + X ^ 2) ^ 2 = 2 * X + 4 * X ^ 2 - 2 * X ^ 3 := by
  let F := mk (fun n => (a n : ℚ))
  change F * _ = _
  rw [show F * (-1 + X ^ 2) ^ 2 = F - 2*(F*X^2) + F*X^4 by ring]
  ext n
  simp only [map_add, map_sub, two_mul, show (4 : ℚ⟦X⟧) = 2+2 by norm_num,
    add_mul, coeff_X, coeff_X_pow, coeff_mul_X_pow', F, coeff_mk]
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [formula, coeff_X, coeff_X_pow]
  · have h := recurrence n (by omega)
    simp [show 2 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega]
    exact_mod_cast (by omega : a n - (a (n-2) + a (n-2)) + a (n-4) = 0)

theorem OMA.solution : type_of% @OMA.S_oeis_a266073.main := by
  exact ⟨formula, recurrence, generating⟩
