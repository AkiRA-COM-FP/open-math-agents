import OMAStatements.S_oeis_a181666

-- The 3-divisibility condition forces an even exponent gap. Mathlib then removes the power of 2.

namespace OMA.A181666

open OMA.S_oeis_a181666

lemma oddPart_eq (n : ℕ) : oddPart n = n.divMaxPow 2 := by
  rw [oddPart, Nat.factorization_def _ Nat.prime_two]
  exact Nat.div_eq_of_eq_mul_right (by positivity) (Nat.pow_multiplicity_mul_divMaxPow 2 n).symm

lemma four_mod (k : ℕ) : 1 ≡ 4 ^ k [MOD 3] := by
  simpa using (show 1 ≡ 4 [MOD 3] by decide).pow k

lemma exponent_even (r : ℕ) (h : 3 ∣ 2 ^ r - 1) : ∃ k, r = 2 * k := by
  refine ⟨r / 2, ?_⟩
  by_contra hn
  have hr : r = 2 * (r / 2) + 1 := by omega
  rw [hr, pow_succ, pow_mul] at h
  have hp : 1 ≡ 4 ^ (r / 2) * 2 [MOD 3] := Nat.modEq_of_dvd' (Nat.succ_le_of_lt (by positivity)) h
  exact (by decide : ¬ (1 ≡ 2 [MOD 3])) (hp.trans (by simpa using ((four_mod (r / 2)).mul_right 2).symm))

lemma two_pow_sub (j r : ℕ) : 2 ^ (j + r) - 2 ^ j = 2 ^ j * (2 ^ r - 1) := by
  rw [pow_add, Nat.mul_sub_left_distrib, mul_one]

end OMA.A181666

open OMA.S_oeis_a181666 OMA.A181666 in
theorem OMA.solution : type_of% @OMA.S_oeis_a181666.main := by
  intro m
  constructor
  · rintro ⟨hm, k, hk⟩
    let j := m.factorization 2
    have h : 2 ^ j * ((4 ^ k - 1) / 3) = m := by
      rw [← hk, oddPart_eq, show j = multiplicity 2 m from Nat.factorization_def _ Nat.prime_two]
      exact Nat.pow_multiplicity_mul_divMaxPow 2 m
    refine ⟨3 * m, ⟨j + 2 * k, j, by omega, ?_⟩, by omega, dvd_mul_right .., by omega⟩
    rw [two_pow_sub, pow_mul, show (2 : ℕ)^2 = 4 by decide, ← h, mul_left_comm, Nat.mul_div_cancel' (four_mod k).dvd']
  · rintro ⟨x, ⟨i, j, hij, rfl⟩, hx, hd, hm⟩
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [two_pow_sub] at hx hd hm
    have hn : ¬ 3 ∣ 2 ^ j := fun h => (by decide : ¬ 3 ∣ (2 : ℕ)) (Nat.prime_three.dvd_of_dvd_pow h)
    obtain ⟨k, rfl⟩ := exponent_even r ((Nat.prime_three.dvd_mul.mp hd).resolve_left hn)
    rw [pow_mul, show (2 : ℕ)^2 = 4 by decide] at hx hm
    rw [Nat.mul_div_assoc _ (four_mod k).dvd'] at hm
    subst m
    have ho : ¬ 2 ∣ (4 ^ k - 1) / 3 := by
      intro h
      have h' := h.trans (Nat.div_dvd_of_dvd (four_mod k).dvd')
      cases k with
      | zero => simp at hx
      | succ t =>
        rw [pow_succ, Nat.dvd_iff_mod_eq_zero] at h'
        have : 0 < 4 ^ t := by positivity
        omega
    refine ⟨Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero fun h => ho (h ▸ dvd_zero _)), k, ?_⟩
    rw [oddPart_eq, Nat.divMaxPow_base_pow_mul (by decide)]
    exact congrArg Prod.snd (Nat.maxPowDvdDiv_of_not_dvd ho)
