import OMAStatements.S_oeis_a189045

-- Problem: A189045: Semiprimes which are sub-perfect powers.
-- Upstream: formal-conjectures statements/oeis-a189045.lean:0 (declaration OMA.S_oeis_a189045.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: suppose p*p + 1 = m^k with p prime and k >= 2. Then m - 1 divides m^k - 1 = p^2,
-- so m - 1 is 1, p or p^2. If m - 1 = p or p^2, then m^2 > p*p + 1 = m^k >= m^2, impossible.
-- If m = 2, then 4 divides 2^k = p*p + 1, but a square is 0 or 1 modulo 4.

open OMA.S_oeis_a189045 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189045.main := by
  intro n p q hn hp _ hpq hEq
  rw [← hEq] at hpq
  have hn' : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∧
      ∃ m k : ℕ, 2 ≤ k ∧ n + 1 = m ^ k := hn
  obtain ⟨-, m, k, hk, hmk⟩ := hn'
  rw [hpq] at hmk
  have hp2 := hp.two_le
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_pow (show k ≠ 0 by omega)] at hmk
    omega
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hdvd : m - 1 ∣ p ^ 2 := by
    have h := Nat.sub_one_dvd_pow_sub_one m k
    have h2 : m ^ k - 1 = p * p := by omega
    rw [h2, ← sq] at h
    exact h
  obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hmk2 : m ^ 2 ≤ m ^ k := Nat.pow_le_pow_right (by omega) hk
  interval_cases i
  · rw [pow_zero] at hmi
    have hm2 : m = 2 := by omega
    subst hm2
    have h4 : 2 ^ k % 4 = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
      rw [pow_add]
      norm_num
    have hmod := Nat.mul_mod p p 4
    have hp4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r, r = p % 4 := ⟨_, rfl⟩
    rw [← hr] at hmod hp4
    interval_cases r
    · omega
    · omega
    · omega
    · omega
  · rw [pow_one] at hmi
    have hm : m = p + 1 := by omega
    subst hm
    rw [sq] at hmk2
    nlinarith
  · rw [sq] at hmi
    have hm : m = p * p + 1 := by omega
    have hmm : m ^ k = m := by omega
    rw [hmm, sq] at hmk2
    have hpp : 2 * 2 ≤ p * p := Nat.mul_le_mul hp2 hp2
    have h5 : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    omega
