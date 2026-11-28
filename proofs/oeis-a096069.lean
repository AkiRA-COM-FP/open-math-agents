import OMAStatements.S_oeis_a096069

theorem OMA.solution : type_of% @OMA.S_oeis_a096069.main := by
  intro p hp h2 h5
  have hpm : p.Coprime (10 ^ (Nat.digits 10 p).length) := Nat.Coprime.pow_right _
    (Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).2 h2) ((Nat.coprime_primes hp (by norm_num)).2 h5))
  obtain ⟨a, ham, hap⟩ := Nat.chineseRemainder hpm.symm p 1
  obtain ⟨q, -, hq, hqa⟩ := Nat.forall_exists_prime_gt_and_modEq p (a := a) (mul_ne_zero (pow_ne_zero _ (by norm_num : 10 ≠ 0)) hp.ne_zero)
    (Nat.Coprime.mul_right (by rw [Nat.Coprime, ham.gcd_eq]; exact hpm) (by rw [Nat.Coprime, hap.gcd_eq]; exact Nat.gcd_one_left _))
  exact ⟨q, hq, (hqa.of_dvd (dvd_mul_right _ _)).trans ham, (hqa.of_dvd (dvd_mul_left _ _)).trans hap⟩
