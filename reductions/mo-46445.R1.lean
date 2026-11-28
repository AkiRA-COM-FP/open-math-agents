import OMAStatements.S_mo_46445

/-!
Two consecutive unit intervals cannot both contain zeros when the finite cotangent sum has no
pole at their shared endpoint and its summation range is constant across both intervals.
Prime pairs and prime squares supply the pole-free endpoints in the arithmetic hypothesis.
-/

namespace OMA.R_mo_46445_R1

open Real Set

/-- Arbitrarily large primes followed two steps later by a prime or a prime square. -/
def H1 : Prop :=
  ∀ B : ℕ, ∃ k ≥ B, k.Prime ∧ ((k + 2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k + 2 = p ^ 2)

/-- Strict decrease of a shifted cotangent on an interval with no poles. -/
def H2 : Prop :=
  ∀ a b c t : ℝ, 0 < t → (∀ x ∈ Ioo a b, sin ((x + c) * t) ≠ 0) →
    StrictAntiOn (fun x => cot ((x + c) * t)) (Ioo a b)

lemma floor_sqrt_center {k : ℕ} (hk : k.sqrt ^ 2 < k) {x : ℝ}
    (hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) : ⌊sqrt x⌋₊ = k.sqrt := by
  have hlo : ((k.sqrt : ℝ) ^ 2) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show k.sqrt ^ 2 + 1 ≤ k by omega)
  have hhi : (k : ℝ) + 1 ≤ ((k.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' k)
  refine (Nat.floor_eq_iff (sqrt_nonneg x)).mpr ⟨?_, ?_⟩
  · rw [← sqrt_sq (Nat.cast_nonneg k.sqrt)]
    exact sqrt_le_sqrt (by linarith only [hx.1, hlo])
  · exact (sqrt_lt' (by positivity)).mpr (hx.2.trans_le hhi)

private lemma sine_ne_center {k n c : ℕ} (hn : 0 < n) (hnd : ¬ n ∣ k + c)
    {x : ℝ} (hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) :
    sin ((x + (c : ℝ)) * (π / n)) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := sin_eq_zero_iff.mp h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_div_assoc] at hz
  have hmul := (eq_div_iff hnR).mp hz
  have he : (z : ℝ) * (n : ℝ) = x + (c : ℝ) := by
    apply mul_right_cancel₀ pi_ne_zero
    linear_combination hmul
  have hlo : (k : ℤ) + (c : ℤ) - 1 < z * (n : ℤ) := by
    exact_mod_cast (show (k : ℝ) + (c : ℝ) - 1 < (z : ℝ) * (n : ℝ) from
      by linarith only [hx.1, he])
  have hhi : z * (n : ℤ) < (k : ℤ) + (c : ℤ) + 1 := by
    exact_mod_cast (show (z : ℝ) * (n : ℝ) < (k : ℝ) + (c : ℝ) + 1 from
      by linarith only [hx.2, he])
  have hint : z * (n : ℤ) = (k : ℤ) + (c : ℤ) := by omega
  apply hnd
  exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hint.symm⟩

private lemma no_small_divisor {k : ℕ} (hk : k.Prime)
    (hk2 : (k + 2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k + 2 = p ^ 2) {n : ℕ}
    (hn : n ∈ Finset.Icc 2 k.sqrt) : (¬ n ∣ k) ∧ (¬ n ∣ k + 2) := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnle⟩
  have hnk : n < k := hnle.trans_lt (Nat.sqrt_lt_self hk.one_lt)
  refine ⟨fun hd => hnk.ne ((Nat.dvd_prime_two_le hk hn2).mp hd), ?_⟩
  intro hd
  rcases hk2 with hprime | ⟨p, hp, hsq⟩
  · exact (show n < k + 2 by omega).ne ((Nat.dvd_prime_two_le hprime hn2).mp hd)
  · have hnp : n < p := hnle.trans_lt (Nat.sqrt_lt'.mpr (by omega : k < p ^ 2))
    rw [hsq] at hd
    obtain ⟨e, he, heq⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hpos : 1 ≤ e := by
      by_contra! h
      have he0 : e = 0 := by omega
      simp [he0] at heq
      omega
    have hle : p ≤ n := by
      rw [heq]
      simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le hpos)
    exact hnp.not_ge hle

private lemma sum_strictAnti (hcot : H2) {k : ℕ} (hk4 : 4 ≤ k) (hsq : k.sqrt ^ 2 < k)
    (hnp : ∀ n ∈ Finset.Icc 2 k.sqrt, (¬ n ∣ k) ∧ (¬ n ∣ k + 2)) :
    StrictAntiOn OMA.S_mo_46445.h (Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) := by
  intro x hx y hy hxy
  unfold OMA.S_mo_46445.h
  rw [floor_sqrt_center hsq hx, floor_sqrt_center hsq hy]
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_sqrt'.mpr (by simpa using hk4)⟩⟩
  · intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hn).1
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have ht : 0 < π / (n : ℝ) := div_pos pi_pos hnR
    have h0 := hcot ((k : ℝ) - 1) ((k : ℝ) + 1) 0 (π / n) ht
      (fun z hz => by simpa using sine_ne_center (c := 0) hn0 (by simpa using (hnp n hn).1) hz)
      hx hy hxy
    have h2 := hcot ((k : ℝ) - 1) ((k : ℝ) + 1) 2 (π / n) ht
      (fun z hz => by simpa using sine_ne_center (c := 2) hn0 (hnp n hn).2 hz)
      hx hy hxy
    simpa only [add_zero, mul_div_assoc] using div_lt_div_of_pos_right (add_lt_add h0 h2) hnR

theorem main : H1 → H2 → type_of% @OMA.S_mo_46445.main := by
  intro centers cotAnti
  rintro ⟨N, hN⟩
  obtain ⟨k, hk, hp, hp2⟩ := centers (max 4 (N + 1))
  have hk4 : 4 ≤ k := (le_max_left _ _).trans hk
  have hkN : N + 1 ≤ k := (le_max_right _ _).trans hk
  have hsq : k.sqrt ^ 2 < k := by
    refine lt_of_le_of_ne (Nat.sqrt_le' k) ?_
    intro he
    exact (Nat.prime_iff.mp hp).not_isSquare ⟨k.sqrt, by simpa [pow_two] using he.symm⟩
  have anti := sum_strictAnti cotAnti hk4 hsq (fun _ hn => no_small_divisor hp hp2 hn)
  obtain ⟨x, hxl, hxu, hx0⟩ := hN (k - 1) (by omega)
  obtain ⟨y, hyl, hyu, hy0⟩ := hN k (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hxl hxu
  have hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := ⟨hxl, by linarith only [hxu]⟩
  have hy : y ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := ⟨by linarith only [hyl], hyu⟩
  have hxy : x < y := by linarith only [hxu, hyl]
  have hlt := anti hx hy hxy
  rw [hx0, hy0] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

end OMA.R_mo_46445_R1
