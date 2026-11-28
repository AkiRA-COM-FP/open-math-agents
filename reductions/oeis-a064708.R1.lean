import OMAStatements.S_oeis_a064708

-- Reduction oeis-a064708.R1 of A064708: Initial term of run of (at least) n consecutive numbers with just 2 distinct prime factors.
-- Credit: @EmadY
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea. In a run of nine consecutive numbers with exactly two distinct prime factors, every multiple
-- of 6 is a 3-smooth number N = 2^a 3^b. Proved here:
-- * two multiples of 6 in the run: they are 3-smooth and 6 apart, so (Catalan for powers of 2 and 3)
--   the run starts below 49, where it always meets 0, 1 or a prime;
-- * one multiple of 6 in the middle (window N-4..N+4): 5 divides one of N+4, N-2, N+2, N-4, which is
--   then 2^k 5^e. The exponential equations that come out (5^e -+ 1 and 3^b -+ 1, 3^b -+ 2 against
--   powers of 2, 3, 5) are solved by congruences (moduli 7, 9, 11, 13, 16, 25, 32, 41, 81, 109, 1181),
--   leaving ten explicit windows that each contain a prime or 322 = 2*7*23.
-- Left open: the multiple of 6 at offset 3 (H1, window N-3..N+5) or offset 5 (H2, window N-5..N+3).
-- With u = N/12 these need 4u-1, 4u+1, 6u-1, 6u+1 and 3u+1 (H1) or 3u-1 (H2) all to be prime powers.

namespace OMA.R_oeis_a064708_R1


def H1 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 3 + i).primeFactors.card = 2

def H2 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2

lemma smooth_of_six_dvd {n : ℕ} (h6 : 6 ∣ n) (hc : n.primeFactors.card = 2) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ n = 2 ^ a * 3 ^ b := by
  have hn : n ≠ 0 := by rintro rfl; simp at hc
  have d2 : 2 ∣ n := dvd_trans (by norm_num) h6
  have d3 : 3 ∣ n := dvd_trans (by norm_num) h6
  have h2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, d2, hn⟩
  have h3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_three, d3, hn⟩
  have hpf : n.primeFactors = {2, 3} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [hc]; rfl
  refine ⟨n.factorization 2, n.factorization 3,
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).1 d2,
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hn).1 d3, ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, hpf]
  simp

lemma three_pow_mod_eight (t : ℕ) : 3 ^ t % 8 = 1 ∨ 3 ^ t % 8 = 3 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- `3^t + 1` is a power of two only for `t ≤ 1`. -/
lemma catalan_a {s t : ℕ} (h : 3 ^ t + 1 = 2 ^ s) : t ≤ 1 := by
  by_contra ht
  push Not at ht
  have h9 : 9 ≤ 3 ^ t := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hs : 3 ≤ s := by
    by_contra hs
    push Not at hs
    have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ∣ 2 ^ s := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    exact ⟨2 ^ k, by rw [pow_add]; norm_num⟩
  have hm := three_pow_mod_eight t
  generalize 3 ^ t = x at *
  generalize 2 ^ s = y at *
  omega

lemma two_pow_mod_period (s M : ℕ) (hM : 2 ^ 18 % M = 1) : 2 ^ s % M = 2 ^ (s % 18) % M := by
  conv_lhs => rw [← Nat.div_add_mod s 18, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (2 ^ 18), hM, one_pow]
  have hM2 : M ≠ 1 := by rintro rfl; norm_num at hM
  rw [Nat.one_mod_eq_one.mpr hM2, one_mul, Nat.mod_mod]

/-- `2^s + 1` is a power of three only for `t ≤ 2`. -/
lemma catalan_b {s t : ℕ} (h : 2 ^ s + 1 = 3 ^ t) : t ≤ 2 := by
  by_contra ht
  push Not at ht
  have h27 : 27 ∣ 2 ^ s + 1 := by
    rw [h]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact ⟨3 ^ k, by rw [pow_add]; norm_num⟩
  have p27 := two_pow_mod_period s 27 (by norm_num)
  have p19 := two_pow_mod_period s 19 (by norm_num)
  have hr : s % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have h19 : 19 ∣ 2 ^ s + 1 := by
    generalize hr' : s % 18 = r at p27 p19 hr
    interval_cases r <;> norm_num at p27 p19 <;> omega
  rw [h] at h19
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 19) h19)
  norm_num at this

/-- Two `3`-smooth multiples of `6` that are `6` apart are small. -/
lemma small_of_two_mult {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 2 ^ a * 3 ^ b + 6 = 2 ^ c * 3 ^ d) : 2 ^ a * 3 ^ b ≤ 48 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have e : 2 ^ a * 3 ^ b + 1 = 2 ^ c * 3 ^ d := by
    have : 6 * (2 ^ a * 3 ^ b + 1) = 6 * (2 ^ c * 3 ^ d) := by
      rw [pow_succ, pow_succ, pow_succ, pow_succ] at h; linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rw [pow_succ, pow_succ]
  -- parity and divisibility by 3 force a = 0 or c = 0, and b = 0 or d = 0
  have hac : a = 0 ∨ c = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (dvd_pow_self 2 hh.1) _
    have h2 : 2 ∣ 2 ^ c * 3 ^ d := Dvd.dvd.mul_right (dvd_pow_self 2 hh.2) _
    omega
  have hbd : b = 0 ∨ d = 0 := by
    by_contra hh
    push Not at hh
    have h1 : 3 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_left (dvd_pow_self 3 hh.1) _
    have h2 : 3 ∣ 2 ^ c * 3 ^ d := Dvd.dvd.mul_left (dvd_pow_self 3 hh.2) _
    omega
  rcases hac with rfl | rfl <;> rcases hbd with rfl | rfl
  · simp
  · simp at e
    have := catalan_a e
    interval_cases b <;> simp
  · simp at e
    have := catalan_b e
    have : 2 ^ a ≤ 8 := by
      have : 3 ^ d ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    simp; omega
  · simp at e

lemma card_ne_two_of_prime {p : ℕ} (hp : p.Prime) : p.primeFactors.card ≠ 2 := by
  rw [hp.primeFactors]; simp

lemma not_prime_of_card_two {n : ℕ} (h : n.primeFactors.card = 2) : ¬ n.Prime :=
  fun hp => card_ne_two_of_prime hp h

/-- Every run of nine consecutive numbers starting at most at `48` contains `0`, `1` or a prime. -/
lemma small_window (m : ℕ) (hm : m ≤ 48) : ¬ ∀ i < 9, (m + i).primeFactors.card = 2 := by
  intro h
  interval_cases m <;>
  first
  | (have h0 := h 0 (by norm_num); simp at h0; done)
  | (have hp := not_prime_of_card_two (h 0 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 1 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 2 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 3 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 4 (by norm_num)); norm_num at hp; done)
  | (have hp := not_prime_of_card_two (h 5 (by norm_num)); norm_num at hp; done)

lemma pow_mod_period (x P M n : ℕ) (h : x ^ P % M = 1) : x ^ n % M = x ^ (n % P) % M := by
  conv_lhs => rw [← Nat.div_add_mod n P, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (x ^ P), h, one_pow]
  have hM : M ≠ 1 := by intro hM1; rw [hM1, Nat.mod_one] at h; exact zero_ne_one h
  rw [Nat.one_mod_eq_one.mpr hM, one_mul, Nat.mod_mod]

lemma not_dvd_23 {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) (x y : ℕ) :
    ¬ q ∣ 2 ^ x * 3 ^ y := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h))

lemma not_dvd_25 {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h5 : q ≠ 5) (x y : ℕ) :
    ¬ q ∣ 2 ^ x * 5 ^ y := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (hq.dvd_of_dvd_pow h))

lemma five_pow_mod_four (e : ℕ) : 5 ^ e % 4 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- `2^x 3^y + 1 = 5^e` forces `x ≤ 3` and `y ≤ 1`. -/
lemma eqA {x y e : ℕ} (h : 2 ^ x * 3 ^ y + 1 = 5 ^ e) : x ≤ 3 ∧ y ≤ 1 := by
  constructor
  · by_contra hx
    have h16 : 16 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 2 (by omega : 4 ≤ x)
      exact Dvd.dvd.mul_right (by simpa using this) _
    have m16 : 5 ^ e % 16 = 1 := by omega
    rw [pow_mod_period 5 4 16 e (by norm_num)] at m16
    have he : e % 4 = 0 := by
      have : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 4) <;> simp_all
    have m13 : 5 ^ e % 13 = 1 := by rw [pow_mod_period 5 4 13 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 13) (by norm_num) (by norm_num) (by norm_num) x y (by omega)
  · by_contra hy
    have h9 : 9 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 3 (by omega : 2 ≤ y)
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m9 : 5 ^ e % 9 = 1 := by omega
    rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
    have he : e % 6 = 0 := by
      have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 6) <;> simp_all
    have m7 : 5 ^ e % 7 = 1 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 7) (by norm_num) (by norm_num) (by norm_num) x y (by omega)

/-- `5^e + 1 = 2^x 3^y` forces `x ≤ 1` and `y ≤ 1`. -/
lemma eqB {x y e : ℕ} (h : 5 ^ e + 1 = 2 ^ x * 3 ^ y) : x ≤ 1 ∧ y ≤ 1 := by
  have m4 := five_pow_mod_four e
  constructor
  · by_contra hx
    have : 4 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 2 (by omega : 2 ≤ x)
      exact Dvd.dvd.mul_right (by simpa using this) _
    omega
  · by_contra hy
    have h9 : 9 ∣ 2 ^ x * 3 ^ y := by
      have := pow_dvd_pow 3 (by omega : 2 ≤ y)
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m9 : 5 ^ e % 9 = 8 := by omega
    rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
    have he : e % 6 = 3 := by
      have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
      interval_cases (e % 6) <;> simp_all
    have m7 : 5 ^ e % 7 = 6 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
    exact not_dvd_23 (q := 7) (by norm_num) (by norm_num) (by norm_num) x y (by omega)

/-- `3^b + 1 = 2^j 5^e` with `e ≥ 1` forces `b ≤ 2`. -/
lemma eqC {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b + 1 = 2 ^ j * 5 ^ e) : b ≤ 2 := by
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · obtain rfl : e = 1 := by omega
    rw [pow_one] at h
    have hj : j ≤ 2 := by
      by_contra hj
      have : 8 ∣ 2 ^ j := by
        have := pow_dvd_pow 2 (by omega : 3 ≤ j)
        simpa using this
      have := three_pow_mod_eight b
      omega
    have h4 : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj
    by_contra hb
    have : 3 ^ 3 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h4 this
    omega
  · have h25 : 25 ∣ 2 ^ j * 5 ^ e := by
      have := pow_dvd_pow 5 he2
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m25 : 3 ^ b % 25 = 24 := by omega
    rw [pow_mod_period 3 20 25 b (by norm_num)] at m25
    have hb : b % 20 = 10 := by
      have : b % 20 < 20 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 20) <;> simp_all
    have m : 3 ^ b % 1181 = 1180 := by
      rw [pow_mod_period 3 20 1181 b (by norm_num), hb]; norm_num
    exact absurd (by omega : 1181 ∣ 2 ^ j * 5 ^ e)
      (not_dvd_25 (q := 1181) (by norm_num) (by norm_num) (by norm_num) j e)

/-- `3^b = 2^j 5^e + 1` with `e ≥ 1` forces `b ≤ 4`. -/
lemma eqD {b j e : ℕ} (he : 1 ≤ e) (h : 3 ^ b = 2 ^ j * 5 ^ e + 1) : b ≤ 4 := by
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · obtain rfl : e = 1 := by omega
    rw [pow_one] at h
    have m5 : 3 ^ b % 5 = 1 := by omega
    rw [pow_mod_period 3 4 5 b (by norm_num)] at m5
    have hb4 : b % 4 = 0 := by
      have : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 4) <;> simp_all
    rcases (show b % 8 = 0 ∨ b % 8 = 4 by omega) with hb8 | hb8
    · have m : 3 ^ b % 41 = 1 := by
        rw [pow_mod_period 3 8 41 b (by norm_num), hb8]; norm_num
      exact absurd (by rw [pow_one]; omega : 41 ∣ 2 ^ j * 5 ^ 1)
        (not_dvd_25 (q := 41) (by norm_num) (by norm_num) (by norm_num) j 1)
    · have m : 3 ^ b % 32 = 17 := by
        rw [pow_mod_period 3 8 32 b (by norm_num), hb8]; norm_num
      have hj : j = 4 := by
        rcases Nat.lt_or_ge j 5 with hj | hj
        · interval_cases j <;> omega
        · have : 32 ∣ 2 ^ j := by
            have := pow_dvd_pow 2 hj
            simpa using this
          omega
      subst hj
      have h81 : 3 ^ b = 3 ^ 4 := by omega
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h81).le
  · have h25 : 25 ∣ 2 ^ j * 5 ^ e := by
      have := pow_dvd_pow 5 he2
      exact Dvd.dvd.mul_left (by simpa using this) _
    have m25 : 3 ^ b % 25 = 1 := by omega
    rw [pow_mod_period 3 20 25 b (by norm_num)] at m25
    have hb : b % 20 = 0 := by
      have : b % 20 < 20 := Nat.mod_lt _ (by norm_num)
      interval_cases (b % 20) <;> simp_all
    have m : 3 ^ b % 11 = 1 := by
      rw [pow_mod_period 3 20 11 b (by norm_num), hb]; norm_num
    exact absurd (by omega : 11 ∣ 2 ^ j * 5 ^ e)
      (not_dvd_25 (q := 11) (by norm_num) (by norm_num) (by norm_num) j e)

/-- `3^b + 2 = 5^e` forces `b ≤ 1`. -/
lemma eqF {b e : ℕ} (h : 3 ^ b + 2 = 5 ^ e) : b ≤ 1 := by
  by_contra hb
  have h9 : 9 ∣ 3 ^ b := by
    have := pow_dvd_pow 3 (by omega : 2 ≤ b)
    simpa using this
  have m9 : 5 ^ e % 9 = 2 := by omega
  rw [pow_mod_period 5 6 9 e (by norm_num)] at m9
  have he : e % 6 = 5 := by
    have : e % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases (e % 6) <;> simp_all
  have m7 : 5 ^ e % 7 = 3 := by rw [pow_mod_period 5 6 7 e (by norm_num), he]; norm_num
  have m4 := five_pow_mod_four e
  have a7 : 3 ^ b % 7 = 1 := by omega
  have a4 : 3 ^ b % 4 = 3 := by omega
  rw [pow_mod_period 3 6 7 b (by norm_num)] at a7
  rw [pow_mod_period 3 2 4 b (by norm_num)] at a4
  have h6 : b % 6 = 0 := by
    have : b % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases (b % 6) <;> simp_all
  have h2 : b % 2 = 1 := by
    have : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases (b % 2) <;> simp_all
  omega

/-- `3^b = 5^e + 2` forces `b ≤ 3`. -/
lemma eqG {b e : ℕ} (h : 3 ^ b = 5 ^ e + 2) : b ≤ 3 := by
  by_contra hb
  have h81 : 81 ∣ 3 ^ b := by
    have := pow_dvd_pow 3 (by omega : 4 ≤ b)
    simpa using this
  have m81 : 5 ^ e % 81 = 79 := by omega
  rw [pow_mod_period 5 54 81 e (by norm_num)] at m81
  have he : e % 54 = 20 := by
    have : e % 54 < 54 := Nat.mod_lt _ (by norm_num)
    interval_cases (e % 54) <;> simp_all
  have m109 : 5 ^ e % 109 = 35 := by
    rw [pow_mod_period 5 54 109 e (by norm_num), he]; norm_num
  have a109 : 3 ^ b % 109 = 37 := by omega
  rw [pow_mod_period 3 27 109 b (by norm_num)] at a109
  have : b % 27 < 27 := Nat.mod_lt _ (by norm_num)
  interval_cases (b % 27) <;> simp_all

lemma two_prime_form {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (dp : p ∣ n)
    (dq : q ∣ n) (hc : n.primeFactors.card = 2) :
    ∃ k e : ℕ, 1 ≤ k ∧ 1 ≤ e ∧ n = p ^ k * q ^ e := by
  have hn : n ≠ 0 := by rintro rfl; simp at hc
  have h2 : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, dp, hn⟩
  have h3 : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, dq, hn⟩
  have hpf : n.primeFactors = {p, q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [hc, Finset.card_pair hpq]
  refine ⟨n.factorization p, n.factorization q,
    (hp.dvd_iff_one_le_factorization hn).1 dp, (hq.dvd_iff_one_le_factorization hn).1 dq, ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, hpf, Finset.prod_pair hpq]

-- 2-adic bookkeeping: Y is the odd part 5^e, X or T the cofactor of N.
lemma adic_p4_a3 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 8 * X + 4 = 2 ^ k * Y) : 2 * X + 1 = Y := by
  rcases k with _ | _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1 + 1) * Y = 8 * (2 ^ k * Y) := by ring
    omega

lemma adic_m4_a3 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 8 * X = 2 ^ k * Y + 4) : 2 * X = Y + 1 := by
  rcases k with _ | _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1 + 1) * Y = 8 * (2 ^ k * Y) := by ring
    omega

lemma adic_p2_a2 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * X + 2 = 2 ^ k * Y) : 2 * X + 1 = Y := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_m2_a2 {X Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * X = 2 ^ k * Y + 2) : 2 * X = Y + 1 := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_p4_a2 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * T + 4 = 2 ^ k * Y) :
    ∃ j, T + 1 = 2 ^ j * Y := by
  rcases k with _ | _ | j
  · simp at h; omega
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1 + 1) * Y = 4 * (2 ^ j * Y) := by ring
    omega

lemma adic_m4_a2 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 4 * T = 2 ^ k * Y + 4) :
    ∃ j, T = 2 ^ j * Y + 1 := by
  rcases k with _ | _ | j
  · simp at h; omega
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1 + 1) * Y = 4 * (2 ^ j * Y) := by ring
    omega

lemma adic_p4_a1 {T Y k : ℕ} (hT : T % 2 = 1) (hY : Y % 2 = 1) (h : 2 * T + 4 = 2 ^ k * Y) :
    T + 2 = Y := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_m4_a1 {T Y k : ℕ} (hT : T % 2 = 1) (hY : Y % 2 = 1) (h : 2 * T = 2 ^ k * Y + 4) :
    T = Y + 2 := by
  rcases k with _ | _ | k
  · simp at h; omega
  · simp at h; omega
  · have : 2 ^ (k + 1 + 1) * Y = 4 * (2 ^ k * Y) := by ring
    omega

lemma adic_p2_a1 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 2 * T + 2 = 2 ^ k * Y) :
    ∃ j, T + 1 = 2 ^ j * Y := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1) * Y = 2 * (2 ^ j * Y) := by ring
    omega

lemma adic_m2_a1 {T Y k : ℕ} (hY : Y % 2 = 1) (h : 2 * T = 2 ^ k * Y + 2) :
    ∃ j, T = 2 ^ j * Y + 1 := by
  rcases k with _ | j
  · simp at h; omega
  · refine ⟨j, ?_⟩
    have : 2 ^ (j + 1) * Y = 2 * (2 ^ j * Y) := by ring
    omega

lemma card_322 : (322 : ℕ).primeFactors.card = 3 := by
  rw [show (322 : ℕ) = 2 * 7 * 23 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- The centered window: no run of nine has its multiple of 6 in the middle. -/
lemma centered : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 4 + i).primeFactors.card = 2 := by
  intro a b ha hb hw
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hN6 : 6 ≤ 2 ^ a * 3 ^ b := by nlinarith
  have w0 := hw 0 (by norm_num)
  have w2 := hw 2 (by norm_num)
  have w6 := hw 6 (by norm_num)
  have w8 := hw 8 (by norm_num)
  rw [show 2 ^ a * 3 ^ b - 4 + 0 = 2 ^ a * 3 ^ b - 4 by omega] at w0
  rw [show 2 ^ a * 3 ^ b - 4 + 2 = 2 ^ a * 3 ^ b - 2 by omega] at w2
  rw [show 2 ^ a * 3 ^ b - 4 + 6 = 2 ^ a * 3 ^ b + 2 by omega] at w6
  rw [show 2 ^ a * 3 ^ b - 4 + 8 = 2 ^ a * 3 ^ b + 4 by omega] at w8
  have n5 : ¬ 5 ∣ 2 ^ a * 3 ^ b := not_dvd_23 (by norm_num) (by norm_num) (by norm_num) a b
  have d2 : 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have hT : 3 ^ b % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have hY : ∀ e : ℕ, 5 ^ e % 2 = 1 := fun e => by rw [Nat.pow_mod]; norm_num
  rcases (show 2 ^ a * 3 ^ b % 5 = 1 ∨ 2 ^ a * 3 ^ b % 5 = 2 ∨ 2 ^ a * 3 ^ b % 5 = 3 ∨
      2 ^ a * 3 ^ b % 5 = 4 by omega) with h5 | h5 | h5 | h5
  · -- 5 divides N + 4
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b + 4) (by omega : 5 ∣ 2 ^ a * 3 ^ b + 4) w8
    rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
    · have := eqF (adic_p4_a1 hT (hY e) (show 2 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by omega))
      interval_cases b
      have hp := not_prime_of_card_two (hw 0 (by norm_num)); norm_num at hp
    · obtain ⟨j, hj⟩ := adic_p4_a2 (hY e) (show 4 * 3 ^ b + 4 = 2 ^ k * 5 ^ e by omega)
      have := eqC he hj
      interval_cases b
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
      have h1 := adic_p4_a3 (hY e) (show 8 * (2 ^ a * 3 ^ b) + 4 = 2 ^ k * 5 ^ e by
        rw [← hke]; ring)
      obtain ⟨hx, hy⟩ := eqA (show 2 ^ (a + 1) * 3 ^ b + 1 = 5 ^ e by rw [← h1]; ring)
      have hx' : a ≤ 2 := by omega
      interval_cases b
      interval_cases a
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
  · -- 5 divides N - 2
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b - 2) (by omega : 5 ∣ 2 ^ a * 3 ^ b - 2) w2
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · obtain ⟨j, hj⟩ := adic_m2_a1 (hY e) (show 2 * 3 ^ b = 2 ^ k * 5 ^ e + 2 by omega)
      have := eqD he hj
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 5 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      have h1 := adic_m2_a2 (hY e) (show 4 * (2 ^ a * 3 ^ b) = 2 ^ k * 5 ^ e + 2 by
        rw [show 4 * (2 ^ a * 3 ^ b) = 2 ^ (a + 2) * 3 ^ b by ring]; omega)
      obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)
      obtain rfl : a = 0 := by omega
      interval_cases b
      have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
  · -- 5 divides N + 2
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b + 2) (by omega : 5 ∣ 2 ^ a * 3 ^ b + 2) w6
    rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · obtain ⟨j, hj⟩ := adic_p2_a1 (hY e) (show 2 * 3 ^ b + 2 = 2 ^ k * 5 ^ e by omega)
      have := eqC he hj
      interval_cases b
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      have h1 := adic_p2_a2 (hY e) (show 4 * (2 ^ a * 3 ^ b) + 2 = 2 ^ k * 5 ^ e by
        rw [← hke]; ring)
      obtain ⟨hx, hy⟩ := eqA (show 2 ^ (a + 1) * 3 ^ b + 1 = 5 ^ e by rw [← h1]; ring)
      have hx' : a ≤ 2 := by omega
      interval_cases b
      interval_cases a
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
  · -- 5 divides N - 4
    obtain ⟨k, e, -, he, hke⟩ := two_prime_form Nat.prime_two p5 (by norm_num)
      (by omega : 2 ∣ 2 ^ a * 3 ^ b - 4) (by omega : 5 ∣ 2 ^ a * 3 ^ b - 4) w0
    rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
    · have := eqG (adic_m4_a1 hT (hY e) (show 2 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega))
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp
    · obtain ⟨j, hj⟩ := adic_m4_a2 (hY e) (show 4 * 3 ^ b = 2 ^ k * 5 ^ e + 4 by omega)
      have := eqD he hj
      interval_cases b
      · norm_num at h5
      · norm_num at h5
      · norm_num at h5
      · have h' := hw 2 (by norm_num); norm_num [card_322] at h'
    · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 3 := ⟨a - 3, by omega⟩
      have h1 := adic_m4_a3 (hY e) (show 8 * (2 ^ a * 3 ^ b) = 2 ^ k * 5 ^ e + 4 by
        rw [show 8 * (2 ^ a * 3 ^ b) = 2 ^ (a + 3) * 3 ^ b by ring]; omega)
      obtain ⟨hx, hy⟩ := eqB (show 5 ^ e + 1 = 2 ^ (a + 1) * 3 ^ b by rw [← h1]; ring)
      obtain rfl : a = 0 := by omega
      interval_cases b
      have hp := not_prime_of_card_two (hw 3 (by norm_num)); norm_num at hp

lemma two_mult_case (m r : ℕ) (hr : r ≤ 2) (h6 : 6 ∣ m + r)
    (hm : ∀ i < 9, (m + i).primeFactors.card = 2) : False := by
  obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_six_dvd h6 (hm r (by omega))
  obtain ⟨c, d, hc, hd, hcd⟩ := smooth_of_six_dvd (by omega : 6 ∣ m + (r + 6)) (hm (r + 6) (by omega))
  have := small_of_two_mult ha hb hc hd (by rw [← hab, ← hcd]; ring)
  exact small_window m (by omega) hm

theorem reduce_core (h1 : H1) (h2 : H2) :
    ¬ ∃ m : ℕ, ∀ i < 9, (m + i).primeFactors.card = 2 := by
  rintro ⟨m, hm⟩
  have hmod : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have cen : ∀ (k : ℕ) (H : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬ ∀ i < 9, (2 ^ a * 3 ^ b - k + i).primeFactors.card = 2), k < 9 → 6 ∣ m + k → False := by
    intro k H hk h6
    obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_six_dvd h6 (hm k hk)
    apply H a b ha hb
    rw [← hab, Nat.add_sub_cancel]
    exact hm
  interval_cases hr : m % 6
  · exact two_mult_case m 0 (by norm_num) (by omega) hm
  · exact cen 5 h2 (by norm_num) (by omega)
  · exact cen 4 centered (by norm_num) (by omega)
  · exact cen 3 h1 (by norm_num) (by omega)
  · exact two_mult_case m 2 (by norm_num) (by omega) hm
  · exact two_mult_case m 1 (by norm_num) (by omega) hm

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a064708.main :=
  fun h1 h2 => reduce_core h1 h2

end OMA.R_oeis_a064708_R1
