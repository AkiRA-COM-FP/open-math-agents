import OMAStatements.S_oeis_a064708

-- Reduction oeis-a064708.R1 of A064708: Initial term of run of (at least) n consecutive numbers with just 2 distinct prime factors.
-- Credit: @EmadY
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea. In a run of nine consecutive numbers with exactly two distinct prime factors, every multiple
-- of 6 is a 3-smooth number 2^a 3^b. If the run contains two multiples of 6, they are 3-smooth and
-- 6 apart, which (Catalan for powers of 2 and 3) forces a run starting below 49: impossible, proved here.
-- Otherwise the unique multiple of 6, N = 2^a 3^b, is at offset 3, 4 or 5 of the run: windows
-- N-3..N+5 (H2), N-4..N+4 (H1, centered) and N-5..N+3 (H3).
-- H1 should follow from a mod 5 argument (some N+i with i in {2,3,4} or {-2,-3,-4} is 2^k 5^e or
-- 3^k 5^e) plus LTE bounds. H2 and H3 are the open core: with u = N/12 they need 4u-1, 4u+1, 6u-1,
-- 6u+1 and 3u+1 (H2) or 3u-1 (H3) all to be prime powers.

namespace OMA.R_oeis_a064708_R1


def H1 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 4 + i).primeFactors.card = 2

def H2 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 3 + i).primeFactors.card = 2

def H3 : Prop := ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
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

lemma two_mult_case (m r : ℕ) (hr : r ≤ 2) (h6 : 6 ∣ m + r)
    (hm : ∀ i < 9, (m + i).primeFactors.card = 2) : False := by
  obtain ⟨a, b, ha, hb, hab⟩ := smooth_of_six_dvd h6 (hm r (by omega))
  obtain ⟨c, d, hc, hd, hcd⟩ := smooth_of_six_dvd (by omega : 6 ∣ m + (r + 6)) (hm (r + 6) (by omega))
  have := small_of_two_mult ha hb hc hd (by rw [← hab, ← hcd]; ring)
  exact small_window m (by omega) hm

theorem reduce_core (h1 : H1) (h2 : H2) (h3 : H3) :
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
  · exact cen 5 h3 (by norm_num) (by omega)
  · exact cen 4 h1 (by norm_num) (by omega)
  · exact cen 3 h2 (by norm_num) (by omega)
  · exact two_mult_case m 2 (by norm_num) (by omega) hm
  · exact two_mult_case m 1 (by norm_num) (by omega) hm

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a064708.main :=
  fun h1 h2 h3 => reduce_core h1 h2 h3

end OMA.R_oeis_a064708_R1
