import OMAReductions.R_oeis_a000215_R1

-- Reduction oeis-a000215.R1.H3.R1 of step oeis-a000215.R1.H3
-- Credit: @thepigeonslastflight

namespace OMA.R_oeis_a000215_R1_H3_R1
open OMA.R_oeis_a000215_R1

/-- The case x = 4t with t odd (x ≡ 4 mod 8), using only the factor x² + 1 = 16t² + 1.
    Python finds no odd t > 1 with 16t² + 1 ∣ 2^(4t) - 1 for 4t < 10^8. -/
def H1 : Prop := ∀ t : ℕ, Odd t → 1 < t → ¬ (16 * t ^ 2 + 1 ∣ 2 ^ (4 * t) - 1)

/-- The case 8 ∣ x. The hypotheses of H3 about 4p^k, 12p^k, 4p^a r, 36·11^k, 36·71^k and
    x % 8 = 4 are automatic or vacuous here. The family x = 8 p^k is now fully excluded:
    R1 left p = 3, k = 3 mod 4 open, and `eight_three_fails` below closes it modulo 9.
    In the family x = 16 p^k, `sixteen_prime_power` leaves six primes, each in one or two
    classes of k. -/
def H2 : Prop := ∀ x : ℕ, 4 < x → 8 ∣ x → ¬ (x - 1).Prime →
    (¬ ∃ s : ℕ, x = 2 ^ s) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x ≠ 8 * p ^ k) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 → x = 16 * p ^ k →
      (p = 3 ∧ (k % 4 = 0 ∨ k % 16 = 8 ∨ k % 256 = 64)) ∨ (p = 13 ∧ k % 4 = 2) ∨
      (p = 43 ∧ (k % 8 = 4 ∨ k % 256 = 192)) ∨ (p = 193 ∧ k % 8 = 2) ∨
      (p = 241 ∧ k % 4 = 1) ∨ (p = 643 ∧ k % 16 = 4)) →
    (∀ m : ℕ, m ∣ x ^ 2 + 1 → m < 2 ^ (m.primeFactors.lcm fun q => x.gcd (q - 1))) →
    ¬ (x ^ 4 - 1 ∣ 2 ^ x - 1)

lemma sq_dvd_of_order (o t p k : ℕ) (hp : p.Prime)
    (h1 : o ∣ t * p * p ^ k) (h2 : ¬ o ∣ t * p) : p ^ 2 ∣ o := by
  by_contra hno
  have ho : o ≠ 0 := by
    rintro rfl
    apply h2
    have h := zero_dvd_iff.mp h1
    exact zero_dvd_iff.mpr ((mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hp.ne_zero))
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.ne_one
  have ha : a ≤ 1 := by
    by_contra! ha
    exact hno (dvd_mul_of_dvd_left (pow_dvd_pow p ha) m)
  have cop : m.Coprime (p ^ (k + 1)) :=
    Nat.Coprime.pow_right (k + 1) (Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hm))
  have h1' : m ∣ t * p ^ (k + 1) := (dvd_mul_left m (p ^ a)).trans (by
    rw [pow_succ, mul_comm (p ^ k) p, ← mul_assoc]; exact h1)
  have mt : m ∣ t := cop.dvd_of_dvd_mul_right h1'
  apply h2
  rw [mul_comm t p]
  exact mul_dvd_mul ((pow_dvd_pow p ha).trans (by simp)) mt

/-- Prime divisors of the geometric sum, other than p, are 1 modulo p^2. -/
lemma geom_prime_sq (t p k q : ℕ) (ht : 0 < t) (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (hd : q ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i) :
    q ≡ 1 [MOD p ^ 2] := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hsum := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hsum
  by_cases hb : (2 : ZMod q) ^ (t * p) = 1
  · simp [hb] at hsum
    have hqp : q ∣ p ^ k := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hsum)
    exact (hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp))).elim
  have hbpow : ((2 : ZMod q) ^ (t * p)) ^ (p ^ k) = 1 := by
    have h := geom_sum_mul ((2 : ZMod q) ^ (t * p)) (p ^ k)
    rw [hsum, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  rw [← pow_mul] at hbpow
  have two0 : (2 : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos ht hp.pos)
      (Nat.pow_pos hp.pos)))] at hbpow
    exact zero_ne_one hbpow
  have od := orderOf_dvd_of_pow_eq_one hbpow
  have nd : ¬ orderOf (2 : ZMod q) ∣ t * p := fun h => hb (orderOf_dvd_iff_pow_eq_one.mp h)
  have sq := sq_dvd_of_order _ t p k hp od nd
  have card := ZMod.orderOf_dvd_card_sub_one two0
  exact ((Nat.modEq_iff_dvd' hq.one_le).mpr (sq.trans card)).symm

lemma geom_divisor_sq (t p k v : ℕ) (ht : 0 < t) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i) : v ≡ 1 [MOD p ^ 2] := by
  induction v using Nat.recOnMul with
  | zero => simp at hn
  | one => rfl
  | prime q hq => exact geom_prime_sq t p k q ht hp hq (by rintro rfl; exact hn dvd_rfl) hd
  | mul a b' ia ib =>
    have da : a ∣ a * b' := dvd_mul_right _ _
    have db : b' ∣ a * b' := dvd_mul_left _ _
    simpa using (ia (fun h => hn (h.trans da)) (da.trans hd)).mul
      (ib (fun h => hn (h.trans db)) (db.trans hd))

/-- A divisor of 2^(t p^(k+1)) - 1 prime to p is, modulo p^2, a divisor of 2^(t p) - 1. -/
lemma small_divisor_sq (t p k v : ℕ) (ht : 0 < t) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ 2 ^ (t * p * p ^ k) - 1) :
    ∃ d : ℕ, d ∣ 2 ^ (t * p) - 1 ∧ d ∣ v ∧ v ≡ d [MOD p ^ 2] := by
  let G := ∑ i ∈ Finset.range (p ^ k), (2 ^ (t * p)) ^ i
  have hG : G * (2 ^ (t * p) - 1) = 2 ^ (t * p * p ^ k) - 1 := by
    rw [pow_mul 2 (t * p) (p ^ k)]
    exact geom_sum_mul_of_one_le Nat.one_le_two_pow _
  obtain ⟨r, d, hr, hdBase, h⟩ :=
    exists_dvd_and_dvd_of_dvd_mul (hG.symm ▸ hd : v ∣ G * (2 ^ (t * p) - 1))
  have dr : r ∣ v := ⟨d, h⟩
  refine ⟨d, hdBase, ⟨r, by rw [h, Nat.mul_comm]⟩, ?_⟩
  have h1 := geom_divisor_sq t p k r ht hp (fun h => hn (h.trans dr)) hr
  simpa only [h, one_mul] using h1.mul_right d

lemma pow_period (a n P q : ℕ) (h : a ^ P ≡ 1 [MOD q]) : a ^ n ≡ a ^ (n % P) [MOD q] := by
  have e : a ^ n = (a ^ P) ^ (n / P) * a ^ (n % P) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [e]
  simpa using (h.pow (n / P)).mul_right (a ^ (n % P))

/-- The class k = 3 mod 4 that R1 left open also fails the test. Modulo 9, x - 1 = 8 * 3^k - 1
    must agree with a divisor of 2^24 - 1 that divides x - 1. Every such divisor that is 8 mod 9
    contains 7, 17 or 241, and none of these divides 8 * 3^k - 1 when k = 3 mod 4. -/
theorem eight_three_fails (k : ℕ) (hk : k ≠ 0) :
    ¬ ((8 * 3 ^ k) ^ 4 - 1 ∣ 2 ^ (8 * 3 ^ k) - 1) := by
  intro test
  have k4 := eight_three_exponent k hk test
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let x := 8 * 3 ^ (j + 1)
  have hx : x = 8 * 3 * 3 ^ j := by dsimp [x]; ring
  have xpos : 0 < x := by positivity
  have x1 : x - 1 ∣ 2 ^ x - 1 := (Nat.sub_one_dvd_pow_sub_one x 4).trans test
  have x1' : x - 1 ∣ 2 ^ (8 * 3 * 3 ^ j) - 1 := by rw [← hx]; exact x1
  have x3 : 3 ∣ x := dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) 8
  have x9 : 9 ∣ x := by
    have : 9 ∣ 3 ^ (j + 1) := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]; exact pow_dvd_pow 3 (by omega)
    exact dvd_mul_of_dvd_right this 8
  have n3 : ¬ 3 ∣ x - 1 := by omega
  obtain ⟨d, hd, dx, cong⟩ :=
    small_divisor_sq 8 3 j (x - 1) (by decide) Nat.prime_three n3 x1'
  have d9 : d % 9 = 8 := by
    have c : (x - 1) % 9 = d % 9 := cong
    omega
  have hd' : d ∣ 7 * (17 * (241 * 585)) := by
    have e : 2 ^ (8 * 3) - 1 = 7 * (17 * (241 * 585)) := by norm_num
    rwa [e] at hd
  have key : 7 ∣ d ∨ 17 ∣ d ∨ 241 ∣ d := by
    by_contra! h
    have c7 : d.Coprime 7 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.1).symm
    have c17 : d.Coprime 17 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.2.1).symm
    have c241 : d.Coprime 241 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h.2.2).symm
    have d585 : d ∣ 585 :=
      c241.dvd_of_dvd_mul_left (c17.dvd_of_dvd_mul_left (c7.dvd_of_dvd_mul_left hd'))
    have dle := Nat.le_of_dvd (by norm_num) d585
    have cert : ∀ e : Fin 586, e.val ∣ 585 → e.val % 9 ≠ 8 := by decide +kernel
    exact cert ⟨d, by omega⟩ d585 d9
  have cert : ∀ r : Fin 240, r.val % 4 = 3 → ¬ (1 ≡ 8 * 3 ^ r.val [MOD 7]) ∧
      ¬ (1 ≡ 8 * 3 ^ r.val [MOD 17]) ∧ ¬ (1 ≡ 8 * 3 ^ r.val [MOD 241]) := by decide +kernel
  have c := cert ⟨(j + 1) % 240, Nat.mod_lt _ (by norm_num)⟩ (by show (j + 1) % 240 % 4 = 3; omega)
  have bad : ∀ l : ℕ, 3 ^ 240 ≡ 1 [MOD l] → l ∣ x - 1 → 1 ≡ 8 * 3 ^ ((j + 1) % 240) [MOD l] := by
    intro l hper hdiv
    have m1 : 1 ≡ x [MOD l] := (Nat.modEq_iff_dvd' (by omega)).mpr hdiv
    exact m1.trans ((pow_period 3 (j + 1) 240 l hper).mul_left 8)
  rcases key with h | h | h
  · exact c.1 (bad 7 (by decide) (h.trans dx))
  · exact c.2.1 (bad 17 (by decide) (h.trans dx))
  · exact c.2.2 (bad 241 (by decide) (h.trans dx))

/-- A prime dividing a product of primes is one of them. -/
lemma prime_mem_of_dvd {p : ℕ} (hp : p.Prime) :
    ∀ l : List ℕ, (∀ q ∈ l, q.Prime) → p ∣ l.prod → p ∈ l
  | [], _, h => absurd (Nat.dvd_one.mp (by simpa using h)) hp.ne_one
  | q :: l, hl, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl q (by simp))).mp h))
    · exact List.mem_cons_of_mem _
        (prime_mem_of_dvd hp l (fun r hr => hl r (List.mem_cons_of_mem _ hr)) h)

/-- If d ∣ t p^k - 1 and p^L = 1 mod d, then only k mod L matters. -/
lemma residue_of (t p k d L : ℕ) (hper : p ^ L ≡ 1 [MOD d]) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) : t * p ^ (k % L) ≡ 1 [MOD d] := by
  have m1 : 1 ≡ t * p ^ k [MOD d] := (Nat.modEq_iff_dvd' hpos).mpr h
  exact (m1.trans ((pow_period p k L d hper).mul_left t)).symm

lemma class_of (t p k d L a : ℕ) (hL : 0 < L) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) (hper : p ^ L ≡ 1 [MOD d])
    (cert : ∀ r : Fin L, t * p ^ r.val ≡ 1 [MOD d] → r.val = a) : k % L = a :=
  cert ⟨k % L, Nat.mod_lt _ hL⟩ (residue_of t p k d L hper hpos h)

lemma no_class (t p k d L : ℕ) (hL : 0 < L) (hpos : 0 < t * p ^ k)
    (h : d ∣ t * p ^ k - 1) (hper : p ^ L ≡ 1 [MOD d])
    (cert : ∀ r : Fin L, ¬ t * p ^ r.val ≡ 1 [MOD d]) : False :=
  cert ⟨k % L, Nat.mod_lt _ hL⟩ (residue_of t p k d L hper hpos h)

set_option maxHeartbeats 1000000 in
/-- In the family x = 16 p^k only six odd primes survive the predecessor test, each in one
    or two classes of k. -/
theorem sixteen_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (test : (16 * p ^ k) ^ 4 - 1 ∣ 2 ^ (16 * p ^ k) - 1) :
    (p = 3 ∧ (k % 4 = 0 ∨ k % 16 = 8 ∨ k % 256 = 64)) ∨ (p = 13 ∧ k % 4 = 2) ∨
    (p = 43 ∧ (k % 8 = 4 ∨ k % 256 = 192)) ∨ (p = 193 ∧ k % 8 = 2) ∨
    (p = 241 ∧ k % 4 = 1) ∨ (p = 643 ∧ k % 16 = 4) := by
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 16 p k (by decide) hp hk test
  clear test
  have hpos : 0 < 16 * p ^ k := Nat.mul_pos (by norm_num) (Nat.pow_pos hp.pos)
  have hd' : d ∣ 65535 := by simpa using hd
  have hdle := Nat.le_of_dvd (by norm_num) hd'
  have dmem : ∀ a b : Fin 256, 256 * a.val + b.val ∣ 65535 → 256 * a.val + b.val ∈ [1, 3, 5,
      15, 17, 51, 85, 255, 257, 771, 1285, 3855, 4369, 13107, 21845, 65535] := by decide +kernel
  have hm : d ∈ [1, 3, 5, 15, 17, 51, 85, 255, 257, 771, 1285, 3855, 4369, 13107, 21845,
      65535] := by
    have e := dmem ⟨d / 256, by omega⟩ ⟨d % 256, Nat.mod_lt _ (by norm_num)⟩
    simp only [Nat.div_add_mod] at e
    exact e hd'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have two : p ≠ 2 := odd
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · have := prime_mem_of_dvd hp [2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inl ⟨rfl, Or.inl (class_of 16 3 k 5 4 0 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel))⟩
  · have := prime_mem_of_dvd hp [2, 2, 2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3, 3] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    all_goals exact Or.inl ⟨rfl, Or.inr (Or.inl (class_of 16 3 k 17 16 8 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)))⟩
  · have := prime_mem_of_dvd hp [2, 2, 13] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact Or.inr (Or.inl ⟨rfl, class_of 16 13 k 51 4 2 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)⟩)
  · have := prime_mem_of_dvd hp [2, 43] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (class_of 16 43 k 85 8 4 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel))⟩))
  · have := prime_mem_of_dvd hp [2, 2, 2, 2, 2, 2, 2, 2] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim
  · have := prime_mem_of_dvd hp [2, 3, 43] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (class_of 16 3 k 257 256 64 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)))⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (class_of 16 43 k 257 256 192 (by norm_num) hpos
        dh (by decide +kernel) (by decide +kernel))⟩))
  · have := prime_mem_of_dvd hp [2, 2, 193] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, class_of 16 193 k 771 8 2 (by norm_num) hpos dh
        (by decide +kernel) (by decide +kernel)⟩)))
  · have := prime_mem_of_dvd hp [2, 643] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (two rfl).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, class_of 16 643 k 1285 16 4 (by norm_num)
        hpos dh (by decide +kernel) (by decide +kernel)⟩))))
  · have := prime_mem_of_dvd hp [2, 2, 2, 2, 241] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl
    any_goals exact (two rfl).elim
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, class_of 16 241 k 3855 4 1 (by norm_num)
      hpos dh (by decide +kernel) (by decide +kernel)⟩))))
  · have := prime_mem_of_dvd hp [2, 5, 19, 23] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (no_class 16 5 k 4369 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 19 k 4369 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 23 k 4369 64 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp [2, 2, 29, 113] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (two rfl).elim
    · exact (no_class 16 29 k 13107 128 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 113 k 13107 128 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp [2, 3, 11, 331] (by norm_num) (by simpa using plus)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact (two rfl).elim
    · exact (no_class 16 3 k 21845 256 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 11 k 21845 64 (by norm_num) hpos dh (by decide +kernel) (by decide +kernel)).elim
    · exact (no_class 16 331 k 21845 256 (by norm_num) hpos dh (by decide +kernel)
        (by decide +kernel)).elim
  · have := prime_mem_of_dvd hp (List.replicate 16 2)
      (fun q hq => by rw [List.eq_of_mem_replicate hq]; exact Nat.prime_two) (by simpa using plus)
    simp at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (two rfl).elim

/-- No x = 8 p^k with p an odd prime passes Hasler's test. -/
theorem eight_prime_power_fails (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0) :
    ¬ ((8 * p ^ k) ^ 4 - 1 ∣ 2 ^ (8 * p ^ k) - 1) := by
  intro test
  obtain rfl := eight_prime_power p k hp odd hk test
  exact eight_three_fails k hk test

theorem main : H1 → H2 → OMA.R_oeis_a000215_R1.H3 := by
  intro h1 h2 x big four np npow _ _ _ _ mbound _ test
  have hmod : x % 8 = 0 ∨ x % 8 = 4 := by omega
  rcases hmod with h0 | h4
  · refine h2 x big (by omega) np npow ?_ ?_ mbound test
    · rintro p k hp hp2 hk rfl
      exact eight_prime_power_fails p k hp hp2 hk test
    · rintro p k hp hp2 hk rfl
      exact sixteen_prime_power p k hp hp2 hk test
  · obtain ⟨t, rfl⟩ : ∃ t, x = 4 * t := ⟨x / 4, by omega⟩
    have todd : Odd t := ⟨t / 2, by omega⟩
    apply h1 t todd (by omega)
    have hsq : 16 * t ^ 2 + 1 = (4 * t) ^ 2 + 1 := by ring
    rw [hsq]
    exact dvd_trans (square_add_one_dvd (4 * t) (by omega)) test

end OMA.R_oeis_a000215_R1_H3_R1
