import OMAStatements.S_oeis_a034444

-- Problem: A034444 (Ianakiev's conjecture): the odd unitary divisor power sum divides the full one.
-- Credit: @alan-phobos-claude (first solve); shorter proof (same argument, golfed) by @PandaWill.

open OMA.S_oeis_a034444 Finset

lemma U {N d : ℕ} (h : N ≠ 0) : d ∈ unitary N ↔ ∃ c, N = d * c ∧ d.Coprime c := by
  simp only [unitary, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨c, rfl⟩, -⟩, h'⟩
    exact ⟨c, rfl, by rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul h))] at h'⟩
  · rintro ⟨c, rfl, h'⟩
    exact ⟨⟨dvd_mul_right _ _, h⟩, by rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul h))]⟩

lemma P (n : ℕ) (h : n ≠ 0) : ∃ a m, Odd m ∧ n = 2 ^ a * m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨q, rfl⟩ | h
    · obtain ⟨a, m, hm, rfl⟩ := ih q (by omega) (by omega)
      exact ⟨a + 1, m, hm, by rw [pow_succ, mul_right_comm, mul_two]⟩
    · exact ⟨0, n, h, by simp⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a034444.main := by
  intro n hn k
  obtain ⟨a, m, hm, rfl⟩ := P _ hn.ne'
  have hN := hn.ne'
  have O {d c} (h : m = d * c) : Odd d := (Nat.odd_mul.1 (h ▸ hm)).1
  have C {x} : Odd x → Nat.Coprime 2 x := Nat.coprime_two_left.2
  rw [← sum_filter_add_sum_filter_not (unitary _) Odd]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [sum_eq_zero (s := (unitary _).filter (¬ Odd ·)) fun d hd => ?_, add_zero]
    rw [mem_filter, U hN] at hd
    obtain ⟨⟨c, hc, -⟩, h⟩ := hd
    exact absurd (O (by simpa using hc)) h
  suffices h : ∑ d ∈ (unitary _).filter (¬ Odd ·), d ^ k = (2 ^ a) ^ k * ∑ d ∈ (unitary _).filter Odd, d ^ k by
    rw [h]; exact dvd_add dvd_rfl (dvd_mul_left _ _)
  refine (map_sum (AddMonoidHom.mulLeft _) _ _).trans (sum_nbij (2 ^ a * ·) (fun e he => ?_)
    (mul_right_injective₀ (by simp)).injOn (fun d hd => ?_) fun e _ => (mul_pow _ _ _).symm) |>.symm
  · rw [mem_filter, U hN] at he ⊢
    obtain ⟨⟨c, hc, hec⟩, he⟩ := he
    obtain ⟨c, rfl⟩ := ((C he).pow_left a).dvd_of_dvd_mul_left ⟨m, hc.symm⟩
    have hmc : m = e * c := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_left_comm])
    exact ⟨⟨c, by rw [hmc, mul_assoc], Nat.coprime_mul_iff_left.2
      ⟨(C (O (hmc.trans (mul_comm _ _)))).pow_left a, hec.coprime_dvd_right (dvd_mul_left _ _)⟩⟩,
      Nat.not_odd_iff_even.2 ((Nat.even_pow.2 ⟨even_two, ha.ne'⟩).mul_right _)⟩
  · rw [mem_coe, mem_filter, U hN] at hd
    obtain ⟨⟨c, hc, hdc⟩, hd⟩ := hd
    have hco : Odd c := Nat.coprime_two_left.1 (hdc.coprime_dvd_left (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hd)))
    obtain ⟨e, rfl⟩ := ((C hco).pow_left a).dvd_of_dvd_mul_right ⟨m, hc.symm⟩
    have hmc : m = e * c := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) (by rw [hc, mul_assoc])
    refine ⟨e, ?_, rfl⟩
    rw [mem_coe, mem_filter, U hN]
    exact ⟨⟨2 ^ a * c, by rw [hmc, mul_left_comm], Nat.coprime_mul_iff_right.2
      ⟨((C (O hmc)).pow_left a).symm, hdc.coprime_dvd_left (dvd_mul_left _ _)⟩⟩, O hmc⟩
