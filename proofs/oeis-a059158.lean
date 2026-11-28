import OMAStatements.S_oeis_a059158

-- Problem: A059158: A hierarchical sequence (S(W'3{2,2}cc) - see A059126).
-- Credit: @rtflynn
-- Proof idea: the k-th term depends only on v = padicValNat 2 k. Splitting 1..2N+1 into odd numbers
-- (v = 0) and 2j (v = 1 + v(j)) gives the sum over 1..2^m - 1 in closed form by induction on m;
-- the recurrence and the g.f. (comparing coefficients) follow from the closed form.

open PowerSeries OMA.S_oeis_a059158 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059158.main := by
  have v_odd : ∀ j : ℕ, padicValNat 2 (2 * j + 1) = 0 := fun j =>
    padicValNat.eq_zero_of_not_dvd (by omega)
  have v_even : ∀ j : ℕ, padicValNat 2 (2 * (j + 1)) = padicValNat 2 (j + 1) + 1 := by
    intro j
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    ring
  have split : ∀ (f : ℕ → ℚ) (N : ℕ),
      ∑ k ∈ Finset.range (2 * N + 1), f (padicValNat 2 (k + 1)) =
        ((N : ℚ) + 1) * f 0 + ∑ k ∈ Finset.range N, f (padicValNat 2 (k + 1) + 1) := by
    intro f N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring,
        Finset.sum_range_succ _ (2 * N + 1 + 1), Finset.sum_range_succ _ (2 * N + 1), ih,
        Finset.sum_range_succ _ N, show 2 * N + 1 + 1 = 2 * (N + 1) by ring, v_even N,
        v_odd (N + 1)]
      push_cast
      ring
  have hpow : ∀ m : ℕ, 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
    intro m
    have : 0 < 2 ^ m := by positivity
    rw [pow_succ]
    omega
  have hcast : ∀ m : ℕ, ((2 ^ m - 1 : ℕ) : ℚ) = 2 ^ m - 1 := by
    intro m
    have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub this]
    push_cast
    ring
  have lin : ∀ (B A : ℚ) (m : ℕ),
      ∑ k ∈ Finset.range (2 ^ m - 1), (A + B * (padicValNat 2 (k + 1) : ℚ)) =
        A * (2 ^ m - 1) + B * (2 ^ m - m - 1) := by
    intro B A m
    induction m generalizing A with
    | zero => simp
    | succ m ih =>
      rw [hpow m, split (fun v => A + B * (v : ℚ)) (2 ^ m - 1)]
      have e : ∀ k : ℕ, A + B * ((padicValNat 2 (k + 1) + 1 : ℕ) : ℚ) =
          (A + B) + B * (padicValNat 2 (k + 1) : ℚ) := fun k => by push_cast; ring
      simp only [e]
      rw [ih (A + B), hcast m]
      push_cast
      ring
  have geo : ∀ (c : ℚ) (m : ℕ),
      ∑ k ∈ Finset.range (2 ^ m - 1), c * (16 : ℚ) ^ (padicValNat 2 (k + 1)) =
        c / 14 * (16 ^ m - 2 ^ m) := by
    intro c m
    induction m generalizing c with
    | zero => simp
    | succ m ih =>
      rw [hpow m, split (fun v => c * (16 : ℚ) ^ v) (2 ^ m - 1)]
      have e : ∀ k : ℕ, c * (16 : ℚ) ^ (padicValNat 2 (k + 1) + 1) =
          (16 * c) * (16 : ℚ) ^ (padicValNat 2 (k + 1)) := fun k => by ring
      simp only [e, pow_zero, mul_one]
      rw [ih (16 * c), hcast m]
      ring
  have hval : ∀ k : ℕ, (collapsed2 k : ℚ) = 24 * 16 ^ (padicValNat 2 k) := by
    intro k
    have hb : 4 * (ruler k - 1) + 1 = 4 * padicValNat 2 k + 1 := by simp [ruler]
    simp only [collapsed2, element', element, hb, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have p : ∀ t : ℕ, 2 ^ (4 * padicValNat 2 k + 1 + t - 1) = 2 ^ t * 16 ^ padicValNat 2 k := by
      intro t
      rw [show 4 * padicValNat 2 k + 1 + t - 1 = t + 4 * padicValNat 2 k by omega, pow_add,
        pow_mul]
      norm_num
    have p0 : 2 ^ (4 * padicValNat 2 k + 1 - 1) = 16 ^ padicValNat 2 k := by
      rw [show 4 * padicValNat 2 k + 1 - 1 = 4 * padicValNat 2 k by omega, pow_mul]
      norm_num
    rw [p0, p 1, p 2, p 3]
    push_cast
    ring
  have ha : ∀ n : ℕ, (a n : ℚ) = 24 / 7 * (8 * 16 ^ n - 2 ^ n) := by
    intro n
    have e : (a n : ℚ) = ∑ k ∈ Finset.range (2 ^ (n + 1) - 1),
        (24 : ℚ) * (16 : ℚ) ^ (padicValNat 2 (k + 1)) := by
      unfold a
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => hval (k + 1)
    rw [e, geo]
    ring
  refine ⟨ha, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    have h : ((a (m + 2) : ℤ) : ℚ) = ((18 * a (m + 1) - 32 * a m : ℤ) : ℚ) := by
      push_cast
      simp only [ha]
      ring
    exact_mod_cast h
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * ((2 * X - 1) * (16 * X - 1)) =
        (C : ℚ →+* PowerSeries ℚ) 32 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
          - (C : ℚ →+* PowerSeries ℚ) 18 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
          + PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [map_ofNat (C : ℚ →+* PowerSeries ℚ) 32, map_ofNat (C : ℚ →+* PowerSeries ℚ) 18]
      ring
    have e2 : (24 : PowerSeries ℚ) = (C : ℚ →+* PowerSeries ℚ) 24 := by
      rw [map_ofNat (C : ℚ →+* PowerSeries ℚ) 24]
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;> norm_num [ha]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      rw [if_pos (show 2 ≤ k + 2 by omega), if_pos (show 1 ≤ k + 2 by omega),
        if_neg (show ¬ (k + 2 = 0) by omega), show k + 2 - 2 = k by omega,
        show k + 2 - 1 = k + 1 by omega]
      simp only [ha]
      ring

