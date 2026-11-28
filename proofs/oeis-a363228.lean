import OMAStatements.S_oeis_a363228
import Mathlib

namespace OMA.A363228P

open OMA.S_oeis_a363228

lemma pow4_dvd_iff {x : ℕ} (hx : x ≠ 0) (k : ℕ) :
    4 ^ k ∣ x ↔ 2 * k ≤ padicValNat 2 x := by
  have : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [this]
  exact padicValNat_dvd_iff_le hx

lemma exp4_eq {x : ℕ} (hx : x ≠ 0) : exp4 x = padicValNat 2 x / 2 := by
  unfold exp4
  rw [Nat.findGreatest_eq_iff]
  have hle : padicValNat 2 x < x := by
    have h1 : 2 ^ padicValNat 2 x ∣ x := pow_padicValNat_dvd
    have h2 : 2 ^ padicValNat 2 x ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) h1
    have h3 : padicValNat 2 x < 2 ^ padicValNat 2 x := Nat.lt_two_pow_self
    omega
  refine ⟨by omega, fun _ => (pow4_dvd_iff hx _).2 (by omega), ?_⟩
  intro n hn _ hP
  rw [pow4_dvd_iff hx] at hP
  omega

lemma v2_gen (f : ℕ → ℕ) (h1 : ∀ m, Odd m → f m % 16 = 8)
    (h2 : ∀ n, ∃ g, f (2 * n) = f n * g ∧ g % 4 = 2) :
    ∀ k m, Odd m → f (2 ^ k * m) ≠ 0 ∧ padicValNat 2 (f (2 ^ k * m)) = k + 3 := by
  intro k m hm
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    have h := h1 m hm
    obtain ⟨q, hq⟩ : ∃ q, f m = 8 * (2 * q + 1) := ⟨f m / 16, by omega⟩
    rw [hq]
    refine ⟨by omega, ?_⟩
    rw [padicValNat.mul (by norm_num) (by omega)]
    have : padicValNat 2 (2 * q + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega)
    rw [this]
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this, padicValNat.prime_pow]
  | succ k ih =>
    obtain ⟨g, hg, hg2⟩ := h2 (2 ^ k * m)
    have e : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [e, hg]
    obtain ⟨r, hr⟩ : ∃ r, g = 2 * (2 * r + 1) := ⟨g / 4, by omega⟩
    rw [hr]
    refine ⟨mul_ne_zero ih.1 (by omega), ?_⟩
    rw [padicValNat.mul ih.1 (by omega), padicValNat.mul (by norm_num) (by omega), ih.2,
      padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 2 * r + 1 by omega)]
    simp

lemma fib_add6 (n : ℕ) : Nat.fib (n + 6) % 4 = Nat.fib n % 4 := by
  have h : Nat.fib (5 + n + 1) = Nat.fib 5 * Nat.fib n + Nat.fib 6 * Nat.fib (n + 1) := by
    rw [Nat.fib_add]
  rw [show n + 6 = 5 + n + 1 by ring, h]
  simp [Nat.fib_add_two, Nat.fib_one, Nat.fib_zero]
  omega

lemma fib_mod4 (n : ℕ) : Nat.fib n % 4 = Nat.fib (n % 6) % 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 6
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      rw [fib_add6, ih k (by omega)]
      congr 2
      omega

lemma fib_add24 (n : ℕ) : Nat.fib (n + 24) % 16 = Nat.fib n % 16 := by
  have h : Nat.fib (23 + n + 1) = Nat.fib 23 * Nat.fib n + Nat.fib 24 * Nat.fib (n + 1) := by
    rw [Nat.fib_add]
  rw [show n + 24 = 23 + n + 1 by ring, h]
  have e23 : Nat.fib 23 = 28657 := by decide
  have e24 : Nat.fib 24 = 46368 := by decide
  rw [e23, e24]
  omega

lemma fib_mod16 (n : ℕ) : Nat.fib n % 16 = Nat.fib (n % 24) % 16 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 24
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 24 := ⟨n - 24, by omega⟩
      rw [fib_add24, ih k (by omega)]
      congr 2
      omega

lemma fib_v2 : ∀ k m, Odd m →
    (fun n => Nat.fib (6 * n)) (2 ^ k * m) ≠ 0 ∧
      padicValNat 2 ((fun n => Nat.fib (6 * n)) (2 ^ k * m)) = k + 3 := by
  refine v2_gen (fun n => Nat.fib (6 * n)) ?_ ?_
  · intro m hm
    rw [fib_mod16]
    obtain ⟨j, rfl⟩ := hm
    have : 6 * (2 * j + 1) % 24 = 6 ∨ 6 * (2 * j + 1) % 24 = 18 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  · intro n
    refine ⟨2 * Nat.fib (6 * n + 1) - Nat.fib (6 * n), ?_, ?_⟩
    · rw [show 6 * (2 * n) = 2 * (6 * n) by ring, Nat.fib_two_mul]
    · have a1 := fib_mod4 (6 * n)
      have a2 := fib_mod4 (6 * n + 1)
      have b1 : 6 * n % 6 = 0 := by omega
      have b2 : (6 * n + 1) % 6 = 1 := by omega
      rw [b1] at a1
      rw [b2] at a2
      simp at a1 a2
      have : Nat.fib (6 * n) ≤ Nat.fib (6 * n + 1) := Nat.fib_le_fib_succ
      omega

lemma pow9_mod16 (m : ℕ) (hm : Odd m) : 9 ^ m % 16 = 9 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

lemma nine_v2 : ∀ k m, Odd m →
    (fun n => 9 ^ n - 1) (2 ^ k * m) ≠ 0 ∧
      padicValNat 2 ((fun n => 9 ^ n - 1) (2 ^ k * m)) = k + 3 := by
  refine v2_gen (fun n => 9 ^ n - 1) ?_ ?_
  · intro m hm
    have h := pow9_mod16 m hm
    have : 1 ≤ 9 ^ m := Nat.one_le_pow _ _ (by norm_num)
    omega
  · intro n
    refine ⟨9 ^ n + 1, ?_, ?_⟩
    · obtain ⟨y, hy⟩ : ∃ y, 9 ^ n = y + 1 :=
        ⟨9 ^ n - 1, by have := Nat.one_le_pow n 9 (by norm_num); omega⟩
      rw [pow_mul', hy, Nat.add_sub_cancel]
      have : (y + 1) ^ 2 = y * (y + 2) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    · rw [Nat.add_mod, Nat.pow_mod]
      norm_num

end OMA.A363228P

open OMA.A363228P in
theorem OMA.solution : type_of% @OMA.S_oeis_a363228.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
    obtain ⟨h1, h2⟩ := nine_v2 k m hm
    obtain ⟨h3, h4⟩ := fib_v2 k m hm
    simp only at h1 h2 h3 h4
    unfold OMA.S_oeis_a363228.a
    rw [exp4_eq h1, exp4_eq h3, h2, h4]
  · intro m hm h6
    have h := fib_mod4 m
    have hne : Nat.fib m ≠ 0 := by
      have := Nat.fib_pos.2 (show 0 < m by omega)
      omega
    have hr : m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
    have h4 : ¬ 4 ∣ Nat.fib m := by
      rw [Nat.dvd_iff_mod_eq_zero, h]
      rcases hr with h | h | h | h | h <;> rw [h] <;> decide
    unfold OMA.S_oeis_a363228.exp4
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, fun h0 => absurd rfl h0, ?_⟩
    intro n hn _ hP
    exact h4 (dvd_trans (dvd_pow_self 4 (by omega)) hP)
