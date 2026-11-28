import OMAStatements.S_oeis_a059140
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a059140

lemma v2_odd (v w : ℕ) (hw : Odd w) : padicValNat 2 (2 ^ v * w) = v := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [padicValNat.mul (by positivity) hw0, padicValNat.prime_pow]
  have : ¬ 2 ∣ w := by rwa [← even_iff_two_dvd, ← Nat.not_odd_iff_even, not_not]
  rw [padicValNat.eq_zero_of_not_dvd this]; simp

lemma v2_add (m j : ℕ) (hj : 0 < j) (hjm : j < 2 ^ m) : padicValNat 2 (2 ^ m + j) = padicValNat 2 j := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj.ne'
  have hv : v < m := by
    by_contra h
    push_neg at h
    have : 2 ^ m ≤ 2 ^ v * u := by
      calc 2 ^ m ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) h
        _ ≤ 2 ^ v * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hu))
    omega
  have h1 : 2 ^ m + 2 ^ v * u = 2 ^ v * (2 ^ (m - v) + u) := by
    rw [mul_add, ← pow_add]; congr 2; omega
  rw [h1, v2_odd v _, v2_odd v _ hu]
  have : Even (2 ^ (m - v)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact this.add_odd hu

/-- h k = value of the k-th collapsed term, with h 0 = 0. -/
def h (k : ℕ) : ℕ := if k = 0 then 0 else collapsed k

def G (m : ℕ) : ℕ := ∑ k ∈ Finset.range (2 ^ m), h k

lemma collapsed_eq (k : ℕ) : collapsed k = 3 * padicValNat 2 k + 4 := by
  simp [collapsed, phrase, ruler]; ring

lemma h_pos (k : ℕ) (hk : 0 < k) : h k = 3 * padicValNat 2 k + 4 := by
  simp [h, hk.ne', collapsed_eq]

lemma G_succ (m : ℕ) : G (m + 1) = 2 * G m + 3 * m + 4 := by
  unfold G
  rw [pow_succ, mul_two, Finset.sum_range_add]
  have : ∑ j ∈ Finset.range (2 ^ m), h (2 ^ m + j) =
      ∑ j ∈ Finset.range (2 ^ m), (h j + if j = 0 then 3 * m + 4 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · simp [padicValNat.prime_pow, h, collapsed_eq]
    · rw [h_pos _ (by omega), h_pos _ hjp, v2_add m j hjp hj]; simp [hjp.ne']
  rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (2 ^ m)) 0 (fun _ => 3 * m + 4)]
  simp only [Finset.mem_range]
  rw [if_pos (by positivity)]
  ring

lemma G_closed (m : ℕ) : G m + 3 * m + 7 = 7 * 2 ^ m := by
  induction m with
  | zero => simp [G, h]
  | succ k ih => rw [G_succ, pow_succ]; omega

lemma a_eq (n : ℕ) : a n = G (n + 1) := by
  unfold a G
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ (n + 1) = N + 1 := ⟨2 ^ (n + 1) - 1, by have := Nat.one_le_two_pow (n := n + 1); omega⟩
  rw [hN, Nat.add_sub_cancel, Finset.sum_range_succ']
  simp [h]

end OMA.S_oeis_a059140

theorem OMA.solution : type_of% @OMA.S_oeis_a059140.main := by
  open OMA.S_oeis_a059140 in
  have hc : ∀ n : ℕ, (a n : ℤ) = 2 * (-5 + 7 * 2 ^ n) - 3 * n := by
    intro n
    have := G_closed (n + 1)
    rw [a_eq]
    rw [pow_succ] at this
    zify at this
    linarith
  refine ⟨hc, ?_, ?_⟩
  · intro n hn
    rw [hc, hc, hc, hc]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [show 3 + k - 1 = k + 2 by omega, show 3 + k - 2 = k + 1 by omega, show 3 + k - 3 = k by omega]
    push_cast
    ring
  · ext n
    have hP : ((X - 1) ^ 2 * (2 * X - 1) : PowerSeries ℚ) = C (2:ℚ) * X ^ 3 - C (5:ℚ) * X ^ 2 + C (4:ℚ) * X ^ 1 - 1 := by
      simp only [map_ofNat]; ring
    have hq : ∀ n : ℕ, (a n : ℚ) = 2 * (-5 + 7 * 2 ^ n) - 3 * n := by
      intro n; have := hc n; exact_mod_cast this
    have hF : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) =
        C (2:ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) - C (5:ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (4:ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) - PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [hP]; ring
    rw [hF, show (4:PowerSeries ℚ) = C (4:ℚ) from (map_ofNat C 4).symm]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X, coeff_C]
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n <;> simp [hq] <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h3
      have e1 : 3 + k - 3 = k := by omega
      have e2 : 3 + k - 2 = k + 1 := by omega
      have e3 : 3 + k - 1 = k + 2 := by omega
      simp only [e1, e2, e3, hq]
      split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
