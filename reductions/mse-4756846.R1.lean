import OMAStatements.S_mse_4756846
import Mathlib

/-!
The reverse implication is the factorization in the original question
(https://math.stackexchange.com/questions/4756846). For an odd factorization
of the exponent, divide the sum of powers in two stages. Both quotients
are integers greater than one.
-/

namespace OMA.R_mse_4756846_R1

private theorem sum_lt_sum_pow {x y k : ℕ} (hx : 0 < x) (hy : 1 < y) (hk : 1 < k) :
    x + y < x ^ k + y ^ k := by
  have hxk : x ^ 1 ≤ x ^ k := pow_le_pow_right₀ (by omega : 1 ≤ x) (by omega)
  have hyk : y ^ 1 < y ^ k := pow_lt_pow_right₀ hy hk
  simpa only [pow_one] using Nat.add_lt_add_of_le_of_lt hxk hyk

private theorem quotient_not_prime {x y r s : ℕ} (hx : 0 < x) (hy : 1 < y)
    (hr : 1 < r) (hs : 1 < s) (hro : Odd r) (hso : Odd s) :
    ¬ ((x ^ (r * s) + y ^ (r * s)) / (x + y)).Prime := by
  obtain ⟨a, ha⟩ := hro.nat_add_dvd_pow_add_pow x y
  obtain ⟨b, hb⟩ := hso.nat_add_dvd_pow_add_pow (x ^ r) (y ^ r)
  have h₁ := sum_lt_sum_pow hx hy hr
  have hyp : y < y ^ r := by simpa only [pow_one] using pow_lt_pow_right₀ hy hr
  have h₂ := sum_lt_sum_pow (x := x ^ r) (by positivity) (hy.trans hyp) hs
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, mul_one] at ha
    omega
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, mul_one] at hb
    omega
  rw [pow_mul, pow_mul, hb, ha, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < x + y)]
  exact Nat.not_prime_mul ha1 hb1

/-- Primality of the quotient forces primality of the exponent. -/
def H1 : Prop := ∀ m n : ℕ, 1 ≤ m → 1 < n →
  ((Nat.fib n ^ (2 * m + 1) + Nat.fib (n + 1) ^ (2 * m + 1)) /
    (Nat.fib n + Nat.fib (n + 1))).Prime → (2 * m + 1).Prime

/-- The existence question for each prime exponent. -/
def H2 : Prop := ∀ m : ℕ, 1 ≤ m → (2 * m + 1).Prime → ∃ n : ℕ, 1 < n ∧
  ((Nat.fib n ^ (2 * m + 1) + Nat.fib (n + 1) ^ (2 * m + 1)) /
    (Nat.fib n + Nat.fib (n + 1))).Prime

theorem prime_of_prime_quotient : H1 := by
  intro m n hm hn hq
  by_contra hp
  obtain ⟨r, s, hrlt, hslt, hfactor⟩ : ∃ r s : ℕ,
      r < 2 * m + 1 ∧ s < 2 * m + 1 ∧ r * s = 2 * m + 1 := by
    by_contra h
    exact hp (Nat.prime_iff_not_exists_mul_eq.mpr ⟨by omega, h⟩)
  have hr : 1 < r := by
    by_contra! h
    interval_cases r <;> simp_all
  have hs : 1 < s := by
    by_contra! h
    interval_cases s <;> simp_all
  have hord : Odd (r * s) := ⟨m, hfactor⟩
  have hodd := Nat.odd_mul.mp hord
  have hx : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  have hxy := Nat.fib_lt_fib_succ (show 2 ≤ n from hn)
  have hy : 1 < Nat.fib (n + 1) := by omega
  exact quotient_not_prime hx hy hr hs hodd.1 hodd.2 (hfactor.symm ▸ hq)

theorem main : H1 → H2 → type_of% @OMA.S_mse_4756846.main := by
  intro reverse forward m hm
  exact ⟨forward m hm, fun ⟨n, hn, hq⟩ => reverse m n hm hn hq⟩

end OMA.R_mse_4756846_R1
