import OMAReductions.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1

/-! If an odd perfect number at most 10^1500 avoids 3, 5, and 7, the
divisor-sum estimates force it to exceed 10^1238 and force 11^6, 13^4, 17^2, 19^4, and 23^4 to divide it. -/

namespace OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105

def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105 → 10^1238 < n → ¬ 11^6 * 13^4 * 17^2 * 19^4 * 23^4 ∣ n

def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105 → 10^1238 < n ∧ 11^6 * 13^4 * 17^2 * 19^4 * 23^4 ∣ n

theorem main : H1 → H2 → H3 → OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1.H1 := by
  intro small exclude force n ho hn hs
  have hc := small n ho hn hs
  obtain ⟨lower, divisibility⟩ := force n ho hn hs hc
  exact (exclude n ho hn hs hc lower divisibility).elim

end OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1
