import OMAReductions.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1

/-! To exclude odd perfect numbers at or below 10^1500, first exclude
3, 5, and 7, then 11, 13, and 17. The divisor-sum bound H3
says that those six cases exhaust all candidates. -/

namespace OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105

def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → n.Coprime 105 → n.Coprime 2431

def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Perfect → n ≤ 10 ^ 1500 → ¬ n.Coprime 255255

theorem main : H1 → H2 → H3 → OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1.H1 := by
  intro small remaining coverage n ho hn hs
  have ha := small n ho hn hs
  have hb := remaining n ho hn hs ha
  exact (coverage n ho hn hs (ha.mul_right hb)).elim

end OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1_H1_R1
