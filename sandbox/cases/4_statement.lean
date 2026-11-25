import Mathlib

/-! test -/

namespace OMA.S_wp_hadwiger_nelson_problem_on_the_chromatic_number_of_unit_distance_graphs

def UnitDistanceColoring (k : ℕ) (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ x y, dist x y = 1 → c x ≠ c y

theorem main : sInf {k : ℕ | ∃ c, UnitDistanceColoring k c} ∈ ({5, 6, 7} : Set ℕ) := by
  sorry

end OMA.S_wp_hadwiger_nelson_problem_on_the_chromatic_number_of_unit_distance_graphs
