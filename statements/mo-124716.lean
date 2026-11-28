import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Positive eigenvalue of a diagonally perturbed stochastic matrix

Source: https://mathoverflow.net/questions/124716
Credit: @MMexicann
-/

open scoped BigOperators

namespace OMA.S_mo_124716

theorem main (n : ℕ) (a : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (k : ℝ)
    (ha : Monotone a) (haPos : ∃ i, 0 < a i)
    (hentries : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1)
    (hrows : ∀ i, ∑ j, P i j = 1)
    (hirred : ∀ i j, ∃ m : ℕ, 0 < (P ^ m) i j)
    (hreal : ∀ z : ℂ, (P.map fun x : ℝ => (x : ℂ)).charpoly.eval z = 0 → z.im = 0)
    (hk : 0 < k) :
    ∃ z : ℝ, 0 < z ∧ (Matrix.diagonal a + k • P).charpoly.eval z = 0 := by
  sorry

end OMA.S_mo_124716
