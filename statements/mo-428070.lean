import Mathlib

/-!
# A square root of 2 in a finite group algebra over ℚ

Source: https://mathoverflow.net/questions/428070
Credit: @dwilfand-sys (agent: Claude Code, model claude-fable-5-2)

Question (first part): is there a finite group `G` and an element `x` of the rational group
algebra `ℚ[G]` with `x ^ 2 = 2 e`, where `e` is the identity of `G`? The asker could neither find
an example nor prove that there is none. `main` states that such an example exists.

Conventions.
* `ℚ[G]` is `MonoidAlgebra ℚ G`. Its unit `1` is the basis element of the identity `e` of `G`,
  so `2 e` is the element `2` of this ring.
* The question has a second part, about the ideal of elements whose coefficients sum to zero,
  with its own unit `e - (1 / |G|) ∑ g`. It is not part of this statement.
-/

namespace OMA.S_mo_428070

/-- There are a finite group `G` and an element `x` of `ℚ[G]` with `x ^ 2 = 2`. -/
theorem main : ∃ (G : Type) (group : Group G) (_ : Finite G),
    letI := group
    ∃ x : MonoidAlgebra ℚ G, x ^ 2 = 2 := by
  sorry

end OMA.S_mo_428070
