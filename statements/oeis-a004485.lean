import Mathlib

/-!
# OEIS A004485: conjectured recurrence and generating function

Conjectures by Chai Wah Wu, April 5, 2021, in https://oeis.org/A004485.
The Wythoff game and its Sprague–Grundy table are defined in https://oeis.org/A004481.
Credit: @sassmama27
-/

namespace OMA.S_oeis_a004485

/-- A move reduces one heap, or reduces both by the same positive amount. -/
def Move (a b c d : ℕ) : Prop :=
  (c < a ∧ d = b) ∨ (c = a ∧ d < b) ∨
    ∃ k : ℕ, 0 < k ∧ a = c + k ∧ b = d + k

/-- At each position the value is the least natural number absent from its options. -/
def IsGrundy (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ a b : ℕ,
    (∀ c d : ℕ, Move a b c d → g c d ≠ g a b) ∧
    (∀ m : ℕ, m < g a b → ∃ c d : ℕ, Move a b c d ∧ g c d = m)

/-- The row indexed by 4, with the recurrence interpreted over the integers. -/
def a (g : ℕ → ℕ → ℕ) (n : ℕ) : ℤ := Int.ofNat (g 4 n)

/-- Numerator of the conjectured ordinary generating function. -/
def numerator (x : PowerSeries ℤ) : PowerSeries ℤ :=
  -8 * x^21 + 6 * x^20 + 6 * x^19 - 4 * x^18 + 4 * x^16 - 4 * x^15 +
    x^14 + 4 * x^13 - 5 * x^12 - x^11 + 5 * x^10 + 7 * x^9 + x^8 -
    9 * x^7 + 3 * x^6 - x^5 + 5 * x^4 - x^3 - 2 * x^2 + x + 4

def x : PowerSeries ℤ := PowerSeries.X

/-- The generating-function identity is written with its denominator cleared.
The denominator has constant coefficient 1. -/
theorem main : ∀ (g : ℕ → ℕ → ℕ), IsGrundy g →
    (∀ n : ℕ, 21 < n → a g n = a g (n - 1) + a g (n - 12) - a g (n - 13)) ∧
    ((x^13 - x^12 - x + 1) * PowerSeries.mk (a g) = numerator x) := by
  sorry

end OMA.S_oeis_a004485
